# To Do #
# Stop playing sounds when exiting mission. 



import socket
import math
import tkinter as tk
import re
from tkinter import Scale, messagebox
import os
import pygame
from tkinter import filedialog
from pathlib import Path
import shutil
from tkinter import*
from PIL import Image, ImageTk
import time
import threading
import json
import webbrowser
import sys

root = tk.Tk()
root.title("Bandits 12 O'Clock!")
root.config(background="black")
pygame.mixer.init()

main_frame = tk.Frame(root)
main_frame.pack(padx=10, pady=5)


# Paths used by both normal Python runs and PyInstaller builds.
# PyInstaller places bundled files beside this script inside its bundle, while
# writable files are kept in a data folder beside the executable.
BUNDLE_DIR = Path(__file__).resolve().parent
APP_DIR = (
    Path(sys.executable).resolve().parent
    if getattr(sys, "frozen", False)
    else BUNDLE_DIR
)

ASSETS_DIR = BUNDLE_DIR / "assets"
IMAGES_DIR = ASSETS_DIR / "images"
AUDIO_DIR = ASSETS_DIR / "audio"
DATA_DIR = APP_DIR / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)

USER_DATA_PATH = DATA_DIR / "usr_data.json"
GAME_INFO_PATH = DATA_DIR / "info.txt"
APP_LOG_PATH = DATA_DIR / "log.txt"

# Keep this string available for older code that uses it as a file-dialog path.
program_directory = str(APP_DIR)

soundlevel = pygame.mixer.Sound(str(AUDIO_DIR / "SoundLevel.mp3"))

results = []

# Per-trigger runtime state (armed, loiter start time)
trigger_states = {}

# Cache the trigger objects currently present in the loaded .mis file.
# trigger_check() runs frequently, so rereading the mission for every trigger
# and every coordinate packet would be unnecessarily expensive.
mission_trigger_cache = {
    "path": None,
    "modified_time": None,
    "triggers": [],
}

# Avoid checking and rewriting the same .trig file on every position packet.
trigger_sync_cache = {
    "mission_path": None,
    "mission_modified_time": None,
    "trigger_path": None,
    "trigger_modified_time": None,
}

# Trigger groups that have already been completed during the current mission.
# Once one trigger in a group fires, every trigger with the same Group ID is disabled.
disabled_trigger_groups = set()

# Generic mission-rule runtime state.
active_rules = set()
mission_rules = {}
rule_states = {}
telemetry_values = {}
telemetry_lock = threading.Lock()
current_rules_path = None

app_icon_path = IMAGES_DIR / "app_icon.png"

if app_icon_path.exists():
    try:
        app_icon = tk.PhotoImage(file=str(app_icon_path))
        root.iconphoto(True, app_icon)

        # Keep a reference so Tkinter does not discard it.
        root.app_icon = app_icon

    except tk.TclError as error:
        print("Could not load app icon:", error)


# Stock DeviceLink readable parameters used by mission rules.
DEVICE_LINK_PARAMETERS = {
    "time_of_day": 20,
    "plane": 22,
    "cockpits": 24,
    "cockpit_cur": 26,
    "engines": 28,
    "speedometer_indicated": 30,
    "variometer": 32,
    "slip": 34,
    "turn": 36,
    "angular_speed": 38,
    "altimeter": 40,
    "azimuth": 42,
    "beacon_azimuth": 44,
    "roll": 46,
    "pitch": 48,
    "fuel": 50,
    "overload": 52,
    "shake_level": 54,
    "gear_pos_l": 56,
    "gear_pos_r": 58,
    "gear_pos_c": 60,

    # Engine RPM. "rpm" remains a backwards-compatible alias for rpm0,
    # allowing existing mission rule files to keep working.
    "rpm": 64,
    "rpm0": 64,
    "rpm1": 64,
    "rpm2": 64,
    "rpm3": 64,

    "manifold": 66,
    "temp_oilin": 68,
    "temp_oilout": 70,
    "temp_water": 72,
    "temp_cylinders": 74,
    "power": 80,
    "flaps": 82,
    "aileron": 84,
    "elevator": 86,
    "rudder": 88,
    "brakes": 90,
    "prop_pitch": 92,
    "aileron_trim": 94,
    "elevator_trim": 96,
    "rudder_trim": 98,
    "level_stabilizer": 100,
    "boost": 104,
    "gear": 164,
    "airbrake": 172,
    "tailwheel_lock": 174,
    "weapon_1": 180,
    "weapon_2": 182,
    "weapon_3": 184,
    "weapon_4": 186,
    "wing_fold": 210,
    "canopy": 212,
    "arresting_hook": 214,
    "chocks": 216,
}

DEVICELINK_HOST = "127.0.0.1"
DEVICELINK_PORT = 21100



filepath = str(AUDIO_DIR)  # Default folder used when browsing for bundled audio.
trig_name = str(DATA_DIR / "racing_markers.log")

# Socket for receiving position data
sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.bind(("0.0.0.0", 21101))
sock.settimeout(0.01)

print("DeviceLink client running... waiting for IL-2")

TRIGGER_OBJECTS = {
    "vehicles.stationary.Smoke$Smoke15": "Normal",
    "vehicles.stationary.Smoke$Smoke14": "Repeatable",
    "vehicles.stationary.Smoke$Smoke13": "Loiter",
    "vehicles.stationary.Smoke$Smoke12": "ActivateRule",
    "vehicles.stationary.Smoke$Smoke11": "DeactivateRule",
}

#------------------------Logging and trigger checking -------------------------#

mission_path_var = tk.StringVar(value="Wait, did you select a mission file? If not, select one using the button!")


def ensure_rules_file_for_mission(mission_path):
    """Create an empty .rules.json beside a mission if it does not exist.

    This accepts either the original .mis path or an existing .rules.json path
    without appending the JSON suffix a second time.
    """
    if not mission_path:
        return None

    mission_path = Path(mission_path)

    if mission_path.name.lower().endswith(".rules.json"):
        rules_path = mission_path
    else:
        rules_path = mission_path.with_suffix(".rules.json")

    if rules_path.exists():
        print("Mission rules file already exists:", rules_path)
        return rules_path

    default_rules = {
        "rules": []
    }

    try:
        with open(rules_path, "x", encoding="utf-8") as rules_file:
            json.dump(default_rules, rules_file, indent=2)
            rules_file.write("\n")

        print("Created mission rules file:", rules_path)
        return rules_path

    except FileExistsError:
        # Another part of the app may have created it between the check and write.
        return rules_path
    except OSError as error:
        print("Could not create mission rules file:", error)
        return None

def load_volume_percent():
    json_path = USER_DATA_PATH

    try:
        with open(json_path, "r", encoding="utf-8") as file:
            data = json.load(file)
    except FileNotFoundError:
        return 0
    except (OSError, json.JSONDecodeError) as error:
        print("Could not read volume settings:", error)
        return 0

    volume = data.get("volume", 0)

    if not isinstance(volume, (int, float)):
        return 0

    if 0 <= volume <= 1:
        return round(volume * 100)

    if 0 <= volume <= 100:
        return round(volume)

    return 0


def save_volume_setting(volume_percent):
    json_path = USER_DATA_PATH
    volume_percent = max(0, min(100, round(float(volume_percent))))

    data = {}
    try:
        with open(json_path, "r", encoding="utf-8") as file:
            data = json.load(file)
    except FileNotFoundError:
        pass
    except (OSError, json.JSONDecodeError) as error:
        print("Could not read volume settings:", error)

    data["volume"] = volume_percent

    with open(json_path, "w", encoding="utf-8") as file:
        json.dump(data, file, indent=4)
        file.write("\n")

    print("Saved volume:", volume_percent)
    return volume_percent


def usr_data():
    saved_volume = load_volume_percent()
    slider.set(saved_volume)
    print(f"Volume loaded from file: {saved_volume}")
    set_volume(play_preview=False)
    

def select_mission_file():

    global trig_name
    filepath = filedialog.askopenfilename(title="Select a Mission File to Work With!")


    if filepath:
        mission_path_var.set(filepath)
        print("Selected mission file:", filepath)



        mission_file = Path(filepath)
        trig_name = str(mission_file.with_suffix(".trig"))

        # Automatically create the mission rule file beside the .mis file.
        ensure_rules_file_for_mission(mission_file)

        new_results = find_trigger_objects(0, 0, 0)
        refresh_dropdown(new_results)

        # Keep an existing .trig file aligned with this mission immediately.
        if game_dir:
            try:
                mission_relative_name = str(
                    mission_file.relative_to(
                        Path(game_dir) / "Missions"
                    )
                )
            except ValueError:
                mission_relative_name = None

            if mission_relative_name:
                sync_registered_triggers_with_mission(
                    mission_relative_name,
                    force=True
                )

        print("Log file is now:", trig_name)


        
    return filepath



def refresh_dropdown(new_results):
    global results

    if not new_results:
        new_results = ["No triggers found in mission."]

    results = new_results

    menu = dropdown["menu"]
    menu.delete(0, "end")

    selected_option.set(results[0])

    for option in results:
        menu.add_command(
            label=option,
            command=lambda value=option: selected_option.set(value)
        )
def log_print(message):
    print(message)  # still prints to console
    with open(APP_LOG_PATH, "a", encoding="utf-8") as f:
        f.write(message + "\n")


def find_trigger_objects(x=0, y=0, z=0):
    """Return every supported trigger object found in the selected mission."""
    results = []
    filepath = mission_path_var.get()

    if not filepath or not os.path.exists(filepath):
        print("No valid mission file selected.")
        return ["No mission selected."]

    with open(
        filepath,
        "r",
        encoding="utf-8",
        errors="replace"
    ) as mission_file:

        for line in mission_file:
            for object_class, trigger_type in TRIGGER_OBJECTS.items():
                if object_class not in line:
                    continue

                parts = line.split()

                if len(parts) < 6:
                    print("Bad trigger object line:", line.strip())
                    break

                object_id = parts[0]
                trigger_x = parts[3]
                trigger_y = parts[4]
                trigger_z = parts[5]

                results.append(
                    f"{object_id}: {trigger_x}, {trigger_y}, {trigger_z}, "
                    f"Type: {trigger_type}"
                )

                # The line has already matched one trigger object class.
                break

    if not results:
        return ["No triggers found in mission."]

    return results


selected_option = tk.StringVar(root)


def load_mission_trigger_objects(mission_name):
    """Load supported trigger objects currently present in the mission file.

    Results are cached until the mission path or its modification time changes.
    """
    mission_path = get_mission_path(mission_name)

    if mission_path is None or not mission_path.is_file():
        print("Could not find mission file:", mission_path)
        return []

    try:
        modified_time = mission_path.stat().st_mtime_ns
    except OSError as error:
        print("Could not inspect mission file:", mission_path, error)
        return []

    if (
        mission_trigger_cache["path"] == mission_path
        and mission_trigger_cache["modified_time"] == modified_time
    ):
        return mission_trigger_cache["triggers"]

    mission_triggers = []

    try:
        with open(
            mission_path,
            "r",
            encoding="utf-8",
            errors="replace"
        ) as mission_file:

            for line in mission_file:
                for object_class, trigger_type in TRIGGER_OBJECTS.items():
                    if object_class not in line:
                        continue

                    parts = line.split()

                    if len(parts) < 6:
                        print("Bad mission trigger line:", line.strip())
                        break

                    try:
                        coordinates = (
                            float(parts[3]),
                            float(parts[4]),
                            float(parts[5]),
                        )
                    except ValueError:
                        print(
                            "Invalid mission trigger coordinates:",
                            line.strip()
                        )
                        break

                    coordinate_strings = (
                        parts[3].strip(),
                        parts[4].strip(),
                        parts[5].strip(),
                    )

                    mission_triggers.append({
                        "name": parts[0].strip(),
                        "coords": coordinates,
                        "coord_strings": coordinate_strings,
                        "selected": (
                            f"{parts[0].strip()}: "
                            f"{coordinate_strings[0]}, "
                            f"{coordinate_strings[1]}, "
                            f"{coordinate_strings[2]}"
                        ),
                        "type": trigger_type,
                    })

                    break

    except OSError as error:
        print("Could not read mission trigger objects:", error)
        return []

    mission_trigger_cache["path"] = mission_path
    mission_trigger_cache["modified_time"] = modified_time
    mission_trigger_cache["triggers"] = mission_triggers

    print(
        f"Loaded {len(mission_triggers)} trigger objects from "
        f"{mission_path}"
    )

    return mission_triggers



def _coordinate_difference(first, second):
    return math.sqrt(
        (first[0] - second[0]) ** 2
        + (first[1] - second[1]) ** 2
        + (first[2] - second[2]) ** 2
    )


def _safe_trigger_type_conversion(data, mission_type):
    """Apply a .mis trigger type when the existing settings remain usable.

    Cross-family changes sometimes require information that cannot be inferred:
    a sound-playing trigger needs a sound, while a rule-control trigger needs a
    target Rule ID. In those cases the coordinates and object ID are still
    corrected, but the type is left for manual configuration in the editor.
    """
    old_type = data.get("type", "")
    if old_type == mission_type:
        return True

    sound_types = {"Normal", "Repeatable", "Loiter"}
    action_types = {"ActivateRule", "DeactivateRule"}

    if mission_type in action_types:
        if not data.get("target", "").strip():
            print(
                "Could not automatically change trigger type from "
                f"{old_type} to {mission_type}: no target Rule ID exists."
            )
            return False

        data["type"] = mission_type
        data["sound"] = ""
        data["loiter"] = ""
        return True

    if mission_type in sound_types:
        if not data.get("sound", "").strip():
            print(
                "Could not automatically change trigger type from "
                f"{old_type} to {mission_type}: no sound is configured."
            )
            return False

        data["type"] = mission_type
        data["target"] = ""

        if mission_type == "Loiter":
            try:
                if float(data.get("loiter", "")) <= 0:
                    raise ValueError
            except (TypeError, ValueError):
                data["loiter"] = "10"
        else:
            data["loiter"] = ""

        return True

    return False


def sync_registered_triggers_with_mission(
    mission_name,
    force=False,
    threshold=0.1
):
    """Amend .trig entries so the current .mis file is authoritative.

    Matching is primarily by mission object ID. If an object was renumbered,
    a unique object at the same coordinates is used as a fallback.

    Radius, altitude limits, group, Rule ID, loiter duration, and sound paths
    are preserved wherever they remain compatible with the .mis trigger type.
    """
    mission_path = get_mission_path(mission_name)
    trigger_path = get_trigger_path(mission_name)

    if (
        mission_path is None
        or trigger_path is None
        or not mission_path.is_file()
        or not trigger_path.is_file()
    ):
        return 0

    try:
        mission_modified_time = mission_path.stat().st_mtime_ns
        trigger_modified_time = trigger_path.stat().st_mtime_ns
    except OSError as error:
        print("Could not inspect trigger files for synchronization:", error)
        return 0

    if (
        not force
        and trigger_sync_cache["mission_path"] == mission_path
        and trigger_sync_cache["mission_modified_time"]
        == mission_modified_time
        and trigger_sync_cache["trigger_path"] == trigger_path
        and trigger_sync_cache["trigger_modified_time"]
        == trigger_modified_time
    ):
        return 0

    mission_triggers = load_mission_trigger_objects(mission_name)
    if not mission_triggers:
        return 0

    mission_by_name = {
        trigger["name"]: trigger
        for trigger in mission_triggers
    }

    try:
        file_lines = trigger_path.read_text(
            encoding="utf-8",
            errors="replace"
        ).splitlines(keepends=True)
    except OSError as error:
        print("Could not read trigger file for synchronization:", error)
        return 0

    updated_count = 0

    for line_index, line in enumerate(file_lines):
        parsed = parse_registered_trigger_line(line)
        if parsed is None:
            continue

        selected = parsed.get("selected", "").strip()

        try:
            registered_name, coordinate_text = selected.split(":", 1)
            registered_name = registered_name.strip()

            registered_coordinates = tuple(
                float(value.strip())
                for value in coordinate_text.split(",")
            )

            if len(registered_coordinates) != 3:
                raise ValueError

        except (ValueError, TypeError):
            print(
                "Could not synchronize malformed registered trigger:",
                selected
            )
            continue

        mission_trigger = mission_by_name.get(registered_name)

        # If the FMB renumbered the object, use a unique object occupying the
        # same coordinates. Prefer one with the same trigger type.
        if mission_trigger is None:
            nearby = [
                trigger
                for trigger in mission_triggers
                if _coordinate_difference(
                    trigger["coords"],
                    registered_coordinates
                ) <= threshold
            ]

            same_type_nearby = [
                trigger
                for trigger in nearby
                if trigger["type"] == parsed.get("type")
            ]

            if len(same_type_nearby) == 1:
                mission_trigger = same_type_nearby[0]
            elif len(nearby) == 1:
                mission_trigger = nearby[0]

        if mission_trigger is None:
            print(
                "No authoritative .mis object could be matched to "
                f"registered trigger {selected}."
            )
            continue

        coordinates_changed = (
            _coordinate_difference(
                mission_trigger["coords"],
                registered_coordinates
            ) > threshold
        )
        name_changed = mission_trigger["name"] != registered_name
        type_changed = mission_trigger["type"] != parsed.get("type")

        if not (coordinates_changed or name_changed or type_changed):
            continue

        corrected_data = dict(parsed)
        corrected_data["selected"] = mission_trigger["selected"]

        type_was_corrected = True
        if type_changed:
            type_was_corrected = _safe_trigger_type_conversion(
                corrected_data,
                mission_trigger["type"]
            )

        file_lines[line_index] = build_registered_trigger_line(
            corrected_data
        )
        updated_count += 1

        changes = []
        if name_changed:
            changes.append(
                f"ID {registered_name} -> {mission_trigger['name']}"
            )
        if coordinates_changed:
            changes.append("coordinates")
        if type_changed and type_was_corrected:
            changes.append(
                f"type {parsed.get('type')} -> "
                f"{mission_trigger['type']}"
            )
        elif type_changed:
            changes.append(
                "coordinates/ID only; type needs editor configuration"
            )

        print(
            "Amended registered trigger from .mis authority:",
            mission_trigger["selected"],
            "(" + ", ".join(changes) + ")"
        )

    if updated_count:
        temporary_path = trigger_path.with_name(
            trigger_path.name + ".sync_tmp"
        )

        try:
            temporary_path.write_text(
                "".join(file_lines),
                encoding="utf-8"
            )
            os.replace(temporary_path, trigger_path)
        except OSError as error:
            print("Could not write synchronized trigger file:", error)
            try:
                temporary_path.unlink(missing_ok=True)
            except OSError:
                pass
            return 0

        # Existing runtime keys may contain the former coordinates or ID.
        trigger_states.clear()
        disabled_trigger_groups.clear()

        print(
            f"Synchronized {updated_count} registered trigger(s) "
            f"using {mission_path.name}."
        )

    try:
        final_trigger_modified_time = trigger_path.stat().st_mtime_ns
    except OSError:
        final_trigger_modified_time = trigger_modified_time

    trigger_sync_cache["mission_path"] = mission_path
    trigger_sync_cache["mission_modified_time"] = mission_modified_time
    trigger_sync_cache["trigger_path"] = trigger_path
    trigger_sync_cache["trigger_modified_time"] = (
        final_trigger_modified_time
    )

    return updated_count


def compare_trigger(
    object_name,
    trigger_x,
    trigger_y,
    trigger_z,
    mission_name,
    threshold=0.1
):
    """Confirm that a registered .trig entry still exists in the .mis file.

    The object ID must match and its stored coordinates must be within
    threshold metres of the registered coordinates.
    """
    mission_triggers = load_mission_trigger_objects(mission_name)

    target_coordinates = (
        float(trigger_x),
        float(trigger_y),
        float(trigger_z),
    )

    for mission_trigger in mission_triggers:
        if mission_trigger["name"] == object_name.strip():
            return mission_trigger

    # Fallback for an object ID that was renumbered while retaining the same
    # mission coordinates.
    nearby = [
        mission_trigger
        for mission_trigger in mission_triggers
        if _coordinate_difference(
            mission_trigger["coords"],
            target_coordinates
        ) <= threshold
    ]

    if len(nearby) == 1:
        return nearby[0]

    print(
        "Skipping stale registered trigger; no unique .mis object matches "
        f"{object_name} at {target_coordinates}"
    )
    return None


def parse_selected_trigger():
    selected = selected_option.get().strip()

    if ", Type:" not in selected:
        raise ValueError("Selected trigger does not contain a trigger type.")

    trigger_data, trigger_type = selected.rsplit(", Type:", 1)

    return trigger_data.strip(), trigger_type.strip()

if results:
    selected_option.set(results[0])
else:
    selected_option.set("No triggers found.")




def log_selected_option(trig_name):
    try:
        selected_clean, trigger_type = parse_selected_trigger()
    except ValueError as error:
        messagebox.showerror("Invalid Trigger", str(error))
        return

    radius_text = r.get().strip()
    sound_path = selected_sound_path.get().strip()

    # Rule-control markers only activate or deactivate rule IDs.
    # Their audio belongs in the rule JSON, not in the spatial trigger.
    if trigger_type in ("ActivateRule", "DeactivateRule"):
        sound_path = ""

    min_alt_text = min_alt_entry.get().strip()
    max_alt_text = max_alt_entry.get().strip()
    trigger_group = trigger_group_entry.get().strip()

    try:
        radius = float(radius_text)
        if radius <= 0:
            raise ValueError
    except ValueError:
        messagebox.showwarning(
            "Invalid Radius",
            "Please enter a radius greater than zero."
        )
        return

    try:
        min_alt_ft = float(min_alt_text)
        max_alt_ft = float(max_alt_text)

        if min_alt_ft > max_alt_ft:
            raise ValueError
    except ValueError:
        messagebox.showwarning(
            "Invalid Altitude Range",
            "Enter valid minimum and maximum altitudes in feet. "
            "The minimum cannot be greater than the maximum."
        )
        return

    if trigger_type in ("ActivateRule", "DeactivateRule"):
        target_rule = rule_target_entry.get().strip()

        if not target_rule:
            messagebox.showwarning(
                "Missing Rule ID",
                "Enter the rule ID that this zone should control."
            )
            return

        # Rule-control zones are always stored without trigger audio.
        log_line = (
            f"Selected: {selected_clean}, "
            f"Type: {trigger_type}, "
            f"Target: {target_rule}, "
            f"Radius: {radius}, "
            f"MinAltFt: {min_alt_ft}, "
            f"MaxAltFt: {max_alt_ft}, "
            f"Group: {trigger_group}, "
            f"Sound: {sound_path}\n"
        )

    elif trigger_type == "Loiter":
        if not sound_path:
            messagebox.showwarning(
                "No Sound Selected",
                "Please select a sound file."
            )
            return

        try:
            loiter_seconds = float(loiter_entry.get().strip())
            if loiter_seconds <= 0:
                raise ValueError
        except ValueError:
            messagebox.showwarning(
                "Invalid Loiter Time",
                "Loiter triggers require a time greater than zero seconds."
            )
            return

        log_line = (
            f"Selected: {selected_clean}, "
            f"Type: Loiter, "
            f"Loiter: {loiter_seconds}, "
            f"Radius: {radius}, "
            f"MinAltFt: {min_alt_ft}, "
            f"MaxAltFt: {max_alt_ft}, "
            f"Group: {trigger_group}, "
            f"Sound: {sound_path}\n"
        )

    else:
        if not sound_path:
            messagebox.showwarning(
                "No Sound Selected",
                "Please select a sound file."
            )
            return

        log_line = (
            f"Selected: {selected_clean}, "
            f"Type: {trigger_type}, "
            f"Radius: {radius}, "
            f"MinAltFt: {min_alt_ft}, "
            f"MaxAltFt: {max_alt_ft}, "
            f"Group: {trigger_group}, "
            f"Sound: {sound_path}\n"
        )

    with open(trig_name, "a", encoding="utf-8") as trigger_file:
        trigger_file.write(log_line)

    print("Logged trigger:", log_line.strip())


def check_logged_options(trig_name):
    try:
        selected_clean, trigger_type = parse_selected_trigger()
    except ValueError as error:
        messagebox.showerror("Invalid Trigger", str(error))
        return

    existing_selections = set()

    try:
        with open(
            trig_name,
            "r",
            encoding="utf-8",
            errors="replace"
        ) as trigger_file:

            for line in trigger_file:
                if not line.startswith("Selected:"):
                    continue

                match = re.match(
                    r"Selected:\s*(.*?)\s*,\s*Type:",
                    line.strip()
                )

                if match:
                    existing_selections.add(match.group(1).strip())

    except FileNotFoundError:
        pass

    if selected_clean in existing_selections:
        messagebox.showwarning(
            "Duplicate Selection",
            "This trigger object has already been configured."
        )
        return

    # ActivateRule and DeactivateRule are control-only markers.
    # Rule audio is configured with prompt_sound, success_sound, or
    # timeout_sound inside the mission's .rules.json file.
    if trigger_type in ("ActivateRule", "DeactivateRule"):
        selected_system_sound_path.set("")
        selected_sound_path.set("")

    else:
        copy_result = copy_sound_to_mission_folder()
        if copy_result is None:
            return

    log_selected_option(trig_name)

def list_selected_trigger_objects():
    try:
        with open(trig_name, "r") as log:
            for line in log:
                print(line.strip())
    except FileNotFoundError:
        print("No trigger log file exists yet.")

def dialogue():
    soundpath = filedialog.askopenfilename(
        title="Select a sound file",
        initialdir=str(AUDIO_DIR),
        filetypes=(("Audio files", "*.mp3;*.wav"), ("All files", "*.*"))
    )

    if soundpath:
        selected_system_sound_path.set(soundpath)
        print("Selected sound:", soundpath)

        return soundpath

    return None

def copy_sound_to_mission_folder():
    soundpath = selected_system_sound_path.get()
    mission_path = game_dir.get()

    if not soundpath or not os.path.exists(soundpath):
        messagebox.showwarning(
            "No Sound Selected",
            "Please select a sound file first."
        )
        return None

    if not mission_path or not os.path.exists(mission_path):
        messagebox.showwarning(
            "No Mission Selected",
            "Please select a .mis mission file first."
        )
        return None

    mission_dir = Path(mission_path).parent

    target_dir = "audio" / "custom"
    target_dir.mkdir(parents=True, exist_ok=True)

    destination = target_dir / Path(soundpath).name

    shutil.copy(soundpath, destination)

    selected_sound_path.set(str(destination))

    print("Copied sound to:", destination)

    messagebox.showinfo(
        "Sound Copied",
        f"Sound copied to:\n{destination}"
    )

    return destination

# ------------------------ Registered trigger editor ------------------------#

REGISTERED_NORMAL_PATTERN = re.compile(
    r"^Selected:\s*(?P<selected>.*?),\s*"
    r"Type:\s*(?P<type>Normal|Repeatable),\s*"
    r"Radius:\s*(?P<radius>[^,]+),\s*"
    r"(?:MinAltFt:\s*(?P<min_alt>[^,]+),\s*"
    r"MaxAltFt:\s*(?P<max_alt>[^,]+),\s*)?"
    r"(?:Group:\s*(?P<group>[^,]*),\s*)?"
    r"Sound:\s*(?P<sound>.+)$",
    re.IGNORECASE
)

REGISTERED_LOITER_PATTERN = re.compile(
    r"^Selected:\s*(?P<selected>.*?),\s*"
    r"Type:\s*Loiter,\s*"
    r"Loiter:\s*(?P<loiter>[^,]+),\s*"
    r"Radius:\s*(?P<radius>[^,]+),\s*"
    r"(?:MinAltFt:\s*(?P<min_alt>[^,]+),\s*"
    r"MaxAltFt:\s*(?P<max_alt>[^,]+),\s*)?"
    r"(?:Group:\s*(?P<group>[^,]*),\s*)?"
    r"Sound:\s*(?P<sound>.+)$",
    re.IGNORECASE
)

REGISTERED_ACTION_PATTERN = re.compile(
    r"^Selected:\s*(?P<selected>.*?),\s*"
    r"Type:\s*(?P<type>ActivateRule|DeactivateRule),\s*"
    r"Target:\s*(?P<target>[^,]+),\s*"
    r"Radius:\s*(?P<radius>[^,]+),\s*"
    r"(?:MinAltFt:\s*(?P<min_alt>[^,]+),\s*"
    r"MaxAltFt:\s*(?P<max_alt>[^,]+),\s*)?"
    r"(?:Group:\s*(?P<group>[^,]*),\s*)?"
    r"Sound:\s*(?P<sound>.*)$",
    re.IGNORECASE
)


def parse_registered_trigger_line(line):
    """Parse one .trig line into editable values."""
    stripped = line.strip()

    match = REGISTERED_ACTION_PATTERN.match(stripped)
    if match:
        return {
            "selected": match.group("selected").strip(),
            "type": match.group("type").strip(),
            "target": match.group("target").strip(),
            "radius": match.group("radius").strip(),
            "min_alt": (match.group("min_alt") or "0").strip(),
            "max_alt": (match.group("max_alt") or "60000").strip(),
            "group": (match.group("group") or "").strip(),
            "sound": match.group("sound").strip(),
            "loiter": "",
        }

    match = REGISTERED_LOITER_PATTERN.match(stripped)
    if match:
        return {
            "selected": match.group("selected").strip(),
            "type": "Loiter",
            "target": "",
            "radius": match.group("radius").strip(),
            "min_alt": (match.group("min_alt") or "0").strip(),
            "max_alt": (match.group("max_alt") or "60000").strip(),
            "group": (match.group("group") or "").strip(),
            "sound": match.group("sound").strip(),
            "loiter": match.group("loiter").strip(),
        }

    match = REGISTERED_NORMAL_PATTERN.match(stripped)
    if match:
        return {
            "selected": match.group("selected").strip(),
            "type": match.group("type").strip().title(),
            "target": "",
            "radius": match.group("radius").strip(),
            "min_alt": (match.group("min_alt") or "0").strip(),
            "max_alt": (match.group("max_alt") or "60000").strip(),
            "group": (match.group("group") or "").strip(),
            "sound": match.group("sound").strip(),
            "loiter": "",
        }

    return None


def build_registered_trigger_line(data):
    """Build a normalized .trig line from edited values."""
    common = (
        f"Radius: {data['radius']}, "
        f"MinAltFt: {data['min_alt']}, "
        f"MaxAltFt: {data['max_alt']}, "
        f"Group: {data['group']}, "
        f"Sound: {data['sound']}"
    )

    if data["type"] == "Loiter":
        return (
            f"Selected: {data['selected']}, Type: Loiter, "
            f"Loiter: {data['loiter']}, {common}\n"
        )

    if data["type"] in ("ActivateRule", "DeactivateRule"):
        return (
            f"Selected: {data['selected']}, Type: {data['type']}, "
            f"Target: {data['target']}, {common}\n"
        )

    return (
        f"Selected: {data['selected']}, Type: {data['type']}, "
        f"{common}\n"
    )


def open_registered_trigger_editor():
    """Open a GUI for updating or deleting entries in the selected .trig file."""
    mission_path = mission_path_var.get().strip()

    if not mission_path or not os.path.isfile(mission_path):
        messagebox.showwarning(
            "No Mission Selected",
            "Select a valid .mis mission file before editing registered triggers."
        )
        return

    trigger_path = Path(mission_path).with_suffix(".trig")


    if not trigger_path.exists():
        messagebox.showinfo(
            "No Registered Triggers",
            "This mission does not have a .trig file yet."
        )
        return

    editor = tk.Toplevel(root)
    editor.title("Edit Registered Triggers")
    editor.geometry("860x570")
    editor.configure(bg="#111111")
    editor.transient(root)

    trigger_records = []
    file_lines = []
    selected_record = {"record": None}
    replacement_sound = tk.StringVar(value="")

    # Editable Tk variables.
    selected_var = tk.StringVar()
    type_var = tk.StringVar()
    radius_var = tk.StringVar()
    min_alt_var = tk.StringVar()
    max_alt_var = tk.StringVar()
    group_var = tk.StringVar()
    loiter_var = tk.StringVar()
    target_var = tk.StringVar()
    sound_var = tk.StringVar()

    tk.Label(
        editor,
        text="Registered Mission Triggers",
        font=("Arial", 18, "bold"),
        fg="white",
        bg="#111111"
    ).place(x=20, y=15)

    tk.Label(
        editor,
        text=str(trigger_path),
        fg="#aaaaaa",
        bg="#111111",
        wraplength=810,
        justify="left"
    ).place(x=20, y=48)

    list_frame = tk.Frame(editor, bg="#111111")
    list_frame.place(x=20, y=85, width=820, height=180)

    trigger_list = tk.Listbox(
        list_frame,
        bg="#1d1d1d",
        fg="white",
        selectbackground="#3a6ea5",
        activestyle="none",
        font=("Consolas", 10)
    )
    trigger_list.pack(side="left", fill="both", expand=True)

    scrollbar = tk.Scrollbar(list_frame, command=trigger_list.yview)
    scrollbar.pack(side="right", fill="y")
    trigger_list.config(yscrollcommand=scrollbar.set)


    def set_entry_state(entry, enabled):
        entry.config(state="normal" if enabled else "disabled")

    def refresh_type_specific_fields():
        is_loiter = type_var.get() == "Loiter"
        is_action = type_var.get() in ("ActivateRule", "DeactivateRule")

        set_entry_state(loiter_edit, is_loiter)
        set_entry_state(target_edit, is_action)
        set_entry_state(sound_edit, not is_action)
        browse_sound_button.config(
            state="disabled" if is_action else "normal"
        )

        if is_action:
            sound_var.set("")
            replacement_sound.set("")

    def load_file_records(select_index=None):
        nonlocal file_lines, trigger_records
        try:
            file_lines = trigger_path.read_text(
                encoding="utf-8", errors="replace"
            ).splitlines(keepends=True)
        except OSError as error:
            messagebox.showerror("Read Error", str(error), parent=editor)
            return

        trigger_records = []
        trigger_list.delete(0, tk.END)

        for line_index, line in enumerate(file_lines):
            parsed = parse_registered_trigger_line(line)
            if parsed is None:
                continue

            record = {
                "line_index": line_index,
                "data": parsed,
            }
            trigger_records.append(record)
            display_group = parsed["group"] or "—"
            trigger_list.insert(
                tk.END,
                f"{parsed['selected']} | {parsed['type']} | Group: {display_group}"
            )

        if not trigger_records:
            trigger_list.insert(tk.END, "No editable trigger entries found.")
            selected_record["record"] = None
            return

        index = 0 if select_index is None else min(select_index, len(trigger_records) - 1)
        trigger_list.selection_clear(0, tk.END)
        trigger_list.selection_set(index)
        trigger_list.activate(index)
        load_selected_record()

    def load_selected_record(event=None):
        selection = trigger_list.curselection()
        if not selection or not trigger_records:
            return

        index = selection[0]
        if index >= len(trigger_records):
            return

        record = trigger_records[index]
        selected_record["record"] = record
        data = record["data"]

        selected_var.set(data["selected"])
        type_var.set(data["type"])
        radius_var.set(data["radius"])
        min_alt_var.set(data["min_alt"])
        max_alt_var.set(data["max_alt"])
        group_var.set(data["group"])
        loiter_var.set(data["loiter"])
        target_var.set(data["target"])
        sound_var.set(data["sound"])
        replacement_sound.set("")
        refresh_type_specific_fields()

    def choose_replacement_sound():
        if type_var.get() in ("ActivateRule", "DeactivateRule"):
            sound_var.set("")
            replacement_sound.set("")
            return

        chosen = filedialog.askopenfilename(
            parent=editor,
            title="Select replacement sound",
            initialdir=str(AUDIO_DIR),
            filetypes=(("Audio files", "*.mp3;*.wav"), ("All files", "*.*"))
        )
        if chosen:
            replacement_sound.set(chosen)
            sound_var.set(chosen)

    def validated_form_data():
        record = selected_record["record"]
        if record is None:
            messagebox.showwarning(
                "No Trigger Selected",
                "Select a registered trigger first.",
                parent=editor
            )
            return None

        try:
            radius = float(radius_var.get().strip())
            min_alt = float(min_alt_var.get().strip())
            max_alt = float(max_alt_var.get().strip())
            if radius <= 0 or min_alt > max_alt:
                raise ValueError
        except ValueError:
            messagebox.showwarning(
                "Invalid Values",
                "Radius must be greater than zero and minimum altitude cannot exceed maximum altitude.",
                parent=editor
            )
            return None

        data = dict(record["data"])
        data.update({
            "radius": str(radius),
            "min_alt": str(min_alt),
            "max_alt": str(max_alt),
            "group": group_var.get().strip(),
            "sound": sound_var.get().strip(),
            "loiter": loiter_var.get().strip(),
            "target": target_var.get().strip(),
        })

        if data["type"] in ("ActivateRule", "DeactivateRule"):
            data["sound"] = ""

        if data["type"] == "Loiter":
            try:
                if float(data["loiter"]) <= 0:
                    raise ValueError
            except ValueError:
                messagebox.showwarning(
                    "Invalid Loiter Time",
                    "Loiter time must be greater than zero seconds.",
                    parent=editor
                )
                return None

        if data["type"] in ("ActivateRule", "DeactivateRule") and not data["target"]:
            messagebox.showwarning(
                "Missing Rule ID",
                "Rule-control triggers require a Rule ID.",
                parent=editor
            )
            return None

        if data["type"] not in ("ActivateRule", "DeactivateRule") and not data["sound"]:
            messagebox.showwarning(
                "Missing Sound",
                "This trigger type requires a sound file.",
                parent=editor
            )
            return None

        return data

    def save_selected_trigger():
        data = validated_form_data()
        if data is None:
            return

        record = selected_record["record"]
        selected_index = trigger_list.curselection()[0]

        # Copy audio only for sound-playing spatial trigger types.
        # ActivateRule and DeactivateRule entries are always saved without audio.
        new_sound_source = replacement_sound.get().strip()
        if (
            data["type"] not in ("ActivateRule", "DeactivateRule")
            and new_sound_source
        ):
            source_path = Path(new_sound_source)
            if not source_path.exists():
                messagebox.showerror(
                    "Sound Not Found",
                    f"The selected sound file no longer exists:\n{source_path}",
                    parent=editor
                )
                return

            target_dir = game_dir / "audio" / "custom"
            target_dir.mkdir(parents=True, exist_ok=True)
            destination = target_dir / source_path.name

            try:
                shutil.copy2(source_path, destination)
            except OSError as error:
                messagebox.showerror("Copy Error", str(error), parent=editor)
                return

            data["sound"] = str(destination)

        file_lines[record["line_index"]] = build_registered_trigger_line(data)

        try:
            trigger_path.write_text("".join(file_lines), encoding="utf-8")
        except OSError as error:
            messagebox.showerror("Save Error", str(error), parent=editor)
            return

        # Clear runtime state so an edited trigger does not retain stale state.
        trigger_states.clear()
        disabled_trigger_groups.clear()

        print("Updated registered trigger:", data["selected"])
        load_file_records(selected_index)
        messagebox.showinfo(
            "Trigger Updated",
            "The registered trigger was updated successfully.",
            parent=editor
        )

    def delete_selected_trigger():
        record = selected_record["record"]
        if record is None:
            return

        data = record["data"]
        confirmed = messagebox.askyesno(
            "Delete Trigger",
            f"Delete this registered trigger?\n\n{data['selected']}\nType: {data['type']}",
            parent=editor
        )
        if not confirmed:
            return

        selected_index = trigger_list.curselection()[0]
        del file_lines[record["line_index"]]

        try:
            trigger_path.write_text("".join(file_lines), encoding="utf-8")
        except OSError as error:
            messagebox.showerror("Delete Error", str(error), parent=editor)
            return

        trigger_states.clear()
        disabled_trigger_groups.clear()
        selected_record["record"] = None
        load_file_records(max(0, selected_index - 1))
        print("Deleted registered trigger:", data["selected"])

    trigger_list.bind("<<ListboxSelect>>", load_selected_record)

    # Read-only identity fields.
    tk.Label(editor, text="Trigger:", fg="white", bg="#111111").place(x=20, y=285)
    tk.Entry(editor, textvariable=selected_var, state="readonly").place(x=90, y=280, width=470, height=28)
    tk.Label(editor, text="Type:", fg="white", bg="#111111").place(x=580, y=285)
    tk.Entry(editor, textvariable=type_var, state="readonly").place(x=625, y=280, width=215, height=28)

    tk.Label(editor, text="Radius (km):", fg="white", bg="#111111").place(x=20, y=330)
    tk.Entry(editor, textvariable=radius_var).place(x=105, y=325, width=110, height=28)
    tk.Label(editor, text="Min altitude (ft):", fg="white", bg="#111111").place(x=235, y=330)
    tk.Entry(editor, textvariable=min_alt_var).place(x=345, y=325, width=100, height=28)
    tk.Label(editor, text="Max altitude (ft):", fg="white", bg="#111111").place(x=465, y=330)
    tk.Entry(editor, textvariable=max_alt_var).place(x=580, y=325, width=100, height=28)

    tk.Label(editor, text="Group:", fg="white", bg="#111111").place(x=20, y=375)
    tk.Entry(editor, textvariable=group_var).place(x=75, y=370, width=250, height=28)
    tk.Label(editor, text="Loiter seconds:", fg="white", bg="#111111").place(x=350, y=375)
    loiter_edit = tk.Entry(editor, textvariable=loiter_var)
    loiter_edit.place(x=450, y=370, width=100, height=28)
    tk.Label(editor, text="Rule ID:", fg="white", bg="#111111").place(x=575, y=375)
    target_edit = tk.Entry(editor, textvariable=target_var)
    target_edit.place(x=630, y=370, width=210, height=28)

    tk.Label(editor, text="Sound:", fg="white", bg="#111111").place(x=20, y=420)

    sound_edit = tk.Entry(editor, textvariable=sound_var)
    sound_edit.place(x=75, y=415, width=610, height=28)

    browse_sound_button = tk.Button(
        editor,
        text="Browse…",
        command=choose_replacement_sound
    )
    browse_sound_button.place(x=700, y=414, width=140, height=30)

    tk.Button(
        editor,
        text="Save Changes",
        command=save_selected_trigger,
        bg="#245c2a",
        fg="white"
    ).place(x=510, y=500, width=155, height=38)

    tk.Button(
        editor,
        text="Delete Trigger",
        command=delete_selected_trigger,
        bg="#702020",
        fg="white"
    ).place(x=685, y=500, width=155, height=38)

    tk.Button(
        editor,
        text="Close",
        command=editor.destroy
    ).place(x=20, y=500, width=120, height=38)

    load_file_records()

    return trigger_path


#------------------------Tkinter GUI Setup-------------------------#

selected_sound_path = tk.StringVar(value="")
selected_system_sound_path = tk.StringVar(value="")

# ---------- Frames / Screens ----------

main_frame = tk.Frame(root, bg='black')
editor_frame = tk.Frame(root, bg='black')
setup_frame = tk.Frame(root, bg='black')
root.geometry("700x490")

def show_frame(frame):
    main_frame.pack_forget()
    editor_frame.pack_forget()
    setup_frame.pack_forget()

    
    frame.pack(fill="both", expand=True)
   



# ---------- Menu Bar ----------

menubar = tk.Menu(root)

file_menu = tk.Menu(menubar, tearoff=0)
file_menu.add_command(label="Main Screen", command=lambda: show_frame(main_frame))
file_menu.add_command(label="Editor", command=lambda: show_frame(editor_frame))
file_menu.add_command(label="Setup", command=lambda: show_frame(setup_frame))
file_menu.add_separator()
file_menu.add_command(label="Exit", command=root.quit)

menubar.add_cascade(label="File", menu=file_menu)
root.config(menu=menubar)


# ---------- Main Frame ----------

BG = "black"
FG = "white"
MUTED = "#b8b8b8"
BORDER = "white"
CARD_BG = "#111111"
GREEN = "#2ecc71"
RED = "#e74c3c"
COORDINATE_TIMEOUT_SECONDS = 1.0

main_frame.config(bg=BG)

# -------------------------
# Header
# -------------------------

tk.Label(
    main_frame,
    text="Bandits, Twelve O'clock!",
    bg=BG,
    fg=FG,
    font=("Arial", 25, "bold")
).place(x=20, y=15)

tk.Label(
    main_frame,
    text="IL-2 1946 Triggered Mission Audio Companion",
    bg=BG,
    fg=MUTED,
    font=("Arial", 12)
).place(x=23, y=52)


# -------------------------
# Welcome Card
# -------------------------

welcome_card = tk.Frame(
    main_frame,
    bg=CARD_BG,
    highlightbackground=BORDER,
    highlightthickness=2
)
welcome_card.place(x=20, y=85, width=660, height=90)

tk.Label(
    welcome_card,
    bg=CARD_BG,
    fg=FG,
    text=(
        "Welcome to Bandits, Twelve O'clock! This companion app enables "
        "triggerable sound effects in campaigns and missions for IL-2 1946."
    ),
    wraplength=620,
    justify="left",
    font=("Arial", 13)
).place(x=15, y=12)

# tk.Label(
#     welcome_card,
#     bg=CARD_BG,
#     fg=MUTED,
#     text="First time setup: open the Setup tab and select your IL-2 game directory.",
#     wraplength=620,
#     justify="left",
#     font=("Arial", 10)
# ).place(x=15, y=58)


# -------------------------
# Cassette Panel
# -------------------------

# cassette_panel = tk.Frame(
#     main_frame,
#     bg=CARD_BG,
#     highlightbackground=BORDER,
#     highlightthickness=2
# )
# cassette_panel.place(x=20, y=200, width=305, height=190)

# tk.Label(
#    cassette_panel,
#    text="Audio System",
#    bg=CARD_BG,
#    fg=FG,
#    font=("Arial", 14, "bold")
#).place(x=15, y=12)

# tk.Label(
  #  cassette_panel,
   # text="Cassette deck active",
    #bg=CARD_BG,
    #fg=MUTED,
    #font=("Arial", 10)
# ).place(x=15, y=38)

# cassette_pil = Image.open(IMAGES_DIR / "cassete.png").convert("RGBA").resize((220, 220))
# wheel_pil = Image.open(IMAGES_DIR / "cassetewheel.png").convert("RGBA").resize((34, 34))

# cassette_tk = ImageTk.PhotoImage(cassette_pil)

# cassette_canvas = tk.Canvas(
#     cassette_panel,
#     width=260,
#     height=125,
#     bg=CARD_BG,
#     highlightthickness=0,
#     borderwidth=0
# )
# cassette_canvas.place(x=22, y=55)

# # Draw cassette body.
# # The negative Y pulls the 220px image upward so it fits nicely inside the visible canvas.
# cassette_canvas.create_image(20, -45, image=cassette_tk, anchor="nw")
# cassette_canvas.cassette_tk = cassette_tk

# left_wheel_tk = ImageTk.PhotoImage(wheel_pil)
# right_wheel_tk = ImageTk.PhotoImage(wheel_pil)

# left_wheel_item = cassette_canvas.create_image(
#     87, 57,
#     image=left_wheel_tk,
#     anchor="center"
# )

# right_wheel_item = cassette_canvas.create_image(
#     173, 57,
#     image=right_wheel_tk,
#     anchor="center"
# )

# cassette_canvas.left_wheel_tk = left_wheel_tk
# cassette_canvas.right_wheel_tk = right_wheel_tk

# angle = 0
# dospin = False

# def spin_wheels():
#     global angle

#     left_rotated = wheel_pil.rotate(
#         angle,
#         resample=Image.Resampling.BICUBIC,
#         expand=False
#     )

#     right_rotated = wheel_pil.rotate(
#         -angle,
#         resample=Image.Resampling.BICUBIC,
#         expand=False
#     )

#     left_tk = ImageTk.PhotoImage(left_rotated)
#     right_tk = ImageTk.PhotoImage(right_rotated)

#     cassette_canvas.itemconfig(left_wheel_item, image=left_tk)
#     cassette_canvas.itemconfig(right_wheel_item, image=right_tk)

#     cassette_canvas.left_wheel_tk = left_tk
#     cassette_canvas.right_wheel_tk = right_tk
    
#     if dospin == True:
#         angle = (angle + 10) % 360
#         root.after(40, spin_wheels)
#     else:
#         angle = (angle)

# spin_wheels()


# -------------------------
# DeviceLink Status Panel
# -------------------------

status_panel = tk.Frame(
    main_frame,
    bg=CARD_BG,
    highlightbackground=BORDER,
    highlightthickness=2
)
status_panel.place(x=20, y=200, width=660, height=140)

tk.Label(
    status_panel,
    text="Status",
    bg=CARD_BG,
    fg=FG,
    font=("Arial", 15, "bold")
).place(x=18, y=15)

status_canvas = tk.Canvas(
    status_panel,
    width=24,
    height=24,
    bg=CARD_BG,
    highlightthickness=0
)
status_canvas.place(x=20, y=55)



oval = status_canvas.create_oval(
    5, 5, 19, 19,
    fill=RED,
    outline=RED
)

status_text = tk.StringVar(value="Listening")

tk.Label(
    status_panel,
    textvariable=status_text,
    bg=CARD_BG,
    fg=FG,
    font=("Arial", 14, "bold")
).place(x=52, y=53)

tk.Label(
    status_panel,
    text="Waiting for aircraft position data from IL-2.",
    bg=CARD_BG,
    fg=MUTED,
    font=("Arial", 10),
    wraplength=260,
    justify="left"
).place(x=52, y=82)

support_panel = tk.Frame(
    main_frame,
    bg=CARD_BG,
    highlightbackground=BORDER,
    highlightthickness=2
)
support_panel.place(x=20, y=365, width=660, height=100)

tk.Label(
    support_panel,
    text="Support me!",
    bg=CARD_BG,
    fg=FG,
    font=("Arial", 14, "bold")
).place(x=10, y=10)

def open_discord():
    webbrowser.open("https://discord.gg/ejtcsGWugs")

def open_kofi():
    webbrowser.open("https://ko-fi.com/sercrets")

discord_img = Image.open(IMAGES_DIR / "Discord.png").convert("RGBA")
discord_bbox = discord_img.getchannel("A").getbbox()
if discord_bbox:
    discord_img = discord_img.crop(discord_bbox)
discord_img.thumbnail((48, 48), Image.Resampling.LANCZOS)
discord_tk = ImageTk.PhotoImage(discord_img)

discord_button = tk.Button(
    support_panel,
    image=discord_tk,
    command=open_discord,
    bg=CARD_BG,
    activebackground=CARD_BG,
    borderwidth=0
)
discord_button.place(x=10, y=40, width=48, height=48)

kofi_img = Image.open(IMAGES_DIR / "Kofi.png").convert("RGBA")
kofi_img.thumbnail((96, 32), Image.Resampling.LANCZOS)
kofi_tk = ImageTk.PhotoImage(kofi_img)

kofi_button = tk.Button(
    support_panel,
    image=kofi_tk,
    command=open_kofi,
    bg=CARD_BG,
    activebackground=CARD_BG,
    borderwidth=0
)
kofi_button.place(x=105, y=47, width=96, height=32)

youtube_img = Image.open(IMAGES_DIR / "YouTube.png").convert("RGBA")
youtube_bbox = youtube_img.getchannel("A").getbbox()
if youtube_bbox:
    youtube_img = youtube_img.crop(youtube_bbox)
youtube_img.thumbnail((40, 40), Image.Resampling.LANCZOS)
youtube_tk = ImageTk.PhotoImage(youtube_img)

youtube_button = tk.Button(
    support_panel,
    image=youtube_tk,
    command=lambda: webbrowser.open(
        "https://www.youtube.com/@sercrets9531"
    ),
    bg=CARD_BG,
    activebackground=CARD_BG,
    borderwidth=0,
    highlightthickness=0,
    padx=0,
    pady=0,
    relief="flat"
)
youtube_button.place(x=62, y=45, width=40, height=40)

# tk.Label(
#     status_panel,
#     text="UDP Port: 21101",
#     bg=CARD_BG,
#     fg=FG,
#     font=("Arial", 11)
# ).place(x=20, y=120)

# tk.Label(
#     status_panel,
#     text="Use the Editor tab to bind mission triggers to sound files.",
#     bg=CARD_BG,
#     fg=MUTED,
#     font=("Arial", 10),
#     wraplength=285,
#     justify="left"
# ).place(x=20, y=145)

# ---------- Editor Frame ----------

def clear_placeholder(event=None):
    if r.get() == "Enter radius in km":
        r.delete(0, tk.END)
        r.config(fg="black")


mission_path = "Wait, did you select a mission file? If not, select one using the button!"

# ---------- Editor Frame Styling ----------
editor_frame.config(bg="#111111")

# ---------- Header ----------
tk.Label(
    editor_frame,
    text="Trigger Configuration Page",
    font=("Arial", 18, "bold"),
    fg="white",
    bg="#111111"
).place(x=20, y=15)

canvas = tk.Canvas(editor_frame, width=660, height=2, bg="#444444", highlightthickness=0)
canvas.place(x=20, y=55)

# ---------- Mission File Section ----------
tk.Label(
    editor_frame,
    text="Mission File",
    font=("Arial", 11, "bold"),
    fg="white",
    bg="#111111"
).place(x=20, y=75)

tk.Label(
    editor_frame,
    textvariable=mission_path_var,
    wraplength=450,
    justify="left",
    fg="#cccccc",
    bg="#111111"
).place(x=20, y=100)

tk.Button(
    editor_frame,
    text="Select your .mis file.",
    command=select_mission_file
).place(x=510, y=95, width=160, height=30)

# ---------- Instructions ----------
tk.Label(
    editor_frame,
    text="Select a trigger from the dropdown menu, then set the radius for the trigger and select a sound file to play when you enter the trigger zone.",
    wraplength=640,
    justify="left",
    fg="#dddddd",
    bg="#111111"
).place(x=20, y=145)

# ---------- Trigger Settings Section ----------
tk.Label(
    editor_frame,
    text="Trigger Settings",
    font=("Arial", 11, "bold"),
    fg="white",
    bg="#111111"
).place(x=20, y=200)

tk.Label(
    editor_frame,
    text="Trigger:",
    fg="white",
    bg="#111111"
).place(x=20, y=230)

results = find_trigger_objects()

if not results:
    results = ["No triggers found."]

selected_option = tk.StringVar(root)
selected_option.set(results[0])

dropdown = tk.OptionMenu(editor_frame, selected_option, *results)
dropdown.config(width=38)
dropdown.place(x=90, y=225, width=350, height=32)

tk.Label(
    editor_frame,
    text="Radius:",
    fg="white",
    bg="#111111"
).place(x=460, y=230)

r = tk.Entry(editor_frame, fg="black")
r.insert(0, "Enter radius in km")
r.place(x=520, y=226, width=150, height=30)

r.bind("<FocusIn>", clear_placeholder)

# ---------- Altitude Range Section ----------
tk.Label(
    editor_frame,
    text="Altitude Range:",
    font=("Arial", 11, "bold"),
    fg="white",
    bg="#111111"
).place(x=20, y=270)

# tk.Label(
#    editor_frame,
#    text="Min (ft):",
#    fg="white",
 #   bg="#111111"
#).place(x=150, y=272)

min_alt_entry = tk.Entry(editor_frame)
min_alt_entry.insert(0, "Min (feet)")
min_alt_entry.place(x=150, y=267, width=90, height=30)

def min_alt_clear():
    if min_alt_entry.get() == "Min (feet)":
        min_alt_entry.delete(0, tk.END)
        min_alt_entry.config(fg="black")

min_alt_entry.bind("<FocusIn>", lambda event: min_alt_clear())

# tk.Label(
#    editor_frame,
#    text="Max (ft):",
#    fg="white",
#    bg="#111111"
# ).place(x=470, y=272)

max_alt_entry = tk.Entry(editor_frame)
max_alt_entry.insert(0, "Max (feet)")
max_alt_entry.place(x=250, y=267, width=90, height=30)

def max_alt_clear():
    if max_alt_entry.get() == "Max (feet)":
        max_alt_entry.delete(0, tk.END)
        max_alt_entry.config(fg="black")

max_alt_entry.bind("<FocusIn>", lambda event: max_alt_clear())

# ---------- Trigger Group Section ----------
tk.Label(
    editor_frame,
    text="Trigger Group (optional):",
    fg="white",
    bg="#111111"
).place(x=20, y=380)

trigger_group_entry = tk.Entry(editor_frame)
trigger_group_entry.place(x=165, y=375, width=275, height=30)

# tk.Label(
 #   editor_frame,
 #   text="First trigger played disables the whole group.",
 #   fg="#aaaaaa",
 #   bg="#111111"
#).place(x=450, y=440)

# ---------- Sound Section ----------
sound_label = tk.Label(
    editor_frame,
    text="Sound File",
    font=("Arial", 11, "bold"),
    fg="white",
    bg="#111111"
)
sound_value_label = tk.Label(
    editor_frame,
    textvariable=selected_system_sound_path,
    fg="white",
    bg="#111111"
)

sound_select_button = tk.Button(
    editor_frame,
    text="Select Sound File",
    command=dialogue
)
sound_select_button.place(x=510, y=320, width=160, height=30)

# ---------- Bottom Action ----------
tk.Button(
    editor_frame,
    text="Set Trigger",
    command=lambda: check_logged_options(trig_name)
).place(x=510, y=370, width=160, height=35)


tk.Button(
    editor_frame,
    text="Advanced Trigger Editor",
    command=open_registered_trigger_editor
).place(x=490, y=420, width=195, height=35)

loiter_label = tk.Label(
    editor_frame,
    text="Loiter Time:",
    fg="white",
    bg="#111111"
)

loiter_entry = tk.Entry(editor_frame)
loiter_entry.insert(0, "10")

rule_target_label = tk.Label(
    editor_frame,
    text="Rule ID:",
    fg="white",
    bg="#111111"
)

rule_target_entry = tk.Entry(editor_frame)


def update_loiter_controls(*args):
    selected = selected_option.get().strip()
    is_activate_rule = selected.endswith("Type: ActivateRule")
    is_deactivate_rule = selected.endswith("Type: DeactivateRule")
    is_rule_control = is_activate_rule or is_deactivate_rule

    if selected.endswith("Type: Loiter"):
        loiter_label.place(x=20, y=305)
        loiter_entry.place(x=100, y=300, width=80, height=30)
    else:
        loiter_label.place_forget()
        loiter_entry.place_forget()

    if is_rule_control:
        rule_target_label.place(x=20, y=325)
        rule_target_entry.place(x=70, y=320, width=180, height=30)
        sound_label.place_forget()
        sound_value_label.place_forget()
        sound_select_button.place_forget()
    else:
        rule_target_label.place_forget()
        rule_target_entry.place_forget()
        sound_label.place(x=20, y=320)
        sound_value_label.place(x=20, y=320)
        sound_select_button.place(x=510, y=320, width=160, height=30)

    # Rule-control markers are intentionally silent. Their audio belongs
    # in the rule JSON through prompt_sound, success_sound, or timeout_sound.
    if is_rule_control:
        selected_system_sound_path.set("")
        selected_sound_path.set("")
        sound_select_button.config(state="disabled")
    else:
        sound_select_button.config(state="normal")


selected_option.trace_add("write", update_loiter_controls)

# Run it once so the correct controls are shown when the page opens.
update_loiter_controls()

# ---------- Settings Frame ----------

# ---------- Settings Frame ----------

selected_game_directory = tk.StringVar(value="")


def game_directory_select():
    global game_dir
    game_dir = filedialog.askdirectory(title="Select your IL-2 1946 Game Directory")

    if game_dir:
        print("Selected game directory:", game_dir)
        selected_game_directory.set(game_dir)

        with open(GAME_INFO_PATH, "w", encoding="utf-8") as f:
            f.write(game_dir)

        game_path_label.config(text=f"Selected:\n{game_dir}")
        return game_dir

    return None


def check_if_game_directory():
    try:
        with open(GAME_INFO_PATH, "r", encoding="utf-8") as f:
            path = f.read().strip()

        if os.path.isdir(path):
            selected_game_directory.set(path)
            print(path)
            return path

        print("No valid game directory found. Please select one.")
        return None

    except FileNotFoundError:
        print(f"{GAME_INFO_PATH} not found. Please select your game directory.")
        return None


def set_volume(play_preview=True):
    volume_percent = max(0, min(100, round(float(slider.get()))))
    volume = volume_percent / 100

    pygame.mixer.music.set_volume(volume)
    volume_value_label.config(text=f"{volume_percent}%")
    save_volume_setting(volume_percent)
    soundlevel.set_volume(volume)

    if play_preview:
        soundlevel.play()

    return volume


setup_frame.config(bg="black")

game_dir = check_if_game_directory()
saved_game_path = game_dir


tk.Label(
    setup_frame,
    text="Setup",
    font=("Arial", 18, "bold"),
    bg="black",
    fg="white"
).pack(pady=(14, 2))


tk.Label(
    setup_frame,
    text="Select your IL-2 1946 game folder and set the sound volume.",
    font=("Arial", 11),
    bg="black",
    fg="gray80",
    wraplength=600,
    justify="center"
).pack(pady=(0, 8))


tk.Frame(
    setup_frame,
    bg="gray35",
    height=2,
    width=600
).pack(pady=(0, 10))


# Game directory section
game_box = tk.Frame(
    setup_frame,
    bg="black",
    highlightbackground="gray35",
    highlightthickness=1
)
game_box.pack(pady=(0, 8), padx=35, fill="x")


tk.Label(
    game_box,
    text="Game Directory",
    font=("Arial", 13, "bold"),
    bg="black",
    fg="white"
).pack(pady=(8, 3))


tk.Label(
    game_box,
    text="This app needs your IL-2 1946 path so it can find the correct files.",
    font=("Arial", 10),
    bg="black",
    fg="gray80",
    wraplength=560,
    justify="center"
).pack(pady=(0, 4))


game_path_label = tk.Label(
    game_box,
    text=(
        f"Selected:\n{saved_game_path}"
        if saved_game_path
        else "No valid game directory selected."
    ),
    font=("Arial", 9),
    bg="black",
    fg="gray70",
    wraplength=560,
    justify="center"
)
game_path_label.pack(pady=(0, 5))


tk.Button(
    game_box,
    text="Select Game Directory",
    command=game_directory_select,
    bg="gray20",
    fg="white",
    activebackground="gray35",
    activeforeground="white",
    relief="flat",
    font=("Arial", 10),
    width=24
).pack(pady=(0, 8))


# Volume section
volume_box = tk.Frame(
    setup_frame,
    bg="black",
    highlightbackground="gray35",
    highlightthickness=1
)
volume_box.pack(pady=(0, 8), padx=35, fill="x")


volume_row = tk.Frame(volume_box, bg="black")
volume_row.pack(pady=8)


tk.Label(
    volume_row,
    text="Volume:",
    font=("Arial", 12, "bold"),
    bg="black",
    fg="white"
).pack(side="left", padx=(0, 10))


slider = Scale(
    volume_row,
    from_=0,
    to=100,
    orient=HORIZONTAL,
    background="black",
    fg="white",
    troughcolor="#333333",
    highlightthickness=0,
    length=260,
    activebackground="gray35"
)
slider.pack(side="left")


volume_value_label = tk.Label(
    volume_row,
    text="0%",
    font=("Arial", 10),
    bg="black",
    fg="gray80",
    width=5
)
volume_value_label.pack(side="left", padx=(8, 0))


tk.Button(
    volume_box,
    text="Apply Volume",
    command=set_volume,
    bg="gray20",
    fg="white",
    activebackground="gray35",
    activeforeground="white",
    relief="flat",
    font=("Arial", 10),
    width=24
).pack(pady=(0, 8))


tk.Button(
    setup_frame,
    text="Back to Main",
    command=lambda: show_frame(main_frame),
    bg="gray20",
    fg="white",
    activebackground="gray35",
    activeforeground="white",
    relief="flat",
    font=("Arial", 10),
    width=24
).pack(pady=(0, 5))
# Start app on main screen
show_frame(main_frame)

#------------------------UDP Listener and Trigger Check-------------------------#

last_coordinate_time = None

def receive_coordinates():
    latest_data = None

    try:
        while True:
            data, addr = sock.recvfrom(4096)
            latest_data = data
            

    except socket.timeout:
        pass

    if latest_data is not None:
        try:
            x, y, z = latest_data.decode(
                "US-ASCII",
                errors="replace"
            ).split(",", 2)

            sim_x = float(x)
            sim_y = float(y)
            sim_z = float(z)

            global last_coordinate_time
            last_coordinate_time = time.monotonic()
            print(f"Latest coordinates: {sim_x}, {sim_y}, {sim_z}")

            trigger_check(
                sim_x,
                sim_y,
                sim_z,
                last_mission
            )

            evaluate_active_rules()


        except ValueError as error:
            print("Bad coordinate packet:", error)

    if (
        last_coordinate_time is not None
        and time.monotonic() - last_coordinate_time <= COORDINATE_TIMEOUT_SECONDS
    ):
        status_canvas.itemconfig(oval, fill=GREEN, outline=GREEN)
        status_text.set("Receiving")
    else:
        status_canvas.itemconfig(oval, fill=RED, outline=RED)
        status_text.set("Listening")


    root.after(10, receive_coordinates)

last_mission = None

last_mission = None
trimmed_name = None

game_dir = check_if_game_directory()


def get_game_log_path():
    """Return the IL-2 log file inside the game directory selected in Setup."""
    if not game_dir:
        return None
    return Path(game_dir) / "log.lst"


def reset_mission_runtime_state():
    """Reset every trigger and rule whenever IL-2 loads a mission."""
    # Normal triggers become armed again, Repeatable triggers forget whether
    # the aircraft was inside them, and Loiter timers/completion are cleared.
    trigger_states.clear()
    disabled_trigger_groups.clear()

    mission_trigger_cache["path"] = None
    mission_trigger_cache["modified_time"] = None
    mission_trigger_cache["triggers"] = []

    trigger_sync_cache["mission_path"] = None
    trigger_sync_cache["mission_modified_time"] = None
    trigger_sync_cache["trigger_path"] = None
    trigger_sync_cache["trigger_modified_time"] = None

    # Rule state is also cleared here. load_mission_rules() immediately
    # rebuilds these collections for the newly loaded mission.
    active_rules.clear()
    mission_rules.clear()
    rule_states.clear()

    # Do not carry old telemetry into the newly loaded mission.
    with telemetry_lock:
        telemetry_values.clear()

    # Stop any voice line left over from the previous mission session.
    try:
        pygame.mixer.music.stop()
    except pygame.error as error:
        print("Could not stop previous mission audio:", error)

    print("Mission runtime state reset: all triggers are Unplayed.")


def watch_log():
    global last_mission, trimmed_name

    while True:
        log_path = get_game_log_path()

        if log_path is None or not log_path.is_file():
            time.sleep(1.0)
            continue

        try:
            with open(log_path, "r", encoding="utf-8", errors="replace") as log:
                log.seek(0, 2)

                while True:
                    # Reopen the watcher if the user selects another game folder.
                    if log_path != get_game_log_path():
                        break

                    line = log.readline()

                    if not line:
                        time.sleep(0.1)
                        continue

                    if "Loading mission " in line:
                        last_mission = line.partition("Loading mission ")[2].strip()
                        print("Last loaded mission:", last_mission)

                        # This runs even when the same mission is loaded again.
                        # Every Normal/Loiter/rule trigger starts fresh.
                        reset_mission_runtime_state()

                        # Amend stale .trig IDs, coordinates, and compatible
                        # types before the mission begins processing triggers.
                        sync_registered_triggers_with_mission(
                            last_mission,
                            force=True
                        )

                        trimmed_name = trim_mission_name(last_mission)
                        load_mission_rules(last_mission)

        except OSError as error:
            print("Could not watch IL-2 log file:", error)
            time.sleep(1.0)


def trim_mission_name(mission_name):
    if not mission_name:
        print("No mission name to trim.")
        return None

    cleaned_name = mission_name.strip().rstrip(".")
    trimmed_name = cleaned_name.replace("\\", "/").split("/")[-1]

    if trimmed_name.lower().endswith(".mis"):
        trimmed_name = trimmed_name[:-4]

    print("Trimmed mission name:", trimmed_name)
    return trimmed_name

def get_trigger_path(mission_name):
    if not mission_name:
        return None

    if not game_dir:
        print("No game directory selected.")
        return None

    cleaned_name = mission_name.strip().rstrip(".")
    cleaned_name = cleaned_name.replace("\\", os.sep).replace("/", os.sep)
    mission_folder = "Missions"

    mission_path = Path(game_dir) / mission_folder / cleaned_name
    trig_path = mission_path.with_suffix(".trig")

    print("Looking for trigger file:", trig_path)

    return trig_path

def loiter_calc(sound_info):
    # Deprecated - loiter logic handled in trigger_check using per-trigger state
    return

# ------------------------ Generic mission-rule engine ------------------------#

def get_mission_path(mission_name):
    if not mission_name or not game_dir:
        return None

    cleaned_name = mission_name.strip().rstrip(".")
    cleaned_name = cleaned_name.replace("\\", os.sep).replace("/", os.sep)
    return Path(game_dir) / "Missions" / cleaned_name


def get_rules_path(mission_name):
    mission_path = get_mission_path(mission_name)
    if mission_path is None:
        return None
    return mission_path.with_suffix(".rules.json")


def load_mission_rules(mission_name):
    global mission_rules, rule_states, current_rules_path

    rules_path = get_rules_path(mission_name)
    current_rules_path = rules_path
    mission_rules = {}
    rule_states = {}
    active_rules.clear()

    if rules_path is None:
        return

    # Missions loaded directly by IL-2 also receive an empty rule file
    # automatically, even if they were never opened in the editor.
    # Pass the real mission path, not a filename derived from rules_path.
    mission_path = get_mission_path(mission_name)
    ensure_rules_file_for_mission(mission_path)

    try:
        with open(rules_path, "r", encoding="utf-8", errors="replace") as file:
            data = json.load(file)
    except FileNotFoundError:
        print("No mission rule file found:", rules_path)
        return
    except (OSError, json.JSONDecodeError) as error:
        print("Could not load mission rule file:", error)
        return

    for rule in data.get("rules", []):
        rule_id = str(rule.get("id", "")).strip()
        if not rule_id:
            print("Ignoring rule without an id:", rule)
            continue

        mission_rules[rule_id] = rule
        rule_states[rule_id] = {
            "true_since": None,
            "last_played": None,
            "completed": False,
            "activated_at": None,
        }

        if rule.get("active_at_start", False):
            active_rules.add(rule_id)
            rule_states[rule_id]["activated_at"] = time.monotonic()

    print(f"Loaded {len(mission_rules)} mission rules from {rules_path}")


def collect_rule_parameters():
    names = set()

    def visit_condition(condition):
        if not isinstance(condition, dict):
            return
        parameter = condition.get("parameter")
        if parameter in DEVICE_LINK_PARAMETERS:
            names.add(parameter)

        for key in ("all", "any"):
            for child in condition.get(key, []):
                visit_condition(child)

    for rule in mission_rules.values():
        visit_condition(rule)

    return names


def parse_devicelink_reply(reply):
    """Parse stock DeviceLink replies into rule telemetry values.

    RPM is engine-specific and can appear as:
        A/64\\0\\825.0
        A/64\\1\\790.0

    The first value after key 64 is the zero-based engine index. The last
    value is the engine RPM. Engine zero is stored under both "rpm0" and the
    backwards-compatible alias "rpm".
    """
    updates = {}

    # RPM names deliberately share DeviceLink key 64, so exclude them from
    # the ordinary one-key-to-one-name lookup.
    non_rpm_key_to_name = {
        parameter_id: name
        for name, parameter_id in DEVICE_LINK_PARAMETERS.items()
        if name != "rpm" and not name.startswith("rpm")
    }

    for match in re.finditer(r"/(\d+)\\([^/]+)", reply):
        key = int(match.group(1))
        response_section = match.group(2).strip()

        parts = [
            part.strip()
            for part in response_section.split("\\")
            if part.strip()
        ]

        if not parts:
            continue

        # RPM requires both DeviceLink key 64 and an engine index.
        if key == DEVICE_LINK_PARAMETERS["rpm0"]:
            try:
                if len(parts) >= 2:
                    engine_index = int(float(parts[0]))
                    rpm_value = float(parts[-1])
                else:
                    # Be tolerant of an unindexed RPM reply and treat it as
                    # engine zero.
                    engine_index = 0
                    rpm_value = float(parts[-1])
            except (TypeError, ValueError):
                print("Could not parse RPM DeviceLink reply:", match.group(0))
                continue

            if 0 <= engine_index <= 3:
                updates[f"rpm{engine_index}"] = rpm_value

                if engine_index == 0:
                    updates["rpm"] = rpm_value
            else:
                print(
                    "Ignoring unsupported RPM engine index:",
                    engine_index
                )

            continue

        name = non_rpm_key_to_name.get(key)
        if not name:
            continue

        raw_value = parts[-1]

        try:
            value = float(raw_value)
        except ValueError:
            value = raw_value

        updates[name] = value

    return updates

def devicelink_poll_loop():
    client = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    client.settimeout(0.2)
    target = (DEVICELINK_HOST, DEVICELINK_PORT)

    while True:
        parameter_names = collect_rule_parameters()

        if not parameter_names:
            time.sleep(0.25)
            continue

        query_parts = []
        requested_parts = set()

        for name in sorted(parameter_names):
            parameter_id = DEVICE_LINK_PARAMETERS[name]

            if name in ("rpm", "rpm0"):
                query_part = f"/{parameter_id}\\0"
            elif name == "rpm1":
                query_part = f"/{parameter_id}\\1"
            elif name == "rpm2":
                query_part = f"/{parameter_id}\\2"
            elif name == "rpm3":
                query_part = f"/{parameter_id}\\3"
            else:
                query_part = f"/{parameter_id}"

            # A rules file may use both "rpm" and "rpm0". They represent the
            # same telemetry value, so request engine zero only once.
            if query_part not in requested_parts:
                requested_parts.add(query_part)
                query_parts.append(query_part)

        query = "R" + "".join(query_parts)

        try:
            client.sendto(query.encode("ascii"), target)
            data, _ = client.recvfrom(8192)
            reply = data.decode("ascii", errors="replace")
            updates = parse_devicelink_reply(reply)

            if updates:
                with telemetry_lock:
                    telemetry_values.update(updates)

        except socket.timeout:
            pass
        except OSError as error:
            print("Stock DeviceLink error:", error)
            time.sleep(1.0)

        time.sleep(0.05)

def compare_value(actual, operator_name, expected):
    """Compare rule values while safely normalizing numeric strings."""
    try:
        actual = float(actual)

        if operator_name == "between":
            if not isinstance(expected, (list, tuple)) or len(expected) != 2:
                raise ValueError(
                    "The 'between' operator requires two values."
                )

            expected = (
                float(expected[0]),
                float(expected[1]),
            )
        else:
            expected = float(expected)

    except (TypeError, ValueError, IndexError):
        # Non-numeric parameters can still use equality comparisons.
        pass

    if operator_name == ">":
        return actual > expected
    if operator_name == ">=":
        return actual >= expected
    if operator_name == "<":
        return actual < expected
    if operator_name == "<=":
        return actual <= expected
    if operator_name == "==":
        return actual == expected
    if operator_name == "!=":
        return actual != expected
    if operator_name == "between":
        low, high = expected
        return low <= actual <= high

    raise ValueError(f"Unsupported operator: {operator_name}")


def evaluate_condition(condition, telemetry):
    if "all" in condition:
        return all(
            evaluate_condition(child, telemetry)
            for child in condition["all"]
        )

    if "any" in condition:
        return any(
            evaluate_condition(child, telemetry)
            for child in condition["any"]
        )

    parameter = condition.get("parameter")
    operator_name = condition.get("operator", "==")
    expected = condition.get("value")

    if parameter not in telemetry:
        return False

    actual = telemetry[parameter]

    if condition.get("absolute", False):
        actual = abs(actual)

    try:
        return compare_value(actual, operator_name, expected)
    except (TypeError, ValueError) as error:
        print("Could not evaluate condition:", condition, error)
        return False


def resolve_rule_sound(sound_path):
    if not sound_path:
        return None

    path = Path(sound_path)
    if path.is_absolute():
        return path

    mission_path = get_mission_path(last_mission)
    if mission_path is None:
        return path

    return mission_path.parent / sound_path


def play_rule_sound(sound_path):
    resolved = resolve_rule_sound(sound_path)

    if resolved is None:
        return False

    if pygame.mixer.music.get_busy():
        return False

    try:
        pygame.mixer.music.load(str(resolved))
        pygame.mixer.music.set_volume(slider.get() / 100)
        pygame.mixer.music.play()
        print("Playing rule sound:", resolved)
        return True
    except Exception as error:
        print("Could not play rule sound:", resolved, error)
        return False


def activate_rule(rule_id):
    if rule_id not in mission_rules:
        print(f"Cannot activate unknown rule: {rule_id}")
        return

    state = rule_states.setdefault(rule_id, {})
    state["true_since"] = None
    state["completed"] = False
    state["activated_at"] = time.monotonic()
    active_rules.add(rule_id)

    prompt_sound = mission_rules[rule_id].get("prompt_sound")
    if prompt_sound:
        play_rule_sound(prompt_sound)

    print("Activated rule:", rule_id)


def deactivate_rule(rule_id):
    active_rules.discard(rule_id)
    state = rule_states.get(rule_id)
    if state:
        state["true_since"] = None
    print("Deactivated rule:", rule_id)


def process_rule_zone_action(action, target, sound_info=""):
    """Apply a silent rule-control zone action.

    Spatial rule-control markers only change whether a rule is active.
    Rule audio is configured inside the .rules.json file.
    """
    if action == "ActivateRule":
        activate_rule(target)

    elif action == "DeactivateRule":
        deactivate_rule(target)

    else:
        print("Unknown rule-zone action:", action)


def evaluate_active_rules():
    if not active_rules:
        return

    with telemetry_lock:
        telemetry = dict(telemetry_values)

    now = time.monotonic()

    for rule_id in list(active_rules):
        rule = mission_rules.get(rule_id)
        state = rule_states.get(rule_id)

        if not rule or not state:
            continue

        timeout = rule.get("timeout")
        activated_at = state.get("activated_at")

        if (
            timeout is not None
            and activated_at is not None
            and now - activated_at >= float(timeout)
        ):
            timeout_sound = rule.get("timeout_sound")
            if timeout_sound:
                play_rule_sound(timeout_sound)
            deactivate_rule(rule_id)
            continue

        condition_true = evaluate_condition(rule, telemetry)

        if not condition_true:
            state["true_since"] = None
            continue

        if state["true_since"] is None:
            state["true_since"] = now

        hold_for = float(rule.get("hold_for", 0))
        if now - state["true_since"] < hold_for:
            continue

        cooldown = float(rule.get("cooldown", 0))
        last_played = state.get("last_played")
        if last_played is not None and now - last_played < cooldown:
            continue

        if play_rule_sound(rule.get("success_sound")):
            state["last_played"] = now
            state["completed"] = True

            if rule.get("auto_deactivate", True):
                deactivate_rule(rule_id)
            elif rule.get("reset_after_play", True):
                state["true_since"] = None


devicelink_thread = threading.Thread(
    target=devicelink_poll_loop,
    daemon=True
)
devicelink_thread.start()

# Trigger Check Logic

NORMAL_TRIGGER_PATTERN = re.compile(
    r"^Selected:\s*(?P<selected>.*?),\s*"
    r"Type:\s*(?P<type>Normal|Repeatable),\s*"
    r"Radius:\s*(?P<radius>[^,]+),\s*"
    r"(?:MinAltFt:\s*(?P<min_alt>[^,]+),\s*"
    r"MaxAltFt:\s*(?P<max_alt>[^,]+),\s*)?"
    r"(?:Group:\s*(?P<group>[^,]*),\s*)?"
    r"Sound:\s*(?P<sound>.+)$",
    re.IGNORECASE
)

LOITER_TRIGGER_PATTERN = re.compile(
    r"^Selected:\s*(?P<selected>.*?),\s*"
    r"Type:\s*Loiter,\s*"
    r"Loiter:\s*(?P<loiter>[^,]+),\s*"
    r"Radius:\s*(?P<radius>[^,]+),\s*"
    r"(?:MinAltFt:\s*(?P<min_alt>[^,]+),\s*"
    r"MaxAltFt:\s*(?P<max_alt>[^,]+),\s*)?"
    r"(?:Group:\s*(?P<group>[^,]*),\s*)?"
    r"Sound:\s*(?P<sound>.+)$",
    re.IGNORECASE
)

ACTION_TRIGGER_PATTERN = re.compile(
    r"^Selected:\s*(?P<selected>.*?),\s*"
    r"Type:\s*(?P<type>ActivateRule|DeactivateRule),\s*"
    r"Target:\s*(?P<target>[^,]+),\s*"
    r"Radius:\s*(?P<radius>[^,]+),\s*"
    r"(?:MinAltFt:\s*(?P<min_alt>[^,]+),\s*"
    r"MaxAltFt:\s*(?P<max_alt>[^,]+),\s*)?"
    r"(?:Group:\s*(?P<group>[^,]*),\s*)?"
    r"Sound:\s*(?P<sound>.*)$",
    re.IGNORECASE
)

def disable_trigger_group(group_id, fired_trigger_key):
    """Disable every trigger sharing group_id for the current mission run."""
    group_id = group_id.strip()
    if not group_id:
        return

    disabled_trigger_groups.add(group_id)

    # Disable any group members whose runtime state has already been created.
    for key, member_state in trigger_states.items():
        if member_state.get("group") == group_id:
            member_state["armed"] = False
            member_state["loiter_start"] = None

    print(
        f"Trigger group '{group_id}' completed by {fired_trigger_key}. "
        "All triggers in the group are now disabled."
    )


def trigger_check(sim_x, sim_y, sim_z, mission_name):
    trig_path = get_trigger_path(mission_name)

    if trig_path is None:
        return

    # The .mis file is authoritative. This is cached, so the file is only
    # inspected again after either the .mis or .trig file changes.
    sync_registered_triggers_with_mission(mission_name)

    try:
        with open(
            trig_path,
            "r",
            encoding="utf-8",
            errors="replace"
        ) as trigger_file:

            for line in trigger_file:
                line = line.strip()

                if not line.startswith("Selected:"):
                    continue

                loiter_match = LOITER_TRIGGER_PATTERN.match(line)
                normal_match = NORMAL_TRIGGER_PATTERN.match(line)
                action_match = ACTION_TRIGGER_PATTERN.match(line)

                # -----------------------------------------
                # Read a rule activation/deactivation trigger
                # -----------------------------------------

                if action_match:
                    selected_str = action_match.group("selected").strip()
                    trigger_type = action_match.group("type").strip()
                    target_rule = action_match.group("target").strip()
                    radius_str = action_match.group("radius").strip()
                    sound_info = action_match.group("sound").strip()
                    min_alt_str = action_match.group("min_alt")
                    max_alt_str = action_match.group("max_alt")
                    trigger_group = (action_match.group("group") or "").strip()
                    loiter_seconds = None

                    try:
                        radius = float(radius_str) * 1000
                        min_alt_ft = float(min_alt_str) if min_alt_str is not None else float("-inf")
                        max_alt_ft = float(max_alt_str) if max_alt_str is not None else float("inf")
                    except ValueError:
                        print("Invalid rule-zone radius:", line)
                        continue

                # -----------------------------------------
                # Read a Loiter trigger
                # -----------------------------------------

                elif loiter_match:
                    selected_str = loiter_match.group("selected").strip()
                    trigger_type = "Loiter"
                    radius_str = loiter_match.group("radius").strip()
                    loiter_str = loiter_match.group("loiter").strip()
                    sound_info = loiter_match.group("sound").strip()
                    min_alt_str = loiter_match.group("min_alt")
                    max_alt_str = loiter_match.group("max_alt")
                    trigger_group = (loiter_match.group("group") or "").strip()

                    try:
                        radius = float(radius_str) * 1000
                        min_alt_ft = float(min_alt_str) if min_alt_str is not None else float("-inf")
                        max_alt_ft = float(max_alt_str) if max_alt_str is not None else float("inf")
                        loiter_seconds = float(loiter_str)

                    except ValueError:
                        print("Invalid Loiter trigger values:", line)
                        continue

                # -----------------------------------------
                # Read a Normal or Repeatable trigger
                # -----------------------------------------

                elif normal_match:
                    selected_str = normal_match.group("selected").strip()
                    trigger_type = normal_match.group("type").strip().title()
                    radius_str = normal_match.group("radius").strip()
                    sound_info = normal_match.group("sound").strip()
                    min_alt_str = normal_match.group("min_alt")
                    max_alt_str = normal_match.group("max_alt")
                    trigger_group = (normal_match.group("group") or "").strip()

                    try:
                        radius = float(radius_str) * 1000
                        min_alt_ft = float(min_alt_str) if min_alt_str is not None else float("-inf")
                        max_alt_ft = float(max_alt_str) if max_alt_str is not None else float("inf")

                    except ValueError:
                        print("Invalid trigger radius:", line)
                        continue

                    loiter_seconds = None

                else:
                    print("Bad trigger line format:", line)
                    continue

                # -----------------------------------------
                # Read trigger coordinates
                #
                # selected_str should look like:
                # 14_bld: 5000.00, 6000.00, 50.00
                # -----------------------------------------

                try:
                    object_name, coordinate_text = selected_str.split(":", 1)

                    coordinate_parts = coordinate_text.split(",")

                    if len(coordinate_parts) != 3:
                        raise ValueError(
                            "Trigger must contain exactly three coordinates."
                        )

                    trigger_x = float(coordinate_parts[0].strip())
                    trigger_y = float(coordinate_parts[1].strip())
                    trigger_z = float(coordinate_parts[2].strip())

                    matching_trigger = compare_trigger(
                        object_name,
                        trigger_x,
                        trigger_y,
                        trigger_z,
                        mission_name
                    )

                    if matching_trigger is None:
                        continue

                    # Always use the .mis object's current coordinates.
                    trigger_x, trigger_y, trigger_z = (
                        matching_trigger["coords"]
                    )

                    authoritative_type = matching_trigger["type"]
                    if trigger_type != authoritative_type:
                        print(
                            "Skipping trigger until its type-specific settings "
                            "are corrected in the editor:",
                            object_name,
                            f".trig={trigger_type}",
                            f".mis={authoritative_type}"
                        )
                        continue

                    object_name = matching_trigger["name"]
                    selected_str = matching_trigger["selected"]

                except ValueError as error:
                    print(
                        "Could not parse trigger coordinates:",
                        selected_str,
                        error
                    )
                    continue

                # -----------------------------------------
                # Give this exact trigger its own state
                # -----------------------------------------

                trigger_key = selected_str

                state = trigger_states.setdefault(
                    trigger_key,
                    {
                        "armed": True,
                        "loiter_start": None,
                        "inside": False,
                        "group": trigger_group
                    }
                )

                # Existing runtime state may have been created before the group
                # field was added or changed, so keep it synchronized.
                state["group"] = trigger_group

                # Horizontal distance only.
                #
                # Altitude is not included, so an aircraft only
                # needs to be inside the trigger's map radius.
                distance = math.sqrt(
                    (sim_x - trigger_x) ** 2
                    + (sim_y - trigger_y) ** 2
                )

                # The custom coordinate broadcaster supplies sim_z in metres.
                # Convert only the live aircraft altitude to feet. The trigger
                # object's stored Z coordinate is deliberately not used.
                sim_altitude_ft = sim_z * 3.28084
                inside_horizontal_radius = distance <= radius
                inside_altitude_range = (
                    min_alt_ft <= sim_altitude_ft <= max_alt_ft
                )
                inside_trigger = (
                    inside_horizontal_radius and inside_altitude_range
                )

                group_is_disabled = (
                    bool(trigger_group)
                    and trigger_group in disabled_trigger_groups
                )

                # A completed group blocks other trigger objects in that
                # group. Keep processing a zone that is already occupied only
                # long enough to reset its inside/outside edge state.
                if group_is_disabled and not state["inside"]:
                    state["armed"] = False
                    state["loiter_start"] = None
                    continue

                # =========================================
                # RULE ACTIVATION / DEACTIVATION ZONE
                # =========================================

                if trigger_type == "ActivateRule":
                    # Entering the activation zone enables the rule.
                    if inside_trigger and not state["inside"]:
                        state["inside"] = True
                        process_rule_zone_action(
                            "ActivateRule",
                            target_rule,
                            sound_info
                        )
                        disable_trigger_group(trigger_group, trigger_key)

                    # Leaving the activation zone only resets its entry edge.
                    # The rule remains active until it succeeds, times out, or
                    # a dedicated DeactivateRule marker disables it.
                    elif not inside_trigger and state["inside"]:
                        state["inside"] = False

                elif trigger_type == "DeactivateRule":
                    # A separate deactivation marker still works on entry.
                    if inside_trigger and not state["inside"]:
                        state["inside"] = True
                        process_rule_zone_action(
                            "DeactivateRule",
                            target_rule
                        )
                        disable_trigger_group(trigger_group, trigger_key)
                    elif not inside_trigger and state["inside"]:
                        state["inside"] = False

                # =========================================
                # NORMAL TRIGGER
                # =========================================

                elif trigger_type == "Normal":
                    if inside_trigger and state["armed"]:
                        print(
                            f"Entered Normal trigger {object_name}. "
                            f"Distance: {distance:.1f} metres"
                        )

                        if not pygame.mixer.music.get_busy():
                            try:
                                pygame.mixer.music.load(sound_info)
                                pygame.mixer.music.set_volume(
                                    slider.get() / 100
                                )
                                pygame.mixer.music.play()

                                print("Playing:", sound_info)

                                # Normal triggers permanently disarm.
                                state["armed"] = False
                                disable_trigger_group(trigger_group, trigger_key)

                            except Exception as error:
                                print(
                                    "Error playing Normal trigger sound:",
                                    error
                                )

                    # Leaving a Normal trigger does not re-arm it.
                    state["loiter_start"] = None

                # =========================================
                # REPEATABLE TRIGGER
                # =========================================

                elif trigger_type == "Repeatable":
                    if inside_trigger:
                        if state["armed"]:
                            print(
                                f"Entered Repeatable trigger {object_name}. "
                                f"Distance: {distance:.1f} metres"
                            )

                            if not pygame.mixer.music.get_busy():
                                try:
                                    pygame.mixer.music.load(sound_info)
                                    pygame.mixer.music.set_volume(
                                        slider.get() / 100
                                    )
                                    pygame.mixer.music.play()

                                    print("Playing:", sound_info)

                                    # Prevent repeated playback while the
                                    # aircraft remains inside the zone.
                                    state["armed"] = False
                                    disable_trigger_group(trigger_group, trigger_key)

                                except Exception as error:
                                    print(
                                        "Error playing Repeatable trigger sound:",
                                        error
                                    )

                    else:
                        # It becomes available again only after leaving.
                        state["armed"] = True
                        state["loiter_start"] = None

                # =========================================
                # LOITER TRIGGER
                # =========================================

                elif trigger_type == "Loiter":
                    if inside_trigger:
                        current_time = time.monotonic()

                        # Start this particular Loiter trigger's timer.
                        if state["loiter_start"] is None:
                            state["loiter_start"] = current_time

                            print(
                                f"Started Loiter trigger {object_name}: "
                                f"{loiter_seconds:.1f} seconds required"
                            )

                        elapsed = current_time - state["loiter_start"]
                        remaining = max(0.0, loiter_seconds - elapsed)

                        print(
                            f"Loiter {object_name}: "
                            f"{elapsed:.1f}/{loiter_seconds:.1f} seconds, "
                            f"{remaining:.1f} remaining"
                        )

                        if elapsed >= loiter_seconds and state["armed"]:
                            if not pygame.mixer.music.get_busy():
                                try:
                                    pygame.mixer.music.load(sound_info)
                                    pygame.mixer.music.set_volume(
                                        slider.get() / 100
                                    )
                                    pygame.mixer.music.play()

                                    print(
                                        f"Loiter completed for {object_name}. "
                                        f"Playing: {sound_info}"
                                    )

                                    # This Loiter object now stays completed.
                                    state["armed"] = False
                                    disable_trigger_group(trigger_group, trigger_key)

                                except Exception as error:
                                    print(
                                        "Error playing Loiter trigger sound:",
                                        error
                                    )

                    else:
                        # Leaving before completing the required time
                        # resets only this Loiter object's timer.
                        if (
                            state["loiter_start"] is not None
                            and state["armed"]
                        ):
                            print(
                                f"Left Loiter trigger {object_name} early. "
                                "Timer reset."
                            )

                        state["loiter_start"] = None

    except FileNotFoundError:
        print("Trigger file not found:", trig_path)

    except OSError as error:
        print("Could not read trigger file:", error)
                
            

    

monitor_thread = threading.Thread(
    target=watch_log,
    daemon=True
)
monitor_thread.start()

# Start coordinate listener
receive_coordinates()

usr_data()

# Start Tkinter GUI
root.mainloop()