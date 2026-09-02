#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import argparse
import os
from os import system
from importlib.machinery import SourceFileLoader
import shutil
import time
import os.path as op
import xml.etree.ElementTree as ET
from multi_ver_utils import reduce_combinations, create_setting_from_combination

FAIL = False

RESULTS_FILE = "results.xml"


def parse_results(results_file: str = RESULTS_FILE) -> dict:
    """Parse a cocotb JUnit XML results file.

    Returns a dict with keys: passed (bool), num_tests (int),
    num_failed (int), seed (str or None).

    A missing or empty results file is treated as a failure.
    """
    result = {"passed": False, "num_tests": 0, "num_failed": 0, "seed": None}

    if not op.exists(results_file) or op.getsize(results_file) == 0:
        return result

    try:
        tree = ET.parse(results_file)
    except ET.ParseError:
        return result

    for ts in tree.iter("testsuite"):
        for prop in ts.iter("property"):
            if prop.get("name") == "random_seed":
                result["seed"] = prop.get("value")

        for tc in ts.iter("testcase"):
            result["num_tests"] += 1
            for _ in tc.iter("failure"):
                result["num_failed"] += 1
                break  # count at most one failure per testcase
            else:
                for _ in tc.iter("error"):
                    result["num_failed"] += 1
                    break  # count at most one error per testcase

    result["passed"] = result["num_tests"] > 0 and result["num_failed"] == 0
    return result


def find_venv() -> str | None:
    for root, dirs, files in os.walk("."):
        for dir in dirs:
            if op.isfile(op.join(dir, "bin", "activate")):
                return dir

    return None


def run_modelsim(settings: dict, test_name: str, venv: str | None = None, gui=False, cocotb_testcase: str | None = None):
    command = ""

    if venv is not None:
        command += f"source {venv}/bin/activate\n"

    sim_flags = f"-logfile \"{test_name}\""
    if not gui:
        sim_flags = f"{sim_flags} -c -do quit"

    command += f"make TARGET=cocotb SIM_FLAGS=\"{sim_flags}\""

    if cocotb_testcase is not None:
        command += f" COCOTB_TESTCASE='{cocotb_testcase}'"

    if len(settings) > 0:
        command += " GENERICS=\""

        for name, value in settings.items():
            command += f"-g{name}={value} "

        command += "\""

    system(command)

    return parse_results()


def backup_results(test_name: str):
    """Copy results.xml to results_{test_name}.xml for archival."""
    if op.exists(RESULTS_FILE):
        shutil.copy2(RESULTS_FILE, f"results_{test_name}.xml")


def print_summary(results_summary: list):
    """Print a summary table of all combination results.

    Each entry in results_summary is a tuple:
        (combination_name, result_dict, elapsed_minutes)
    """
    if not results_summary:
        return

    # Determine column widths
    name_width = max(len(name) for name, _, _ in results_summary)
    name_width = max(name_width, len("COMBINATION"))

    header_fmt = f" {{:<3}}  {{:<{name_width}}}  {{:<6}}  {{:<5}}  {{:<10}}  {{}}"
    row_fmt = f" {{:<3}}  {{:<{name_width}}}  {{:<6}}  {{:<5}}  {{:<10}}  {{}}"

    total_width = 3 + 2 + name_width + 2 + 6 + 2 + 5 + 2 + 10 + 2 + 12 + 2
    sep = "=" * total_width

    print(f"\n{sep}")
    print(header_fmt.format("#", "COMBINATION", "STATUS", "TESTS", "TIME (min)", "SEED"))
    print(sep)

    num_passed = 0
    num_failed = 0

    for idx, (name, result, elapsed) in enumerate(results_summary):
        status = "PASS" if result["passed"] else "FAIL"
        tests = result["num_tests"]
        seed = result["seed"] if result["seed"] is not None else "N/A"

        if result["passed"]:
            num_passed += 1
        else:
            num_failed += 1

        print(row_fmt.format(idx, name, status, tests, f"{elapsed:.2f}", seed))

    total = num_passed + num_failed
    print(sep)
    print(f" TOTAL: {total} | PASSED: {num_passed} | FAILED: {num_failed}")
    print(f"{sep}\n")

##########
# Parsing script arguments
##########


parser = argparse.ArgumentParser()

parser.add_argument("settings_file", help="Name of verification settings \".py\" file containing \"SETTINGS\" dictionary variable")
parser.add_argument("-s", "--setting", nargs="+", help="Name of a specific setting or a sequence of settings from the \"SETTINGS\" dictionary to apply and run")
parser.add_argument("-d", "--dry-run", action="store_true", help="(Used together with '-s') Only sets the requested setting to test package without starting the verification")
parser.add_argument("-c", "--command-line", action="store_true", help="(Used together with '-s') Starts ModelSim with parameter '-c' for command line run")
parser.add_argument("-r", "--run-percantage", action="store", help="(Used without '-s') Randomly reduces number of performed combination to the given percantage ('100' for running all combinations)")
parser.add_argument("-n", "--test-name", action="store", help="(Used with '-s') select name of test. Some file will be saved with this suffix")
parser.add_argument("-p", "--prefix-name", action="store", help="this create prefix for test_name to prevent rewrite older files", default="")
parser.add_argument("-t", "--cocotb-testcase", action="store", help="Name of a cocotb testcase to run (passed as COCOTB_TESTCASE)")

args = parser.parse_args()

##########

##########
# Import Settings
##########

# import using relative path from execution directory
SETTINGS = SourceFileLoader(args.settings_file, "./" + args.settings_file).load_module().SETTINGS

if "default" not in SETTINGS.keys():
    print("ERROR: The settings file \"{}\" does not contain the obligatory \"default\" setting!".format(args.settings_file))
    exit(-2)

SETTING = {}

##########

##########
# Define settings combinations
##########

COMBINATIONS = dict()

if "_combinations_" in SETTINGS.keys():
    # User defined combinations
    if type(SETTINGS["_combinations_"]) is dict:
        COMBINATIONS = SETTINGS["_combinations_"]
    if type(SETTINGS["_combinations_"]) is tuple:
        for it, comb in enumerate(SETTINGS["_combinations_"]):
            COMBINATIONS[f"test_name_{it}"] = comb

    del SETTINGS["_combinations_"]

else:
    # Default combinations
    for key in SETTINGS.keys():
        COMBINATIONS[key] = (key, )

if args.run_percantage:
    # Randomly reduce number of combinations based on command argument
    COMBINATIONS = reduce_combinations(COMBINATIONS, int(args.run_percantage))
    del SETTINGS["_combinations_run_percentage_"]
elif "_combinations_run_percentage_" in SETTINGS.keys():
    # Randomly reduce number of combinations based on SETTINGS
    COMBINATIONS = reduce_combinations(COMBINATIONS, SETTINGS["_combinations_run_percentage_"])
    del SETTINGS["_combinations_run_percentage_"]

#print(COMBINATIONS)

##########

#Print current directory where verification is running
print(os.getcwd())

#Set text_name_prefix and REPLACE SPACE WITH UNDERSCORE.
test_name_prefix = ""
if args.prefix_name is not None and args.prefix_name != "":
    test_name_prefix = args.prefix_name.replace(" ", "_") + "_"

if (op.isfile("pyproject.toml")):
    system("make cocotb-venv")

venv = find_venv()

if args.setting is None and args.test_name is None:
    ##########
    # Run all settings
    ##########

    results_summary = []

    for key in COMBINATIONS:
        comb = COMBINATIONS[key]
        SETTING = create_setting_from_combination(SETTINGS, comb)

        comb_name = " ".join(comb)
        print(f"Running combination: {key} ({comb_name})")
        if (not args.dry_run):
            vsim_time_start = time.time()
            result = run_modelsim(SETTING, test_name=f"{test_name_prefix}{key}", venv=venv, cocotb_testcase=args.cocotb_testcase)
            vsim_time_stop = time.time()
            time_vsim_consumption = (vsim_time_stop - vsim_time_start)/60

            backup_results(f"{test_name_prefix}{key}")
            results_summary.append((f"{test_name_prefix}{key}", result, time_vsim_consumption))

            if result["passed"]:
                print(f"Run SUCCEEDED ({test_name_prefix}{key})\n\ttime consumption: {time_vsim_consumption:.2f} min")
            else:
                print(f"Run FAILED ({test_name_prefix}{key})\n\ttime consumption: {time_vsim_consumption:.2f} min")
                FAIL = True

    if not args.dry_run:
        print_summary(results_summary)
    ##########
else:
    ##########
    # Run selected setting
    ##########

    if args.test_name is not None:
        test_name = args.test_name
        test_setings = COMBINATIONS[args.test_name]
    if args.setting is not None:
        test_name = "test_setings"
        test_setings = args.setting

    SETTING = create_setting_from_combination(SETTINGS, test_setings)

    print("Running combination: " + " ".join(test_setings))
    if (not args.dry_run):
        result = run_modelsim(SETTING, test_name=f"{test_name_prefix}{test_name}", venv=venv, gui=(not args.command_line), cocotb_testcase=args.cocotb_testcase)
        if result["passed"]:
            print("Run SUCCEEDED (" + " ".join(test_setings) + ")")
        else:
            print("Run FAILED (" + " ".join(test_setings) + ")")
            FAIL = True

    print("Done")
    ##########

if (FAIL):
    exit(-1)
