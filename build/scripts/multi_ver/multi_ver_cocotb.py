# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import argparse
import os
from os import system
from importlib.machinery import SourceFileLoader
from random import randint
import time
import os.path as op
from multi_ver_utils import reduce_combinations, create_setting_from_combination

FAIL = False

def junit(testResults: str, allowEmptyResults: bool = False) -> bool:
    if not op.exists(testResults):
        if allowEmptyResults:
            return True
        else:
            return False

    if op.getsize(testResults) == 0:
        if allowEmptyResults:
            return True
        else:
            return False

    results_file = open(testResults, "r")
    results = results_file.read()
    results_file.close()

    return False if "failure" in results else True


def find_venv() -> str | None:
    for root, dirs, files in os.walk("."):
        for dir in dirs:
            if op.isfile(op.join(dir, "bin", "activate")):
                return dir

    return None

def run_modelsim(settings: dict, venv: str | None = None, gui=False):
    command = ""

    if venv is not None:
        command += f"source {venv}/bin/activate\n"

    if not gui:
        sim_flags = "SIM_FLAGS=\"-c -do quit\""
    else:
        sim_flags = ""

    command += f"make TARGET=cocotb {sim_flags}"

    if len(settings) > 0:
        command += " GENERICS=\""

        for name, value in settings.items():
            command += f"-g{name}={value} "

        command += "\""

    system(command)

    #process = sp.Popen('grep -i "FAIL=0" transcript', shell=True, stdout=sp.PIPE, stderr=sp.PIPE)
    #stdout, stderr = process.communicate()

    return junit(testResults="results.xml", allowEmptyResults=True)

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

if (op.isfile("prepare.sh")):
    system("./prepare.sh")

venv = find_venv()

if args.setting is None and args.test_name is None:
    ##########
    # Run all settings
    ##########

    for key in COMBINATIONS:
        comb = COMBINATIONS[key]
        SETTING = create_setting_from_combination(SETTINGS, comb)

        comb_name = " ".join(comb)
        print(f"Running combination: {key} ({comb_name})")
        if (not args.dry_run):
            vsim_time_start = time.time()
            result = run_modelsim(SETTING, venv=venv)
            vsim_time_stop = time.time()
            time_vsim_consumption = (vsim_time_stop - vsim_time_start)/60
            if result: # detect failure
                print(f"Run SUCCEEDED ({test_name_prefix}{key})\n\ttime consumption: {time_vsim_consumption:.2f} min")
            else:
                print(f"Run FAILED ({test_name_prefix}{key})\n\ttime consumption: {time_vsim_consumption:.2f} min")
                FAIL = True

        # backup transcript
        # system("cp transcript transcript_"+"_".join(c))
        # backup test_pkg
        # system("cp {} {}_".format(args.test_pkg_file,args.test_pkg_file)+"_".join(c))
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
        result = run_modelsim(SETTING, venv=venv, gui=(not args.command_line))
        if result: # detect failure
            print("Run SUCCEEDED (" + " ".join(test_setings) + ")")
        else:
            print("Run FAILED (" + " ".join(test_setings) + ")")
            FAIL = True

    print("Done")
    ##########

if (FAIL):
    exit(-1)
