# multi_synth.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import argparse
from os import system
from importlib.machinery import SourceFileLoader

FAIL = False


# Modify setting variable
def create_setting_from_combination(settings, combination):
    global FAIL
    s = settings["default"].copy()
    for c in combination:
        if c not in settings.keys():
            print("ERROR: Combination \"{}\" contains unknown setting name \"{}\"!".format(combination, c))
            FAIL = True
            continue
        for i in settings[c].keys(): # load modified values
            if i not in s.keys():
                print("ERROR: Parameter \"{}\" is present in setting \"{}\" but not in setting \"default\". This might cause unexpected behaviour in the following runs!".format(i, c))
                FAIL = True
            s[i] = settings[c][i]
    return s


# Modify package file according to setting
def apply_setting(pkg_file, setting, sed_str):
    for i in setting.keys():
        #print(sed_str.format(i,setting[i],pkg_file))
        system(sed_str.format(i, setting[i], pkg_file))


# Run Modelsim with the current test_pkg file
def run_synthesis(makefile_path, implement=False, quartus=False):
    i = "IMPLEMENT=0 " if implement is False else "IMPLEMENT=1 "
    q = "" if not quartus else "quartus "
    system("make clean -C " + makefile_path)
    result = system(i + "make " + q + "-C " + makefile_path)
    return result

##########
# Parsing script arguments
##########


parser = argparse.ArgumentParser()

parser.add_argument("makefile", help="Name of Makefile for running synthesis")
parser.add_argument("entity_file", help="Name of entity \".vhd\" file to modify when applying settings")
parser.add_argument("settings_file", help="Name of verification settings \".py\" file containing \"SETTINGS\" dictionary variable")
parser.add_argument("-s", "--setting", nargs="+", help="Name of a specific setting or a sequence of settings from the \"SETTINGS\" dictionary to apply and run")
parser.add_argument("-v", "--vivado", action="store_true", help="Run Vivado (settings file should contain combination called \"vivado\" for the correct DEVICE generic if needed)")
parser.add_argument("-q", "--quartus", action="store_true", help="Run Quartus (settings file should contain combination called \"quartus\" for the correct DEVICE generic if needed)")
parser.add_argument("-d", "--dry-run", action="store_true", help="(Used together with '-s') Only sets the requested setting to entity file without starting the synthesis")
parser.add_argument("-i", "--implement", action="store_true", help="Run implementation, not just synthesis")
parser.add_argument("--save-whole-project", action="store_true", help="Create backup of an entire project after each run (not just timing and resources report)")

args = parser.parse_args()

if not args.vivado and not args.quartus:
    print("ERROR: Neither '-v'/'--vivado' nor '-q'/'--quartus' option was specified. Select at least one of them to run.")
    exit(-4)

# Create SED cammand for VHDL Entity default generics setting
PKG_MOD_SED = "sed -i \"s/\\(^\\s*\\<{}\\>\\s\\s*\\):\\(\\s\\s*\\<[^:;]*\\>\\)[^;]*\\(;\\?\\)/\\1:\\2 := {}\\3/g\" {}"

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

COMBINATIONS = ()

if "_combinations_" in SETTINGS.keys():
    # User defined combinations
    COMBINATIONS = SETTINGS["_combinations_"]
    del SETTINGS["_combinations_"]
else:
    # Default combinations
    COMBINATIONS = tuple([(x,) for x in SETTINGS.keys()])
#print(COMBINATIONS)

##########
# Get path to the directory of the given Makefile
if "/" in args.makefile:
    makefile_path = "/".join(args.makefile.split("/")[:-1])
else:
    makefile_path = "."

if args.setting is None:
    ##########
    # Run all settings
    ##########

    for c0 in COMBINATIONS:
        # Clean all previous results from the synth directory
        system("git clean -df " + makefile_path)

        # Run Synthesis'
        if args.quartus:
            c = list(c0) + ["quartus"]
            SETTING = create_setting_from_combination(SETTINGS, c)

            apply_setting(args.entity_file, SETTING, PKG_MOD_SED)

            print("Running combination: " + " ".join(c) + " in Quartus")
            result = run_synthesis(makefile_path, args.implement, True)
            if result != 0: # detect failure
                print("Run FAILED (" + " ".join(c) + ")")
                FAIL = True
        if args.vivado:
            c = list(c0) + ["vivado"]
            SETTING = create_setting_from_combination(SETTINGS, c)

            apply_setting(args.entity_file, SETTING, PKG_MOD_SED)

            print("Running combination: " + " ".join(c) + " in Vivado")
            result = run_synthesis(makefile_path, args.implement, False)
            if result != 0: # detect failure
                print("Run FAILED (" + " ".join(c) + ")")
                FAIL = True

        # Create directory to save run results
        res_dir_name = makefile_path + "/../project_" + "_".join(c0)
        system("rm -rf " + res_dir_name)
        system("mkdir " + res_dir_name)

        if args.quartus:
            # backup Quartus timing and resouces reports
            syn_util = makefile_path + "/*.syn.rpt"
            imp_util = makefile_path + "/*.fit.rpt"
            imp_time = makefile_path + "/*.sta.rpt"
            system("cp -rf " + syn_util + " " + res_dir_name + "/")
            if args.implement:
                system("cp -rf " + imp_util + " " + res_dir_name + "/")
                system("cp -rf " + imp_time + " " + res_dir_name + "/")
        if args.vivado:
            # backup Vivado timing and resouces reports
            runs_dir = makefile_path + "/*.runs"
            syn      = runs_dir + "/synth_1"
            imp      = runs_dir + "/impl_1"
            syn_util = syn + "/*_utilization_synth.rpt"
            syn_time = makefile_path + "/*_synth.tim"
            imp_util = imp + "/*_utilization_placed.rpt"
            imp_time = imp + "/*_timing_summary_routed.rpt"
            system("cp -rf " + syn_util + " " + res_dir_name + "/")
            system("cp -rf " + syn_time + " " + res_dir_name + "/")
            if args.implement:
                system("cp -rf " + imp_util + " " + res_dir_name + "/")
                system("cp -rf " + imp_time + " " + res_dir_name + "/")
        if args.save_whole_project:
            # backup whole project
            system("cp -rf " + makefile_path + "/* " + res_dir_name + "/")

    ##########
else:
    ##########
    # Run selected setting
    ##########

    if args.quartus:
        c = args.setting + ["quartus"]
        SETTING = create_setting_from_combination(SETTINGS, c)

        apply_setting(args.entity_file, SETTING, PKG_MOD_SED)

        if not args.dry_run:
            print("Running combination: " + " ".join(c) + " in Quartus")
            result = run_synthesis(makefile_path, args.implement, True)
            if result != 0: # detect failure
                print("Run FAILED (" + " ".join(c) + ")")
                FAIL = True
    if args.vivado:
        c = args.setting + ["vivado"]
        SETTING = create_setting_from_combination(SETTINGS, c)

        apply_setting(args.entity_file, SETTING, PKG_MOD_SED)

        if not args.dry_run:
            print("Running combination: " + " ".join(c) + " in Vivado")
            result = run_synthesis(makefile_path, args.implement, False)
            if result != 0: # detect failure
                print("Run FAILED (" + " ".join(c) + ")")
                FAIL = True

    print("Done")
    ##########

if FAIL:
    exit(-1)
