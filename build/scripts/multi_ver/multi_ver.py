# ver_run.py
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import argparse
import os
from os import system
from importlib.machinery import SourceFileLoader
from random import randint

FAIL = False


# RANDOMLY reduce number of combination to a certain percentage
def reduce_combinations(combinations, reduction_perc=100):
    if reduction_perc >= 100:
        return combinations

    items = len(combinations)
    new_items = items * reduction_perc // 100
    if new_items < 1:
        new_items = 1

    comb = list(combinations.keys())
    new_comb = dict()
    for i in range(new_items):
        new_item_key = comb.pop(randint(0, len(comb) - 1))
        new_comb[new_item_key] = combinations[new_item_key]

    return new_comb


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
    env = {}
    for i in setting.keys():
        if i == '__archgrp__':
            env['ARCHGRP'] = " ".join([f'{k}={v}' for k, v in setting[i].items()])
        elif i == '__core_params__':
            env['CORE_PARAMS'] = " ".join([f'{k}={v}' for k, v in setting[i].items()])
        else:
            #print(sed_str.format(i,setting[i],pkg_file))
            system(sed_str.format(i, setting[i], pkg_file))
    return env


# Run Modelsim with the current test_pkg file
def run_modelsim(fdo_file, test_name, manual=False, gui=False, coverage=False, env={}):
    global FAIL

    logfile_name = f"transcript_{test_name}"

    command  = f"do {fdo_file};"
    if coverage:
        command += f"coverage save -codeAll -testname {test_name} {test_name}.ucdb;"
    if not gui:
        command += "quit -f;"

    params = ""
    params += f" -logfile \"{logfile_name}\" "
    params += "" if gui else " -c "

    if coverage:
        if 'CORE_PARAMS' in env:
            env['CORE_PARAMS'] += " CODE_COVERAGE=true"
        else:
            env['CORE_PARAMS'] = " CODE_COVERAGE=true"

    for k, v in env.items():
        os.environ[k] = v

    cmd_vsim = f'vsim -do "{command}" {params}'
    cmd_grep = 'grep -E "(Verification finished successfully)|(VERIFICATION SUCCESS)"'
    if manual:
        system(cmd_vsim)
        result = system(f'{cmd_grep} {logfile_name} >/dev/null')
    else:
        result = system(f'{cmd_vsim} | {cmd_grep} >/dev/null')

    for k in env:
        del os.environ[k]
    return result

##########
# Parsing script arguments
##########


parser = argparse.ArgumentParser()

parser.add_argument("fdo_file", help="Name of verification \".fdo\" file to run in Modelsim")
parser.add_argument("test_pkg_file", help="Name of verification \".sv\" or \".vhd\" package file modify when applying settings")
parser.add_argument("settings_file", help="Name of verification settings \".py\" file containing \"SETTINGS\" dictionary variable")
parser.add_argument("-s", "--setting", nargs="+", help="Name of a specific setting or a sequence of settings from the \"SETTINGS\" dictionary to apply and run")
parser.add_argument("-d", "--dry-run", action="store_true", help="(Used together with '-s') Only sets the requested setting to test package without starting the verification")
parser.add_argument("-c", "--command-line", action="store_true", help="(Used together with '-s') Starts ModelSim with parameter '-c' for command line run")
parser.add_argument("-r", "--run-percantage", action="store", help="(Used without '-s') Randomly reduces number of performed combination to the given percantage ('100' for running all combinations)")
parser.add_argument("-n", "--test-name", action="store", help="(Used with '-s') select name of test. Some file will be saved with this suffix")
parser.add_argument("-p", "--prefix-name", action="store", help="this create prefix for test_name to prevent rewrite older files", default="")
parser.add_argument("--coverage", action="store_true", help="Generate and save code coverarge to <test_name>.ucdb file")

args = parser.parse_args()

# Detect package type
PKG_MOD_SED = """sed -i "s/\\\\(\\<parameter\\>\\s\\s*\\<{}\\W*\\\\)=..*;/\\\\1= {};/g" {}""" # SystemVerilog format
if len(args.test_pkg_file) > 4:
    if args.test_pkg_file[-4:] == ".vhd":
        PKG_MOD_SED = """sed -i "s/\\\\(\\<constant\\>\\s\\s*\\<{}\\W*:.*\\\\):=..*;/\\\\1:= {};/g" {}""" # VHDL format

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


if args.setting is None and args.test_name is None:
    ##########
    # Run all settings
    ##########

    for key in COMBINATIONS:
        comb = COMBINATIONS[key]
        SETTING = create_setting_from_combination(SETTINGS, comb)

        env = apply_setting(args.test_pkg_file, SETTING, PKG_MOD_SED)

        comb_name = " ".join(comb)
        print(f"Running combination: {key} ({comb_name})")
        result = run_modelsim(args.fdo_file, f'{test_name_prefix}{key}', coverage=args.coverage, env=env)
        if result == 0: # detect failure
            print(f"Run SUCCEEDED ({test_name_prefix}{key})")
        else:
            print(f"Run FAILED ({test_name_prefix}{key})")
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
    env = apply_setting(args.test_pkg_file, SETTING, PKG_MOD_SED)

    if (not args.dry_run):
        print("Running combination: " + " ".join(test_setings))
        result = run_modelsim(args.fdo_file, f'{test_name_prefix}{test_name}', True, (not args.command_line), coverage=args.coverage, env=env)
        if (result == 0): # detect failure
            print("Run SUCCEEDED (" + " ".join(test_setings) + ")")
        else:
            print("Run FAILED (" + " ".join(test_setings) + ")")
            FAIL = True

    print("Done")
    ##########

if (FAIL):
    exit(-1)
