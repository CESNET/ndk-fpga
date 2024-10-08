# File: ndk_xbuild.py
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
# Copyright: (C) 2024 CESNET, z.s.p.o.

"""
Contains script called "harp".
"""

import argparse
import tomli
import sys
import os
import logging
import pandas as pd

from colorama import Fore, Style
from pathlib import Path
from comp_settings.config_description import NdkXBuildTOML
from comp_settings.config_transform import NdkXBuildConfig
from build_adapters.questasim import NdkXBuildQuestaRunner


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def args_setup():
    parser = argparse.ArgumentParser()

    # Add general arguments to the top-level parser
    parser.add_argument(
        "-c",
        "--config_file",
        help="Path to ndk_xbuild TOML config file. Default is \'./harp.toml\'",
        required=False,
        default="./harp.toml",
        action="store")
    parser.add_argument("--gui", help="Launch tool with gui", action="store_true")
    parser.add_argument(
        "--dry",
        help="Run combination evaluation and store them into .md or .csv files",
        action="store",
        choices=[
            "md",
            "csv"])
    parser.add_argument(
        "--log-level",
        choices=[
            "DEBUG",
            "INFO",
            "WARNING",
            "ERROR",
            "CRITICAL"],
        help="Set logging level",
        required=False)
    parser.add_argument("--comb", nargs=1, metavar=("COMB_NAME"),
                        help="Evaluates combinations and prints the one specified")

    # Create subparsers for each command
    subparsers          = parser.add_subparsers(dest="command")
    subparsers.add_parser("synth")
    ver_parser          = subparsers.add_parser("ver")
    multiver_parser     = subparsers.add_parser("multiver")
    subparsers.add_parser("multisynth")

    # Add verification specific arguments to ver and multiver subparsers
    for subparser in [ver_parser, multiver_parser]:
        ver_args = subparser.add_argument_group("Verification specific arguments")
        ver_args.add_argument(
            "-r",
            "--run-comb",
            help="Load combination csv file and launch combination on given row.",
            nargs=2,
            metavar=("COMB_CSV", "COMB_INDEX"),
            action="store")
        ver_args.add_argument(
            "-f",
            "--failed-comb",
            help="Run first or specified failed combination from given csv.",
            nargs=2,
            metavar=("COMB_CSV", "COMB_INDEX"),
            action="store")

    return parser


def load_toml_config(
    path: Path,
):
    parsed_toml = None

    with open(path, "rb") as f:
        parsed_toml = tomli.load(f)

    return NdkXBuildTOML(**parsed_toml)


def get_top_level_fdo(
    parsed_toml: NdkXBuildTOML,
) -> Path:
    cwd = Path(os.getcwd())
    top_level_fdo_path = cwd / parsed_toml.build_system.ver_folder / parsed_toml.build_system.ver_fdo_file
    if not top_level_fdo_path.exists():
        raise FileNotFoundError(
            f"Could not find top level fdo file on path: {top_level_fdo_path.absolute().as_posix()}")

    return top_level_fdo_path


def synth():
    pass


def multisynth():
    pass


def ver(
    parsed_toml: NdkXBuildTOML,
    args,
    multiver,
):

    top_level_fdo = get_top_level_fdo(parsed_toml)
    config = NdkXBuildConfig(parsed_toml)
    runner = NdkXBuildQuestaRunner(
        config,
        top_level_fdo,
        args.gui,
        not multiver
    )
    runner.run()

    if not args.gui:
        a = runner.report()
        exit(0 if a else 42)


def dry_run(
    parsed_toml: NdkXBuildTOML,
    ftype: str,
):
    config = NdkXBuildConfig(parsed_toml)
    ver_combs: pd.DataFrame = pd.concat(
        [x.generics_df for x in config.ver_combinations] + [config.default_generics], ignore_index=True)
    synth_combs: pd.DataFrame = pd.concat(
        [x.generics_df for x in config.synth_combinations] + [config.default_generics], ignore_index=True)

    if ftype == "md":
        ver_combs.to_markdown("ver_combinations.md")
        synth_combs.to_markdown("synth_combinations.md")
    else:
        ver_combs.to_csv("ver_combinations.csv")
        synth_combs.to_csv("synth_combinations.csv")


def failed_comb(
    parsed_toml,
    args,
):
    cwd = Path.cwd()
    comb_csv, index = args.failed_comb
    csv_path = cwd / comb_csv
    failed_comb = pd.read_csv(csv_path)
    failed_comb.drop(columns=failed_comb.columns[0], axis=1, inplace=True)
    selected_comb = failed_comb.iloc[[index]]

    top_level_fdo = get_top_level_fdo(parsed_toml)
    config = NdkXBuildConfig(parsed_toml)

    # HACK Set selected combination as default and run default only
    config.default_generics = selected_comb
    runner = NdkXBuildQuestaRunner(
        config,
        top_level_fdo,
        args.gui,
        True
    )
    runner.run()

    if not args.gui:
        a = runner.report()
        exit(0 if a else 42)


def print_comb(
    parsed_toml: NdkXBuildTOML,
    args,
):
    config = NdkXBuildConfig(parsed_toml)
    for comb in config.ver_combinations:
        if comb.name == args.comb[0]:
            print(comb.generics_df)
            exit(0)

    print(Fore.RED + "Check combination name again, or...am I blind?" + Style.RESET_ALL)
    exit(1)


def main():
    parser = args_setup()
    args = parser.parse_args()

    if args.log_level:
        logging.basicConfig(level=args.log_level)

    toml_path = Path(args.config_file)
    parsed_toml = load_toml_config(toml_path)

    if args.comb:
        print_comb(parsed_toml, args)

    if args.dry:
        dry_run(parsed_toml, args.dry)
        return

    if args.failed_comb:
        failed_comb(parsed_toml, args)
        return

    if args.command in ["multiver", "ver"]:
        ver(parsed_toml, args, args.command == "multiver")
    else:
        raise NotImplementedError("Other commands are not supported. Yet...")

    # conf.debug_print()
    pass


if __name__ == "__main__":
    main()
