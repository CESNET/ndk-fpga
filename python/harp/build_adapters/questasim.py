# File: questasim.py
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
# Copyright: (C) 2024 CESNET, z.s.p.o.

"""
QuestaSim and ModelSim build adapter and runner. Creates interface
between NdkXBuild script and QuestaSim.
"""


import pandas as pd
import logging
import os
import numpy as np
import re
import random
import cowsay

from colorama import Fore, Style
from typing import Union, List
from comp_settings.config_transform import NdkXBuildConfig
from pathlib import Path

from .build_adapter import NdkXBuildAdapter, NdkXBuildRunner

_global_logger = logging.getLogger("BuildAdapter(QuestaSim)")


class NdkXBuildQuestasimAdapter(NdkXBuildAdapter):
    VER_SUCCESS_REGEX = re.compile(
        r'(Verification finished successfully|VERIFICATION SUCCESS)',
        re.IGNORECASE)
    VER_SV_SEED_REGEX = r'Sv_Seed\s*=\s*(\d+)'

    TMP_FOLDER_NAME = "tmp"
    GENERICS_FILE_NAME = "generics.fdo"

    def __init__(
        self,
        fdo_file_path: Path,
    ) -> None:
        self.fdo_file_path: Path = fdo_file_path
        self.curr_transcript_path = None
        self.vsim_succ = True

    def _value_formatter(
        self,
        value: Union[int, bool, str, List[Union[int, bool, str]]],
    ) -> str:
        if isinstance(value, np.bool):
            return f"{value}"
        elif isinstance(value, str):
            return value
        elif isinstance(value, np.int64):
            return f"{value}"
        else:
            print(type(value))
            raise NotImplementedError("Generics of type list are not supported yet!")

    def run_set_generics(
        self,
        generics: pd.Series,
    ):
        fdo_folder = self.fdo_file_path.parent
        tmp_folder = fdo_folder / self.TMP_FOLDER_NAME
        tmp_folder.mkdir(parents=True, exist_ok=True)

        generic_fdo = tmp_folder / self.GENERICS_FILE_NAME
        self.generics = generics

        with open(generic_fdo, "w") as f:
            for generic in generics.keys():
                value = generics[generic]
                f.write(f"set SIM_GENERICS({generic}) \"{self._value_formatter(value)}\"\n")
            f.write("\n")

    def run_tool(
        self,
        transcript_suffix: str,
        gui=False,
        print_output=False,
    ):
        transcript_name = f"transcript_{transcript_suffix}"
        self.curr_transcript_path = self.fdo_file_path.parent / transcript_name

        quit_cmd = "quit -f;" if not gui else ""
        vsim_gui_cmd = "-c" if not gui else ""
        dev_null = "> /dev/null" if not print_output else ""

        vsim_do_command = f"do {self.fdo_file_path.absolute().as_posix()};{quit_cmd}"
        logfile_param = f"-logfile \"{transcript_name}\""
        vsim_cmd = f"cd {self.fdo_file_path.parent}; vsim -do \"{vsim_do_command}\" {logfile_param} {vsim_gui_cmd} {dev_null}"

        _global_logger.debug(f"Running command:\n{vsim_cmd}")
        ret_code = os.system(vsim_cmd)
        self.vsim_succ = ret_code == 0
        if ret_code != 0:
            _global_logger.critical("QuestaSim run into an error!")
            raise ChildProcessError("QuestaSim run into an error!")

    def run_report(self) -> bool:
        if self.vsim_succ:
            return self._parse_transcript()
        else:
            sv_seed_series = pd.Series(["QUESTA FAILED"], index=["SV_SEED"])
            self.generics = self.generics.append(sv_seed_series)
            return False

    def _parse_transcript(self) -> bool:
        with open(self.curr_transcript_path, "r") as f:
            content = f.read()
            success = self.VER_SUCCESS_REGEX.search(content)

            if not success:
                sv_seed_reg = re.search(self.VER_SV_SEED_REGEX, content)
                sv_seed = "DONT_KNOW"
                if sv_seed_reg:
                    sv_seed = sv_seed_reg.group(1)
                else:
                    _global_logger.error("Could not find sv_seed value!")
                    success = False

                sv_seed_series = pd.Series([sv_seed], index=["SV_SEED"])
                self.generics = pd.concat([self.generics, sv_seed_series])

            return success


class NdkXBuildQuestaRunner(NdkXBuildRunner):
    COMB_SUCC_STR = Fore.GREEN + "SUCCESS" + Style.RESET_ALL
    COMB_FAIL_STR = Fore.RED + "FAIL" + Style.RESET_ALL

    VER_FAILED_MESSAGES = [
        "Oops! Your RTL code just stumbled and fell flat on its face. Maybe it needs coding lessons?",
        "Houston, we have a problem. Your RTL component seems to be speaking in riddles. Care to translate?",
        "Congratulations! You've discovered a new way to confuse your RTL component. Impressive... but not quite what we're looking for.",
        "Alert: RTL malfunction detected. Cause: Code that resembles a bowl of digital spaghetti.",
        "Your RTL component just threw a tantrum. It refuses to cooperate until you fix that code.",
        "Beep boop! RTL does not compute. Have you considered a career in abstract art instead?",
        "Warning: RTL verification system has encountered an unexpected laugh track. Please rewrite and try again.",
        "Plot twist! Your RTL code decided to go rogue. Maybe try asking it nicely to behave?",
        "Ouch! Your RTL component just face-palmed itself. It's clearly embarrassed by your code.",
        "Achievement unlocked: 'RTL Confusion Master'! Now, how about we aim for 'RTL Verification Success' instead?"]

    VER_SUCCESS_MESSAGES = [
        "Well, well, well... Your RTL code is surprisingly stubborn. Challenge accepted!",
        "Hmph. Your RTL component refuses to crack. Are you sure you didn't accidentally create skynet?",
        "Congratulations, your code is annoyingly resilient. Time to unleash my secret weapon: more coffee!",
        "Your RTL laughs in the face of my tests. I'm not mad, I'm just... impressed. And a little mad.",
        "Alert: Verification engineer's ego slightly bruised. RTL code remains irritatingly intact.",
        "Is your RTL made of adamantium? Because my tests just bounced right off!",
        "Warning: Unbreakable code detected. Preparing to question my entire career choice.",
        "Plot twist! Your RTL is tougher than a Nokia 3310. What dark magic is this?",
        "Bravo! Your code just earned the 'Verification Engineer's Nightmare' badge. Wear it proudly.",
        "Achievement unlocked: 'The Unbreakable'. Now excuse me while I go sulk in the corner."]

    def __init__(
        self,
        config: NdkXBuildConfig,
        top_level_fdo: Path,
        gui: bool,
        default_only: bool = False,
    ) -> None:
        super().__init__(config)
        self.build_adapter: NdkXBuildQuestasimAdapter = NdkXBuildQuestasimAdapter(top_level_fdo)
        self.gui = gui
        self.run_default = default_only
        self.failed_comb = pd.DataFrame(
            columns=list(
                self.config.ver_combinations[0].generics_df.columns) +
            ["SV_SEED"])

    def _run_comb(
        self,
        comb,
        default=False,
        default_only=False
    ):
        comb_name = comb.name if not default else "default"
        comb_df = comb.generics_df if not default else comb
        gui = self.gui if default_only else False

        internal_comb_count = len(comb_df.index)
        failed_comb_count = 0
        print(f"Running combinations from group {comb_name}...")
        for i in range(internal_comb_count):
            # Run verification
            self.build_adapter.run_set_generics(comb_df.iloc[i])
            transcript_suffix = f"{comb_name}{i}"
            self.build_adapter.run_tool(transcript_suffix=transcript_suffix, gui=gui)
            comb_part_succ = self.build_adapter.run_report()

            if not comb_part_succ:
                self.failed_comb = pd.concat(
                    [self.failed_comb, self.build_adapter.generics.to_frame().T], ignore_index=True)
                failed_comb_count += 1

            # Print partial combination success
            comb_result_str = self.COMB_SUCC_STR if comb_part_succ else self.COMB_FAIL_STR
            print(f"    combination {i}: {comb_result_str}")

        return internal_comb_count, failed_comb_count

    def _run_multiver(self) -> bool:
        self._run_comb(self.config.default_generics, default=True)

        for comb in self.config.ver_combinations:
            internal_comb_count, failed_comb_count = self._run_comb(comb)
            # Report whole combination group
            comb_result_str = self.COMB_SUCC_STR if failed_comb_count == 0 else self.COMB_FAIL_STR
            print(
                f"Combinations group {comb.name}: {comb_result_str} # {internal_comb_count - failed_comb_count} PASSED | {failed_comb_count} FAILED")

    def _run_ver(self):
        self._run_comb(self.config.default_generics, default=True, default_only=True)

    def _run_specified_comb_from_csv(self):
        pass

    def run(self):
        if not self.run_default:
            self._run_multiver()
        else:
            self._run_ver()

    def report(self) -> bool:
        # Report whole multiver status
        failed_comb_total = len(self.failed_comb.index)
        multiver_success = failed_comb_total == 0

        character = random.choice(list(cowsay.CHARS.keys()))
        if multiver_success:
            message = random.choice(self.VER_SUCCESS_MESSAGES)
            message = cowsay.get_output_string(
                character, Fore.GREEN + "SUCCESS! " + Style.RESET_ALL + message)
            print(message)
            return True
        else:
            csv_name = "failed_combinations.csv"
            self.failed_comb.to_csv(csv_name, sep=",", encoding="utf-8")
            # Message
            message = random.choice(self.VER_FAILED_MESSAGES)
            message = cowsay.get_output_string(
                character, Fore.RED + "FAIL! " + Style.RESET_ALL + message)
            print(message)
            return False

    # def report_comb(self) -> bool:
    #     failed_comb_count = len(self.failed_combinations.index)
    #     character = random.choice(list(cowsay.CHARS.keys()))

    #     if failed_comb_count == 0:
    #         message = random.choice(self.VER_SUCCESS_MESSAGES)
    #         message = cowsay.get_output_string(character, Fore.GREEN + "SUCCESS! " + Style.RESET_ALL + message)
    #         print(message)
    #         return True
    #     else:
    #         csv_name = f"failed_comb_{self.combination.name}.csv"
    #         self.failed_combinations.to_csv(csv_name, sep=",", encoding="utf-8")
    #         # Message
    #         message = random.choice(self.VER_FAILED_MESSAGES)
    #         message = cowsay.get_output_string(character, Fore.RED + "FAIL! " + Style.RESET_ALL + message)
    #         print(message)
    #         return False
