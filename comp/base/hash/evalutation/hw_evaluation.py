# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import os
import re
import glob
import json
import matplotlib.pyplot as plt
from collections import defaultdict, Counter
from typing import Any, Optional, Callable
from itertools import product
from dataclasses import dataclass


@dataclass
class ResourceAnalyzerGraphConfig:
    """
    Dataclass for configuring the output graphs of ResourceAnalyzer.
    """
    # name of the generic that will be considered as the main input.
    input_length_key   : str                = ""
    # label of the main input in graphs.
    input_length_label : str                = ""
    # name of the generic based on which multiple plot will be generated.
    plot_series_key    : Optional[str]      = None
    # function returning the labels of the individual plots based on the value of plot_series_key generic.
    plot_series_label  : Optional[Callable] = None


class ResourceAnalyzer:
    """
    Component for analyzing hardware properties of VHDL components.

    Measures resource consumption and maximum possible frequency based on synthesis.
    Also measures latency based on pyuvm (or cocotb) simulation.

    Generates report in the json format and graphs.
    """

    def __init__(
        self,
        common_generics: dict[str, list[Any]],                     # generics common for all the analysed components.
        graph_config: Optional[ResourceAnalyzerGraphConfig] = None # configuration object of the graphs.
    ):
        self._base_path            : str                         = os.getcwd()
        self._generic_combinations : list                        = self._generate_combinations(common_generics)
        self._graph_config         : ResourceAnalyzerGraphConfig = graph_config

    def analyze(
        self,
        name            : str,
        generics        : dict[str, Any],
        synth_path      : str  = "./",
        ver_path        : str  = "./",
        ver_name        : str  = None,
        save_path       : str  = "./",
        synthesis       : bool = True,
        latency         : bool = True,
        generate_report : bool = True,
        generate_graphs : bool = True
    ):
        """
        Call this method to start the analysis.

        Args:
            name(str)                : name of the component
            generics(dict[str, Any]) : set generics of the specific component
            synth_path(str)          : path to the synthesis Makefile
            ver_path(str)            : path to the functional pyuvm/cocotb verification
            ver_name(str)            : name of the component in the realm of the verification (may differ from the actual name of the component).
                                       if not set, name of the component is used for verification too.
            save_path(str)           : path to where the results will be saved (in a folder with the same name as the component)
            synthesis(bool)          : wheter synthesis should be performed
            latency(bool)            : wheter testing of latency should be performed
            generate_report(bool)    : wheter reports shall be generater
            generate_graphs(bool)    : wheter graphs shall be generated

        """

        if ver_name is None:
            ver_name = name

        synthesis_report : dict = dict()
        latency_report   : dict = dict()

        # collecting report from synthesis
        if synthesis:
            synthesis_report = self._get_synthesis_report(name, generics, synth_path)

        # collecting latency report
        if latency:
            latency_report = self._get_latency_report(ver_name, generics, ver_path)

        # joining both reports together
        report: dict = {
            key: {**synthesis_report.get(key, {}), **latency_report.get(key, {})}
            for key in set(synthesis_report) | set(latency_report)
        }

        # generating final report in json
        if generate_report:
            self._save_report_to_json(name, report, save_path)

        # generating graphs from the report
        if generate_graphs:
            self._generate_graphs(name, report, save_path)

    def _generate_combinations(self, generics: dict[str, list[Any]]) -> list[tuple[tuple[str, Any]]]:
        """
        Creates combinations of common generics.

        Args:
            generics(dict[str, list[Any]]): individual generic settings of the component.

        Returns:
            a list of tuples, where every tuple represents a combination, and each combination
            consists of tuples representing a configuration of a generic, which consists of the name
            of the generic as a string and it's value, which can be of any type.
        """

        names  : list[str] = list(generics.keys())
        values : list[Any] = list(generics.values())

        return [tuple(zip(names, combination)) for combination in product(*values)]

    def _get_synthesis_report(self, name: str, generics: dict[str, Any], synth_path: str) -> dict[Any, dict[str, int | float]]:
        """
        Runs synthesis for all combination of common generics and returs a report.

        Args:
            name(str)                : name of the component.
            generics(dict[str, Any]) : individual generic settings of the component.
            synth_path(str)          : path to the synthesis Makefile.

        Returns:
            dictionary of dictionaries, where the key is a combination of common generics. The individual
            dictionaries consist of latency results (Fmax(Mhz), used ALMs) and so on.
        """

        if not os.path.exists(synth_path):
            raise ValueError(f"Synth folder of '{name}' does not exist.")

        # creating dictionary for results of the hash function variant
        synthesis_report: dict = defaultdict(dict)

        # evaluating all the key widths
        for generic_combination in self._generic_combinations:

            # change directory to synth dir
            os.chdir(synth_path)

            # create project file
            os.system("make")

            # find project settings file and set generics
            found_compilation_settings_files = glob.glob("*.qsf")

            # error if file doesn't exist
            if len(found_compilation_settings_files) == 0:
                print("Compilation settings file not found!")
                return

            # generating the compilation settings file and setting the generics
            compilation_settings_file = open(found_compilation_settings_files[0], "a")
            compilation_settings_file.write("\n".join([f'set_parameter -name {name} {value}\n' for name, value in generic_combination]))
            compilation_settings_file.write("\n".join([f'set_parameter -name {name} {value}\n' for name, value in generics.items()]))
            compilation_settings_file.close()

            # compile project (can take a while)
            os.system("quartus_syn *.qpf; quartus_fit *.qpf; quartus_sta *.qpf")

            # get fitter report file
            found_fitter_report_files = glob.glob("*.fit.summary")

            # error if fitter report doesn't exist
            if len(found_fitter_report_files) == 0:
                print("Fitter report not found!")
                return

            # open the found fitter file
            fitter_report_file = open(found_fitter_report_files[0], "r")
            fitter_report = fitter_report_file.read()
            fitter_report_file.close()

            # pattern to find consumed FPGA resources
            fitter_pattern = r"^\s*(Logic utilization[^:]+|Total[^:]+)\s*:\s*([\d,]+)"

            found_resources = re.findall(fitter_pattern, fitter_report, re.MULTILINE)

            # get all resources
            for name, value in found_resources:
                int_value = int(value.replace(",", "").strip())

                # save only resources that have been consumed to reduce clutter
                if int_value > 0:
                    synthesis_report[generic_combination][name.strip()] = int_value

            # get timing report
            found_timing_report_files = glob.glob("*.sta.rpt")

            if len(found_timing_report_files) == 0:
                print("Timing report not found!")
                return

            # reading the found timing report
            timing_report_file = open(found_timing_report_files[0], "r")
            timing_report = timing_report_file.read()
            timing_report_file.close()

            # pattern to find maximum frequency
            fmax_pattern = r"; Fmax Summary(?:.|\n)*?; ([0-9.]+) MHz"

            found_fmax = re.search(fmax_pattern, timing_report)

            # if found, save the Fmax to the report
            if found_fmax:
                synthesis_report[generic_combination]["Fmax (MHz)"] = float(found_fmax.group(1))

            os.system("make clean; rm -fr dni")

            # returning to the script base directory
            os.chdir(self._base_path)

        return synthesis_report

    def _get_latency_report(self, name: str, generics: dict[str, Any], ver_path: str) -> dict[Any, dict[str, int]]:
        """
        Runs pyuvm or cocotb simulation for all combinations of common generics,
        collects latency and returns a report.

        Args:
            name(str)                : name of the component in verification.
            generics(dict[str, Any]) : individual generic settings of the component.
            ver_path(str)            : path to the cocotb verification.

        Returns:
            a dictionary, where keys are combinations of common generics ale values dictionaries
            with the measured latency.
        """

        latency_report: dict[Any, dict[str, int]] = defaultdict(dict)

        # evaluating all the key widths
        for generic_combination in self._generic_combinations:
            # getting latency from pyuvm verification
            os.chdir(ver_path)

            all_generics  = " ".join([f"-g{generic}={value}" for generic, value in (dict(generic_combination) | generics).items()])
            all_generics += f" -gHASH_FUNCTION={name}"

            os.system(f'make SIM_FLAGS="-c -do quit" TESTCASE=run_test_latency GENERICS=\'{all_generics}\'')

            if not os.path.exists("transcript"):
                print("Latency test transcript not found!")
                return

            # reading the transcript of the simulation
            latency_transcript_file = open("transcript", "r")
            latency_transcript = latency_transcript_file.read()
            latency_transcript_file.close()

            # pattern to find the reported latency
            latency_pattern = r"Latency is (\d+) clock cycles"

            found_latency = re.search(latency_pattern, latency_transcript)

            # if found, save it to the report
            if found_latency:
                latency_report[generic_combination]["Latency"] = int(found_latency.group(1))

            # returning to the script base directory
            os.chdir(self._base_path)

        return latency_report

    def _save_report_to_json(self, name: str, report: dict, save_path: str):
        """
        Saves report into a JSON file.

        Args:
            name(str)      : name of the component (also the name of the folder where the
                             report will be saved).
            report(dict)   : the report that will be saved.
            save_path(str) : path where the folder with the name of the component will be created (if it doesn't exist)
                             and the report saved into it.
        """

        # directory where the results and graphs will be saved
        save_dir = os.path.join(save_path, name)

        if not os.path.exists(save_dir):
            os.mkdir(save_dir)

        reorganized_report: dict = defaultdict(dict)

        for generics, results in report.items():
            reorganized_report[f"{generics[0][0]}={generics[0][1]}"][f"{generics[1][0]}={generics[1][1]}"] = results

        # creating the report file for the function variant synthesis report
        report_file = open(os.path.join(save_dir, "resource_analysis.json"), "w")
        # write evaluation to report file
        report_file.write(json.dumps(reorganized_report))
        report_file.close()

    def _generate_graphs(self, name: str, report: dict, save_path: str):
        """
        Generates graphs from the maximum frequency, throughput, latency and resource utilization.

        Args:
            name(str)      : name of the component (also the name of the folder where the
                             graphs will be saved).
            report(dict)   : the from which the graphs will be generated. If some values are missing
                             from the log, the graphs that require this value will be skipped and the
                             problem will be noted in the error log.
            save_path(str) : path where the folder with the name of the component will be created (if it doesn't exist)
                             and the graphs will saved into it.

        If some errors are encountered during the graph generation process, graph_generation_errors.log file will be created
        to denote these errors. Please note that if the previous generation generated errors and the next one is successful,
        the log IS NOT automatically deleted.
        """
        if self._graph_config is None:
            raise AttributeError("Graph configuration is not set!")

        # directory where the results and graphs will be saved
        save_dir = os.path.join(save_path, name)

        if not os.path.exists(save_dir):
            os.mkdir(save_dir)

        # moving to the save directory
        os.chdir(save_dir)

        errors = ""

        # reorganizing the results
        results_per_plot : dict[dict]    = defaultdict(dict)
        input_length_key : str           = self._graph_config.input_length_key
        plot_series_key  : Optional[str] = self._graph_config.plot_series_key

        for generics, result in report.items():
            if plot_series_key is not None:
                plot_series  : Any = dict(generics)[plot_series_key]
                input_length : Any = dict(generics)[input_length_key]

                results_per_plot[plot_series][input_length] = result

        frequency_per_input_length  : dict[dict[int | float]] = defaultdict(dict)
        throughput_per_input_length : dict[dict[int | float]] = defaultdict(dict)
        resources_per_input_length  : dict[dict[int | float]] = defaultdict(dict)
        ta_ratio_per_input_length   : dict[dict[int | float]] = defaultdict(dict)
        throughput_per_resources    : dict[dict[int | float]] = defaultdict(dict)
        throughput_per_latency      : dict[dict[int | float]] = defaultdict(dict)

        # sorting results per plot by pipeline setting
        results_per_plot = dict(sorted(results_per_plot.items(), key=lambda item: int(item[0])))

        # getting results for graphs
        for plot_series, plot_series_dict in results_per_plot.items():

            print(f"{plot_series_dict=}")

            # sorting by input legths
            plot_series_dict = dict(sorted(plot_series_dict.items(), key=lambda item: int(item[0])))

            for input_length, result in plot_series_dict.items():

                print(f"{result=}")

                # checking for frequency, calculating values where only frequency is required
                if "Fmax (MHz)" in result.keys():
                    frequency_per_input_length[plot_series][input_length]  = result["Fmax (MHz)"]
                    # throughput in Gbps
                    throughput_per_input_length[plot_series][input_length] = (result["Fmax (MHz)"] * input_length) / 1_000
                else:
                    errors += f"No 'Fmax (MHz)' for setting ({plot_series_key}={plot_series}, {input_length_key}={input_length}).\n"

                # checking for logic utilization, calculating values where only logic utilization is required
                if "Logic utilization (in ALMs)" in result.keys():
                    resources_per_input_length[plot_series][input_length] = result["Logic utilization (in ALMs)"]
                else:
                    errors += f"No 'Logic utilization (in ALMs)' for setting ({plot_series_key}={plot_series}, {input_length_key}={input_length}).\n"

                # calculating values where frequency and logic utilization is needed
                if "Fmax (MHz)" in result.keys() and "Logic utilization (in ALMs)" in result.keys():
                    resources  = result["Logic utilization (in ALMs)"]
                    # throughput in Mbps
                    throughput = result["Fmax (MHz)"] * input_length

                    throughput_per_resources[plot_series][resources]     = throughput / 1_000
                    ta_ratio_per_input_length[plot_series][input_length] = throughput / resources

                # checking for latency, calculating values where only latency is required
                if "Latency" in result.keys():
                    if "Fmax (MHz)" in result.keys():
                        # throughput in Gbps
                        throughput_per_latency[plot_series][result["Latency"]] = (result["Fmax (MHz)"] * input_length) / 1_000
                else:
                    errors += f"No 'Latency' for setting ({plot_series_key}={plot_series}, {input_length_key}={input_length}).\n"

        graphs: list[dict] = [
            {
                "name"   : "max_frequency_per_input_length",
                "data"   : frequency_per_input_length,
                "xlabel" : self._graph_config.input_length_label,
                "ylabel" : "Maximum frequency (MHz)"
            },
            {
                "name"   : "max_thoughput_per_input_length",
                "data"   : throughput_per_input_length,
                "xlabel" : self._graph_config.input_length_label,
                "ylabel" : "Throughput (Gbps)"
            },
            {
                "name"   : "resource_utilization",
                "data"   : resources_per_input_length,
                "xlabel" : self._graph_config.input_length_label,
                "ylabel" : "Logic utilization (ALMs)"
            },
            {
                "name"   : "throughput_to_area_ratio",
                "data"   : ta_ratio_per_input_length,
                "xlabel" : self._graph_config.input_length_label,
                "ylabel" : "Throughput-to-Area Ratio (Mbps/ALMs)"
            },
            {
                "name"   : "pareto_front",
                "data"   : throughput_per_resources,
                "xlabel" : "Logic utilization (ALMs)",
                "ylabel" : "Throughput (Gbps)"
            },
            {
                "name"   : "throughput_latency_tradeoff",
                "data"   : throughput_per_latency,
                "xlabel" : "Latency (clock cycles)",
                "ylabel" : "Throughput (Gbps)"
            }
        ]

        for graph in graphs:
            # generating graph frequency/input_length_key
            if len(graph["data"]) > 0:
                fig, ax = plt.subplots()

                # generating plot per every pipeline setting
                for plot_series in results_per_plot.keys():

                    if len(graph["data"][plot_series]) == 0:
                        errors += f"No data in {graph.get('name')} for setting {plot_series_key}={plot_series}.\n"
                        continue

                    ax.plot(
                        graph["data"][plot_series].keys(),
                        graph["data"][plot_series].values(),
                        marker='s',
                        linestyle='--',
                        markersize=8,
                        linewidth=1.5,
                        label=self._graph_config.plot_series_label(plot_series)
                    )

                ax.grid(True, linestyle='-', color='gray', alpha=0.5)
                ax.legend()
                ax.set_xlabel(graph["xlabel"], fontsize=12)
                ax.set_ylabel(graph["ylabel"], fontsize=12)

                plt.savefig(f"{graph.get('name')}.png", dpi=300, bbox_inches='tight')
                plt.close(fig)

            else:
                errors += f"No data in {graph.get('name')}.\n"

        # store the log about errors encountered during graph generation
        if len(errors) > 0:
            errors_log = open("graph_generation_errors.log", "w")
            errors_log.write(errors)
            errors_log.close()

        # returning to the script base directory
        os.chdir(self._base_path)


if __name__ == "__main__":
    def get_pipeline_setting_label(pipeline_setting: str) -> str:
        """
        Generates label for the pipeline settings in the graphs.

        Args:
            pipeline_setting(str): setting of the pipeline for which the label
                                   will be created.
        Returns:
            str with the label of the pipeline setting to be used in graphs.
        """
        register_count = Counter(pipeline_setting)["1"]

        if register_count == 0:
            return "No registers"

        register_interval = len(pipeline_setting) // register_count

        match register_interval:
            case 1:
                return "Register between every logical operation"
            case 2:
                return "Register between every 2nd logical operation"
            case 3:
                return "Register between every 3rd logical operation"
            case _:
                return f"Register between every {register_interval}th logical operation"

    common_generics: dict[Any, list[Any]] = {
        "KEY_WIDTH": [32, 128, 296, 512, 1024],
        "REG_SETUP": ["1", "10", "1000"]
    }

    graph_config = ResourceAnalyzerGraphConfig(
        input_length_key="KEY_WIDTH",
        input_length_label="Key length (bits)",
        plot_series_key="REG_SETUP",
        plot_series_label=get_pipeline_setting_label
    )

    # setting of generics for the specific hash functions
    generic_settings = {
        "spookyhash": {
            "SPOOKYHASH": {}
        },

        "siphash": {
            "SIPHASH_2_4": {
                "COMPRESSION_ROUDS"   : 2,
                "FINALIZATION_ROUNDS" : 4,
                "WORD_WIDTH"          : 64,
                "HASH_WIDTH"          : 64,
            },
            "SIPHASH_4_8": {
                "COMPRESSION_ROUDS"   : 4,
                "FINALIZATION_ROUNDS" : 8,
                "WORD_WIDTH"          : 64,
                "HASH_WIDTH"          : 64,
            },
            "SIPHASH_2_4_128": {
                "COMPRESSION_ROUDS"   : 2,
                "FINALIZATION_ROUNDS" : 4,
                "WORD_WIDTH"          : 64,
                "HASH_WIDTH"          : 128,
            },
            "SIPHASH_4_8_128": {
                "COMPRESSION_ROUDS"   : 4,
                "FINALIZATION_ROUNDS" : 8,
                "WORD_WIDTH"          : 64,
                "HASH_WIDTH"          : 128,
            },
        },

        "halfsiphash": {
            "HALFSIPHASH_2_4": {
                "COMPRESSION_ROUDS"   : 2,
                "FINALIZATION_ROUNDS" : 4,
                "WORD_WIDTH"          : 32,
                "HASH_WIDTH"          : 32,
            },
            "HALFSIPHASH_4_8": {
                "COMPRESSION_ROUDS"   : 4,
                "FINALIZATION_ROUNDS" : 8,
                "WORD_WIDTH"          : 32,
                "HASH_WIDTH"          : 32,
            },
            "HALFSIPHASH_2_4_64": {
                "COMPRESSION_ROUDS"   : 2,
                "FINALIZATION_ROUNDS" : 4,
                "WORD_WIDTH"          : 32,
                "HASH_WIDTH"          : 64,
            },
            "HALFSIPHASH_4_8_64": {
                "COMPRESSION_ROUDS"   : 4,
                "FINALIZATION_ROUNDS" : 8,
                "WORD_WIDTH"          : 32,
                "HASH_WIDTH"          : 64,
            },
        },

        "chaskey": {
            "CHASKEY": {
                "ROUNDS": 8
            },
            "CHASKEY_LTS": {
                "ROUNDS": 16
            }
        },

        "pcasd": {
            "PCASD_4_16": {
                "CA_ROUNDS"    : 4,
                "MIX_ROUNDS"   : 16,
                "MIX_FUNCTION" : '"RD_ROUND"'
            },
            "PCASD_8_32" : {
                "CA_ROUNDS"    : 8,
                "MIX_ROUNDS"   : 32,
                "MIX_FUNCTION" : '"RD_ROUND"'
            }
        },

        "pcarx": {
            "PCARX_4_4": {
                "CA_ROUNDS"    : 4,
                "MIX_ROUNDS"   : 4,
                "MIX_FUNCTION" : '"SIPROUND"'
            },
            "PCARX_8_8": {
                "CA_ROUNDS"    : 8,
                "MIX_ROUNDS"   : 8,
                "MIX_FUNCTION" : '"SIPROUND"'
            }
        }
    }

    # lookup for algorithms with shared synth path
    synth_path_alias: dict = {
        "pcarx"       : "pcasd",
        "halfsiphash" : "siphash"
    }

    # lookup for algorithms with shared verification name (verification is used to determine latency)
    ver_alias: dict = {
        "SIPHASH_2_4_128"    : "SIPHASH_2_4",
        "SIPHASH_4_8_128"    : "SIPHASH_4_8",
        "HALFSIPHASH_2_4_64" : "HALFSIPHASH_2_4",
        "HALFSIPHASH_4_8_64" : "HALFSIPHASH_4_8",

    }

    hash_algorithms = ["spookyhash", "siphash", "halfsiphash", "chaskey", "pcasd", "pcarx"]

    resource_analyzer = ResourceAnalyzer(common_generics, graph_config)

    # running analysis for all the hashing algorithms
    for hash_algorithm in hash_algorithms:
        hash_functions_generics = generic_settings[hash_algorithm]

        for hash_function, generics in hash_functions_generics.items():
            resource_analyzer.analyze(
                name=hash_function,
                generics=generics,
                synth_path=os.path.join("..", synth_path_alias.get(hash_algorithm, hash_algorithm), "synth"),
                ver_path=os.path.join("..", "ver", "pyuvm"),
                ver_name=ver_alias.get(hash_function, hash_function)
            )
