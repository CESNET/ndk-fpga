# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import os
import csv
from typing import Callable, Any
from abc import abstractmethod
from random import randbytes, randint
from hashlib import sha256
from collections import Counter, defaultdict
from collections.abc import Iterable
from math import log2
from statistics import mean
import matplotlib.pyplot as plt
import time
import numpy as np


class HashWrapper:
    """
    Universal wrapper for the implemented hash functions.
    """

    @abstractmethod
    def hash(self, message: bytes, seed: bytes) -> bytes:
        """
        Returns calculated hash in bytes.
        """

    @abstractmethod
    def step(self):
        """
        Returns generator which gradually generates variants of the hash function with an increasing number of rounds.

        Yields:
            tuple: A pair containing:
                - int or tuple(int, int): The current round settings.
                - Callable: A function accepting (message, seed) arguments,
                  which performs the hashing with this specific round configuration.
        """


class HashAnalyzer:
    """
    A testing suite for analyzing hash functions.

    This class generates test datasets (random and sequential messages) and performs
    various statistical and cryptographic evaluations, including avalanche effect analysis,
    collision resistance, information entropy, and birthday attacks. It also handles
    the generation of CSV reports and matplotlib graphs for visualizing the results.
    """

    def __init__(self, experiments: int = 1_000_000):
        self._experiments  = experiments
        self._seed         = sha256(b"secret key").digest()[:16]
        self._rnd_messages = set()
        self._seq_messages = set()

        self._generate_messages()

    def analyze(self, name: str, hash_wrapper: HashWrapper, random_message_testing: bool = True, birthday_attack: bool = True, character_distribution: bool = True,
                statistical_analysis_attack: bool = True, information_entropy: bool = True, avalanche: bool = True, collision_resistance: bool = True,
                save_results: bool = True, save_path: str = "./"):
        """
        Executes a selected suite of tests on the provided hash function.
        Generates the required hashes for the datasets and triggers the specific analysis
        methods based on the provided boolean flags.

        Args:
            name(str): The name of the hash function (used for naming output files and plots).
            hash_wrapper(HashWrapper): The wrapper object containing the hash algorithm to be tested.
            random_message_testing(bool): If True, executes the random message mutation test.
            birthday_attack(bool): If True, checks for exact hash collisions.
            character_distribution(bool): If True, evaluates the hexadecimal character spread.
            statistical_analysis_attack(bool): If True, evaluates bit-flipping sensitivity.
            information_entropy(bool): If True, calculates Shannon entropy for hash outputs.
            avalanche(bool): If True, tests the avalanche effect across internal rounds (THIS WILL TAKE A WHILE).
            collision_resistance(bool): If True, tests for partial collisions.
            save_results(bool): If True, exports the results to CSV files and PNG plots.
            save_path(str): The directory where the results folder will be created.
        """

        # generating hashes from random and sequential messages
        rnd_hashes, rnd_lookup = self._generate_hashes(hash_wrapper, self._rnd_messages)
        seq_hashes, seq_lookup = self._generate_hashes(hash_wrapper, self._seq_messages)

        random_message_testing_results      : list[tuple[str, str, int, float]] | None                           = None
        birthday_attack_results             : dict[str, list[str]] | None                                        = None
        character_distribution_results      : list[int] | None                                                   = None
        statistical_analysis_attack_results : tuple[list, int, float, int, float, int, float, int, float] | None = None
        information_entropy_results         : tuple[list, float, float, float] | None                            = None
        avalanche_results                   : dict[Any, tuple[float, float, float, float]] | None                = None
        collision_resistance_results        : tuple[int, int, list[int], int] | None                             = None

        if random_message_testing:
            random_message_testing_results = self.random_message_testing(hash_wrapper)

        if birthday_attack:
            birthday_attack_results = self.birthday_attack(rnd_lookup)

        if character_distribution:
            character_distribution_results = self.character_distribution(seq_hashes)

        if statistical_analysis_attack:
            statistical_analysis_attack_results = self.statistical_analysis_attack(hash_wrapper, rnd_lookup)

        if information_entropy:
            information_entropy_results = self.information_entropy(seq_lookup)

        if avalanche:
            avalanche_results = self.avalanche(hash_wrapper)

        if collision_resistance:
            collision_resistance_results = self.collision_resistance(seq_hashes)

        if save_results:
            self._save_results(
                name,
                save_path,
                random_message_testing_results,
                birthday_attack_results,
                character_distribution_results,
                statistical_analysis_attack_results,
                information_entropy_results,
                avalanche_results,
                collision_resistance_results
            )

    def random_message_testing(self, hash_wrapper: HashWrapper) -> list[tuple[str, str, int, float]]:
        """
        Evaluates the hash function's sensitivity to small, predefined textual changes.

        Takes a base string and slightly modified versions of it, computing the
        Hamming distance between the hash of the first message and the subsequent ones.

        Args:
            hash_wrapper (HashWrapper): The hash function wrapper to be tested.

        Returns:
            list[tuple[str, str, int, float]]: A list of tuples containing:
                - (str) The tested message.
                - (str) The resulting hash in hexadecimal format.
                - (int) The Hamming distance from the original hash.
                - (float) The percentage of changed bits.
        """

        messages = ["Toto je testovaci zprava.",
                    "Toto je Testovaci zprava.",
                    "1Toto je testovaci zprava.",
                    "Toto je testovaci-zprava.",
                    "Toto jf testovaci zprava.",
                    "Toto je testvaci zprava.",
                    "Toto je testovacizprava.",
                    "toto je testovaci zprava.",
                    "Toto je testovaci zprava",
                    "Toto je testovaci zprava. ",
                    ]

        results = list()

        for i, message in enumerate(messages):
            new_hash = hash_wrapper.hash(message.encode(), self._seed)

            if i == 0:
                original_hash = new_hash

            hamming_distance = HashAnalyzer._HammingDistance(original_hash, new_hash)

            results.append((message, new_hash.hex(), hamming_distance, (hamming_distance / (len(original_hash) * 8)) * 100))

        return results

    def birthday_attack(self, lookup: dict[bytes, bytes]) -> dict[str, list[str]]:
        """
        Searches for exact hash collisions within the generated dataset.

        Args:
            lookup (dict[bytes, bytes]): A dictionary mapping original messages to their hashes.

        Returns:
            dict[str, list[str]]: A dictionary of collisions where the key is the
                hexadecimal hash, and the value is a list of hexadecimal messages
                that produced this hash. Empty if no collisions are found.
        """

        reserved_lookup: dict[str, list[str]] = dict()

        for message, hash in lookup.items():
            reserved_lookup.setdefault(hash.hex(), list()).append(message.hex())

        collisions: dict[str, list[str]] = {h: ml for h, ml in reserved_lookup.items() if len(ml) > 1}

        return collisions

    def character_distribution(self, hashes: list[bytes]) -> list[int]:
        """
        Calculates the frequency of each hexadecimal character across all hashes.

        A good hash function should exhibit a uniform distribution of characters (0-9, a-f).

        Args:
            hashes (list[bytes]): A list of generated hashes.

        Returns:
            list[int]: A list of counts corresponding to the occurrence of each
                hexadecimal character (0-9, a-f) in ascending order.
        """

        char_dist: Counter = Counter()

        for hash in hashes:
            char_dist += Counter(hash.hex())

        return list(char_dist.values())

    def statistical_analysis_attack(self, hash_wrapper: HashWrapper, lookup: dict[bytes, bytes]) -> tuple[list[int], int, float, int, float, int, float, int, float]:
        """
        Performs a bit-flipping test to evaluate diffusion.

        Randomly flips exactly one bit in each message of the random dataset, hashes the
        new message, and compares it to the original hash to find the Hamming distance.

        Args:
            hash_wrapper (HashWrapper): The hash function wrapper to be tested.
            lookup (dict[bytes, bytes]): Dictionary mapping original messages to their hashes.

        Returns:
            tuple:
                - (list[int]) all hamming distances.
                - (int) average hamming distance.
                - (float) average percentage of changed bits.
                - (int) minimum hamming distance.
                - (float) minimum percentage of changed bits.
                - (int) maximum hamming distance.
                - (float) maximum percentage of changed bits.
                - (int) difference between minimum and maximum hamming distance.
                - (float) percentage of changed bits of the difference between minimum
                  and maximum hamming distance.
        """

        hamming_distances = list()

        for message1 in self._rnd_messages:
            # flipping random one bit in the message
            message2 = (int.from_bytes(message1, "little") ^ (1 << randint(0, len(message1) * 8 - 1))).to_bytes(len(message1), "little")

            hash1 = lookup[message1]
            hash2 = hash_wrapper.hash(message2, self._seed)

            hamming_distance = HashAnalyzer._HammingDistance(int.from_bytes(hash1, "little"), int.from_bytes(hash2, "little"))

            hamming_distances.append(hamming_distance)

        length = len(hash1) * 8

        # calculating percentage of changed bits
        avg_pr = (mean(hamming_distances) / length) * 100

        min_pr = (min(hamming_distances) / length) * 100

        max_pr = (max(hamming_distances) / length) * 100

        # calculating difference between minum and maximum hamming distance and its percentage compared to the length of the whole message
        min_max_diff_hd = round(((mean(hamming_distances) - min(hamming_distances)) + (max(hamming_distances) - mean(hamming_distances))) / 2)
        min_max_diff_pr = (min_max_diff_hd / length) * 100

        return hamming_distances, round(mean(hamming_distances)), avg_pr, min(hamming_distances), min_pr, max(hamming_distances), max_pr, min_max_diff_hd, min_max_diff_pr

    def information_entropy(self, lookup: dict[bytes, bytes]) -> tuple[list[tuple[str, str, float]], float, float, float]:
        """
        Calculates the Shannon information entropy for the generated hashes.

        H(x) = - Σ [ p(x_i) * log2(p(x_i)) ]  for i = 1 to n

        Measures the randomness and unpredictability of the hash outputs based on
        hex character frequency. An ideal hash approaches the maximum possible entropy.

        Args:
            lookup (dict[bytes, bytes]): Dictionary mapping sequential messages to hashes.

        Returns:
            tuple:
                - (list[tuple[str, str, str]]) decoded message, hex hash, calculated entropy.
                - (float) average entropy.
                - (float) minimum entropy.
                - (float) maximum entropy.
        """

        entropies: list = list()

        for message in self._seq_messages:
            hash = lookup[message].hex()
            hex_chars_count = Counter(hash)
            entropy = 0.0

            for byte_count in hex_chars_count.values():
                p = byte_count / len(hash)
                entropy -= p * log2(p)

            entropies.append(entropy)

        entropies_with_messages_and_hashes = [
            (message.decode(), lookup[message].hex(), entropy) for message, entropy in zip(self._seq_messages, entropies)
        ]

        return entropies_with_messages_and_hashes, mean(entropies), min(entropies), max(entropies)

    def avalanche(self, hash_wrapper: HashWrapper) -> dict[Any, tuple[float, float, float, float]]:
        """
        Evaluates the Avalanche properties of the hash function across different round setups.

        Utilizes the step() generator of the wrapper to test how the completeness,
        avalanche effect, avalanche criterion, and avalanche factor evolve as the
        number of internal rounds increases.

        Args:
            hash_wrapper (HashWrapper): The hash function wrapper yielding step configurations.

        Returns:
            dict[Any, tuple[float, float, float, float]]: A mapping of round configurations
                to their respective avalanche metrics (completeness, avalanche_effect,
                avalanche_criterion, avalanche_factor).
        """

        results     : dict[Any, tuple[float, float, float, float]] = dict()
        hash_length : int = len(hash_wrapper.hash(b"1", self._seed)) * 8

        for key, hash_step in hash_wrapper.step():
            result = self._avalanche_step(hash_step, hash_length)
            results[key] = result

        return results

    def collision_resistance(self, hashes: list[bytes]) -> tuple[int, int, list[int], int]:
        """
        Analyzes the hashes for partial, byte-level collisions.

        Pairs up sequential hashes and counts how many individual bytes match exactly
        at the same positional index, comparing the results to optimal expected values.

        Args:
            hashes (list[bytes]): A list of hashes generated from sequential messages.

        Returns:
            tuple:
                - (int) Hash length in bits (n).
                - (int) Optimal expected number of matching bytes (Nh_optimal).
                - (list[int]) Array of counts representing occurrences of 0 to >=7 byte matches (Neq).
                - (int) Actual weighted sum of matching bytes (Nh_actual).
        """
        Neq: list[int] = [0] * 8

        m: int = len(hashes) // 2

        for i in range(m):
            hash1, hash2 = hashes[i * 2 : (i + 1) * 2]

            matching_bytes_count: int = 0

            for j in range(len(hash1)):
                if hash1[j] == hash2[j]:
                    matching_bytes_count += 1

            if matching_bytes_count >= 7:
                Neq[7] += 1
            else:
                Neq[matching_bytes_count] += 1

        n: int = len(hash1) * 8

        Nh_optimal = (n * m) // 2048
        Nh_actual  = 0

        for i, count in enumerate(Neq):
            Nh_actual += i * count

        return n, Nh_optimal, Neq, Nh_actual

    def _generate_messages(self):
        """
        Generates random and sequential messages.
        """

        # generating random messages
        while len(self._rnd_messages) < self._experiments:
            self._rnd_messages.add(randbytes(randint(1, 191)))

        # generating sequential messages
        for i in range(self._experiments):
            self._seq_messages.add(str(i + 1).encode())

    def _generate_hashes(self, hash_wrapper: HashWrapper, messages: set[bytes]) -> tuple[list[bytes], dict[bytes, bytes]]:
        """
        Generates hashes from the passed messages.

        Args:
            hash_wrapper (HashWrapper): The hash algorithm wrapper.
            messages (set[bytes]): The unique messages to be hashed.

        Returns:
            tuple: A list of the resulting hashes and a dictionary mapping messages to hashes.
        """

        hashes: list = list()
        lookup: dict = dict()

        for message in messages:
            hash = hash_wrapper.hash(message, self._seed)

            hashes.append(hash)
            lookup[message] = hash

        return hashes, lookup

    def _avalanche_step(self, hash_func: Callable, hash_length: int) -> tuple[float, float, float, float]:
        """
        Calculates avalanche metrics for a specific algorithm configuration.

        Flips individual bits of messages, records the resulting bit flips in the hash output,
        and computes standardized cryptographic metrics.

        Args:
            hash_func (Callable): The specific instance of the hash function to run.
            hash_length (int): The expected output length of the hash in bits.

        Returns:
            tuple[float, float, float, float]: The weighted averages of completeness,
                avalanche effect, strict avalanche criterion, and avalanche factor.
        """

        # generating messages of fixed length
        msg_length : int = 64
        messages   : set[bytes] = set()

        while len(messages) < self._experiments:
            messages.add(randbytes(msg_length))

        bits_swapped_map: list[list[int]] = [[0] * hash_length for _ in range(msg_length * 8)]
        hamming_sum = 0

        # processing the individual messages of certain length
        for message in messages:
            original_hash = int.from_bytes(hash_func(message, self._seed), "little")

            for i in range(len(message) * 8):
                new_message = (int.from_bytes(message, "little") ^ (1 << i)).to_bytes(len(message), "little")
                new_hash    = int.from_bytes(hash_func(new_message, self._seed), "little")

                hash_diff   = original_hash ^ new_hash

                hamming_sum += self._HammingDistance(original_hash, new_hash)

                for j in range(hash_length):
                    if (hash_diff >> j) & 1:
                        bits_swapped_map[i][j] += 1

        non_swapped_count = sum(1 for i in range(msg_length * 8) for j in range(hash_length) if not bits_swapped_map[i][j])

        # calculating completenesses
        completness = 1 - (non_swapped_count / (msg_length * 8 * hash_length))

        # calculation of avalanche factor
        total_pairs = len(messages) * msg_length * 8
        average_local_distance = hamming_sum / total_pairs
        ideal_global_distance = hash_length / 2

        avalanche_factor = average_local_distance / ideal_global_distance

        # calculating avalanche effect and criterion
        ae_i_sum = 0.0
        ac_i_sum = 0.0

        for i in range(msg_length * 8):
            ae_j_sum = 0.0
            ac_j_sum = 0.0

            for j in range(hash_length):
                probability_factor = (2 * bits_swapped_map[i][j]) / len(messages)

                ae_j_sum += probability_factor
                ac_j_sum += abs(probability_factor - 1)

            ae_i_sum += abs(ae_j_sum - hash_length)
            ac_i_sum += ac_j_sum

        avalanche_effect    = 1 - (ae_i_sum / (msg_length * 8 * hash_length))
        avalanche_criterion = 1 - (ac_i_sum / (msg_length * 8 * hash_length))

        return completness, avalanche_effect, avalanche_criterion, avalanche_factor

    def _save_results(
        self,
        name                                : str,
        save_path                           : str,
        random_message_testing_results      : list[tuple[str, str, int, float]] | None,
        birthday_attack_results             : dict[str, list[str]] | None,
        character_distribution_results      : list[int] | None,
        statistical_analysis_attack_results : tuple[list, int, float, int, float, int, float, int, float] | None,
        information_entropy_results         : tuple[list, float, float, float] | None,
        avalanche_results                   : dict[Any, tuple[float, float, float, float]] | None,
        collision_resistance_results        : tuple[int, int, list[int], int] | None
    ):
        """
        Creates a dedicated directory for the hash function and generates CSV reports
        and matplotlib PNG graphs for all executed tests.
        """

        cwd = os.getcwd()
        save_path = os.path.join(save_path, name)

        if not os.path.exists(save_path):
            os.mkdir(save_path)

        os.chdir(save_path)

        if random_message_testing_results is not None:
            csv_file   = open("random_message_testing.csv", "w", newline="", encoding="utf-8")
            csv_writer = csv.writer(csv_file)
            csv_writer.writerow(["Message", "Hash", "Hamming distance", "Changed bits (%)"])
            csv_writer.writerows(random_message_testing_results)
            csv_file.close()

            fig, ax = plt.subplots()

            scale   = 0.9
            padding = (1.0 - scale) / 2.0

            message_count = len(random_message_testing_results)

            for i, row in enumerate(random_message_testing_results):
                hash_len = len(row[1]) * 4
                hash     = int(row[1], 16)

                y_offset = message_count - 1 - i

                signal   = [(((hash >> j) & 1) * scale) + padding + y_offset for j in range(hash_len)]

                ax.step(range(hash_len), signal, where='post', linewidth=1)

            ax.set_xlim(0, hash_len)
            ax.set_ylim(-padding, message_count + padding)

            ax.set_xlabel("Bit", fontsize=12)
            ax.set_ylabel("Amplitude", fontsize=12)

            ax.set_yticks(np.arange(message_count) + 0.5)

            labels = [f"Message {message_count - i}" for i in range(message_count)]
            ax.set_yticklabels(labels, fontsize=12)

            ax.tick_params(direction='in', length=6)

            fig.savefig("random_message_testing.png", dpi=300, bbox_inches='tight')
            plt.close(fig)

        if birthday_attack_results is not None:
            csv_file = open("birthday_attack.csv", "w", newline="", encoding="utf-8")
            csv_writer = csv.writer(csv_file)

            if len(birthday_attack_results) > 0:
                csv_writer.writerow(["Hash", "Collisions", "Messages"])

            total_collisions = 0

            for hash_val, messages in birthday_attack_results.items():
                collisions = len(messages) - 1
                total_collisions += collisions

                messages_joined = "\n".join(messages)

                csv_writer.writerow([hash_val, collisions, messages_joined])

            csv_writer.writerow(["Total collisions", total_collisions])

            csv_file.close()

        if character_distribution_results is not None:
            fig, ax = plt.subplots()

            ax.plot(
                [*(str(n) for n in range(10)), "A", "B", "C", "D", "E", "F"],
                character_distribution_results,
                marker='s',
                linestyle='--',
                color='black',
                markerfacecolor='cyan',
                markeredgecolor='blue',
                markersize=8,
                linewidth=1.5,
                label=name
            )

            ax.grid(True, linestyle='-', color='gray', alpha=0.5)
            ax.legend()
            ax.set_xlabel("Hexadecimal character", fontsize=12)
            ax.set_ylabel("Occurence frequency", fontsize=12)

            # scalling the graph to eliminate margin distortion
            mean_val = mean(character_distribution_results)
            percentage_margin = mean_val * 0.015
            data_margin = (max(character_distribution_results) - min(character_distribution_results)) * 0.6
            final_margin = max(percentage_margin, data_margin)

            ax.set_ylim(mean_val - final_margin, mean_val + final_margin)

            fig.savefig("character_distribution.png", dpi=300, bbox_inches='tight')
            plt.close(fig)

        if statistical_analysis_attack_results is not None:
            hamming_distances = statistical_analysis_attack_results[0]

            # hamming distances histogram
            fig, ax = plt.subplots()

            min_val = int(np.floor(np.min(hamming_distances)))
            max_val = int(np.ceil(np.max(hamming_distances)))
            integer_bins = np.arange(min_val, max_val + 2) - 0.5

            ax.hist(
               hamming_distances,
               bins=integer_bins,
               density=False,
               alpha=0.7,
               rwidth=0.85,
               edgecolor='none'
            )

            ax.set_xlabel("Changed bit number", fontsize=12)
            ax.set_ylabel("Number of hits", fontsize=12)
            fig.savefig("hamming_distances_histogram.png", dpi=300, bbox_inches='tight')
            plt.close(fig)

            # hamming distances scatter
            fig, ax = plt.subplots()

            ax.scatter(np.arange(len(hamming_distances)), hamming_distances, s=25, marker='s', c=hamming_distances, cmap='viridis', edgecolors='none', alpha=0.15)

            ax.set_xlabel("Test times", fontsize=12)
            ax.set_ylabel("Changed bit number", fontsize=12)
            fig.savefig("hamming_distances_scatter.png", dpi=300, bbox_inches='tight')
            plt.close(fig)

        if information_entropy_results is not None:
            csv_file   = open("information_entropy.csv", "w", newline="", encoding="utf-8")
            csv_writer = csv.writer(csv_file)
            csv_writer.writerow(["Message", "Hash", "Information entropy"])
            csv_writer.writerows(information_entropy_results[0])
            csv_writer.writerow([f"Average entropy = {information_entropy_results[1]}", f"Minimum entropy = {information_entropy_results[2]}",
                                 f"Maximum entropy = {information_entropy_results[3]}"])
            csv_file.close()

        if avalanche_results is not None:
            param_names = [
                "completeness",
                "avalanche_effect",
                "avalanche_criterion",
                "avalanche_factor"
            ]

            param_y_axis_names = {
                "completeness"        : "Completeness",
                "avalanche_effect"    : "The value of avalanche effect",
                "avalanche_criterion" : "The value of strict avalanche criterion",
                "avalanche_factor"    : "The value avalanche factor"
            }

            di_cond_reached_step: dict[str, int] = dict()
            de_cond_reached_step: dict[str, int] = dict()
            ds_cond_reached_step: dict[str, int] = dict()
            df_cond_reached_step: dict[str, int] = dict()

            first_key = next(iter(avalanche_results.keys()))

            for i, param_name in enumerate(param_names):
                # generating graph
                fig, ax = plt.subplots(figsize=(8, 5))

                if isinstance(first_key, Iterable):
                    data_by_c = defaultdict(dict)

                    for (c_rounds, d_rounds), params_tuple in avalanche_results.items():
                        data_by_c[c_rounds][d_rounds] = params_tuple[i]

                    for c in sorted(data_by_c.keys()):
                        d_dict = data_by_c[c]
                        x_vals = sorted(d_dict.keys())
                        y_vals = [d_dict[d] for d in x_vals]

                        ax.plot(
                            x_vals, y_vals,
                            marker='o', markersize=4, linewidth=1.5,
                            label=f"{name}({c}, x)"
                        )

                        # collecting data for the table
                        match param_name:
                            case "completeness":
                                cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if y >= 1.0), "-")
                                di_cond_reached_step[f"{name}({c}, x)"] = cond_reached
                            case "avalanche_effect":
                                cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if y >= 0.98), "-")
                                de_cond_reached_step[f"{name}({c}, x)"] = cond_reached
                            case "avalanche_criterion":
                                cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if y >= 0.97), "-")
                                ds_cond_reached_step[f"{name}({c}, x)"] = cond_reached
                            case "avalanche_factor":
                                cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if 0.99 <= y <= 1.01), "-")
                                df_cond_reached_step[f"{name}({c}, x)"] = cond_reached

                else:
                    x_vals = sorted(avalanche_results.keys())
                    y_vals = [avalanche_results[x][i] for x in x_vals]

                    ax.plot(
                        x_vals, y_vals,
                        marker='o', markersize=4, linewidth=1.5,
                        label=name
                    )

                    # collecting data for the table
                    match param_name:
                        case "completeness":
                            cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if y >= 1.0), "-")
                            di_cond_reached_step[f"{name}"] = cond_reached
                        case "avalanche_effect":
                            cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if y >= 0.98), "-")
                            de_cond_reached_step[f"{name}"] = cond_reached
                        case "avalanche_criterion":
                            cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if y >= 0.97), "-")
                            ds_cond_reached_step[f"{name}"] = cond_reached
                        case "avalanche_factor":
                            cond_reached = next((x_vals[i] for i, y in enumerate(y_vals) if 0.99 <= y <= 1.01), "-")
                            df_cond_reached_step[f"{name}"] = cond_reached

                ax.legend()

                ax.set_ylim(0, 1.1)

                ax.set_xlabel("Step", fontsize=12)
                ax.set_ylabel(f"{param_y_axis_names[param_name]}", fontsize=12)
                ax.grid(True, linestyle='--', color='gray', alpha=0.5)

                fig.savefig(f"{param_name}.png", dpi=300, bbox_inches='tight')
                plt.close(fig)

            csv_file   = open("avalanche_effect.csv", "w", newline="", encoding="utf-8")
            csv_writer = csv.writer(csv_file)
            csv_writer.writerow(["Hash functions", "Step of DI >= 1", "Step of DE >= 0.98", "Step of DS >= 0.97", "Step of DF = 1.0 +- 0.01"])

            for hash_func_name in di_cond_reached_step.keys():
                csv_writer.writerow([
                    hash_func_name,
                    di_cond_reached_step[hash_func_name],
                    de_cond_reached_step[hash_func_name],
                    ds_cond_reached_step[hash_func_name],
                    df_cond_reached_step[hash_func_name]
                ])

            csv_file.close()

        if collision_resistance_results is not None:
            csv_file   = open("collision_resistance.csv", "w", newline="", encoding="utf-8")
            csv_writer = csv.writer(csv_file)
            csv_writer.writerow(["Name", "n", "Optimum of Nh", *(str(n) for n in range(7)), ">=7", "Actaul Nh"])
            csv_writer.writerow([name, collision_resistance_results[0], collision_resistance_results[1], *collision_resistance_results[2], collision_resistance_results[3]])
            csv_file.close()

        os.chdir(cwd)

    @staticmethod
    def _HammingDistance(h1: int | bytes, h2: int | bytes):
        """
        Computes the Hamming distance (number of differing bits) between two values.

        Args:
            h1 (int | bytes): The first value.
            h2 (int | bytes): The second value.

        Returns:
            int: The total count of differing bits.
        """

        if isinstance(h1, bytes):
            h1 = int.from_bytes(h1, "little")

        if isinstance(h2, bytes):
            h2 = int.from_bytes(h2, "little")

        return (h1 ^ h2).bit_count()


if __name__ == "__main__":
    import spookyhash
    from siphash import siphash_64, siphash_128, half_siphash_32, half_siphash_64
    from ofm.comp.base.hash.chaskey.chaskey import Chaskey
    from ofm.comp.base.hash.pcasd.pcasd import PCASD

    class SpookyHashWrapper(HashWrapper):
        def hash(self, message: bytes, seed: bytes):
            return spookyhash.hash128(message, int.from_bytes(seed[0:8], "little"), int.from_bytes(seed[8:16], "little")).to_bytes(16, "little")

        def step(self):
            yield 1, lambda message, seed: self.hash(message, seed)

    class SipHashWrapper(HashWrapper):
        def __init__(self, c_rounds: int = 2, d_rounds: int = 4, out_width: int = 64, halfsiphash: bool = False, c_step_size: int = 1, d_step_size: int = 1):
            self._c_rounds    = c_rounds
            self._d_rounds    = d_rounds
            self._out_width   = out_width
            self._halfsiphash = halfsiphash
            self._c_step_size = c_step_size
            self._d_step_size = d_step_size

        def _hash(self, message: bytes, seed: bytes, c_rounds: int = 2, d_rounds: int = 4):
            if not self._halfsiphash:
                match self._out_width:
                    case 64:
                        return siphash_64(seed, message, c_rounds, d_rounds)
                    case 128:
                        return siphash_128(seed, message, c_rounds, d_rounds)
                    case _:
                        raise NotImplementedError(f"Siphash with hash width of {self._out_width} bits is not implemented.")
            else:
                match self._out_width:
                    case 32:
                        return half_siphash_32(seed[0:8], message, c_rounds, d_rounds)
                    case 64:
                        return half_siphash_64(seed[0:8], message, c_rounds, d_rounds)
                    case _:
                        raise NotImplementedError(f"Halfsiphash with hash width of {self._out_width} bits is not implemented.")

        def hash(self, message: bytes, seed: bytes):
            return self._hash(message, seed, self._c_rounds, self._d_rounds)

        def step(self):
            for c_rounds in range(0, self._c_rounds + 1, self._c_step_size):
                for d_rounds in range(0, self._d_rounds + 1, self._d_step_size):
                    yield (c_rounds, d_rounds), lambda message, seed: self._hash(message, seed, c_rounds, d_rounds)

    class ChaskeyWrapper(HashWrapper):
        def __init__(self, rounds: int = 8, step_size: int = 2):
            self._rounds    = rounds
            self._step_size = step_size

        def _hash(self, message: bytes, seed: bytes, rounds: int):
            return Chaskey.Hash128(message, seed, rounds)

        def hash(self, message: bytes, seed: bytes):
            return self._hash(message, seed, self._rounds)

        def step(self):
            for rounds in range(0, self._rounds + 1, self._step_size):
                yield rounds, lambda message, seed: self._hash(message, seed, rounds)

    class PCASDWrapper(HashWrapper):
        def __init__(self, ca_rounds: int = 4, rd_rounds: int = 32, mix_function: str = "RD_ROUND", ca_step_size: int = 1, rd_step_size: int = 4):
            self._ca_rounds    = ca_rounds
            self._rd_rounds    = rd_rounds
            self._mix_function = mix_function
            self._ca_step_size = ca_step_size
            self._rd_step_size = rd_step_size

        def _hash(self, message: bytes, seed: bytes, ca_rounds: int, rd_rounds: int):
            return PCASD(seed, ca_rounds, rd_rounds, block_width=32, mix_function=self._mix_function, multithreaded=False).hash(message)[0:16]

        def hash(self, message: bytes, seed: bytes):
            return self._hash(message, seed, self._ca_rounds, self._rd_rounds)

        def step(self):
            for ca_rounds in range(0, self._ca_rounds + 1, self._ca_step_size):
                for rd_rounds in range(0, self._rd_rounds + 1, self._rd_step_size):
                    yield (ca_rounds, rd_rounds), lambda message, seed: self._hash(message, seed, ca_rounds, rd_rounds)

    hash_wrappers: dict[Callable] = {
        "SPOOKYHASH":
            SpookyHashWrapper(),
        "SIPHASH_2_4":
            SipHashWrapper(2, 4, 64),
        "SIPHASH_2_4_128":
            SipHashWrapper(2, 4, 128),
        "SIPHASH_4_8":
            SipHashWrapper(4, 8, 64),
        "SIPHASH_4_8_128":
            SipHashWrapper(4, 8, 128),
        "HALFSIPHASH_2_4":
            SipHashWrapper(2, 4, 32, halfsiphash=True),
        "HALFSIPHASH_2_4_64":
            SipHashWrapper(2, 4, 64, halfsiphash=True),
        "HALFSIPHASH_4_8":
            SipHashWrapper(4, 8, 32, halfsiphash=True),
        "HALFSIPHASH_4_8_64":
            SipHashWrapper(2, 4, 64, halfsiphash=True),
        "CHASKEY":
            ChaskeyWrapper(8),
        "CHASKEY_LTS":
            ChaskeyWrapper(12),
        "PCARX_2_4":
            PCASDWrapper(2, 4, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_4_4":
            PCASDWrapper(4, 4, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_8_4":
            PCASDWrapper(8, 4, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_10_4":
            PCASDWrapper(10, 4, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_2_8":
            PCASDWrapper(2, 8, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_4_8":
            PCASDWrapper(4, 8, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_8_8":
            PCASDWrapper(8, 8, mix_function="SIPROUND", rd_step_size=1),
        "PCARX_10_8":
            PCASDWrapper(10, 8, mix_function="SIPROUND", rd_step_size=1),
        "PCASD_2_16":
            PCASDWrapper(2, 16),
        "PCASD_4_16":
            PCASDWrapper(4, 16),
        "PCASD_8_16":
            PCASDWrapper(8, 16),
        "PCASD_10_16":
            PCASDWrapper(10, 16),
        "PCASD_2_32":
            PCASDWrapper(2, 32),
        "PCASD_4_32":
            PCASDWrapper(4, 32),
        "PCASD_8_32":
            PCASDWrapper(8, 32),
        "PCASD_10_32":
            PCASDWrapper(10, 32),
    }

    # analyzing all hashing algoritms in all the metrics accept for stepped avalanche effect.
    analyzer: HashAnalyzer = HashAnalyzer(1_000_000)

    for name, hash_wrapper in hash_wrappers.items():
        print(f"Testing {name}")
        start = time.perf_counter()
        analyzer.analyze(name, hash_wrapper, avalanche=False)
        end = time.perf_counter()
        print(f"{name} testing finished in {(end - start):.6f} s")

    # analyzing all the hashing algoritmhs in the stepped avalanche effect.
    analyzer: HashAnalyzer = HashAnalyzer(1_000)

    # perform resource-intensive avalanche test only on common denominaters (lower round setting will be tested using the steps)
    for name in ["SIPHASH_4_8", "SIPHASH_4_8_128", "HALFSIPHASH_4_8", "HALFSIPHASH_4_8_64", "CHASKEY_LTS", "PCARX_8_8", "PCASD_8_32"]:
        print(f"Testing avalanche {name}")
        start = time.perf_counter()
        analyzer.analyze(
            name,
            hash_wrappers[name],
            random_message_testing=False,
            birthday_attack=False,
            character_distribution=False,
            statistical_analysis_attack=False,
            information_entropy=False,
            avalanche=True,
            collision_resistance=False
        )
        end = time.perf_counter()
        print(f"{name} avalanche testing finished in {(end - start):.6f} s")
