# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_subscriber


class Coverage(uvm_subscriber):
    key_intervals = (
        range(0, 8), range(8, 16), range(16, 31), range(32, 64), range(64, 128),
        range(128, 512), range(512, 1024), range(1024, 1400), range(1400, 1464),
        range(1464, 1496), range(1496, 1512), range(1512, 1520), range(1520, 1528)
    )

    seed_intervals = (
        range(0, 8), range(8, 16), range(16, 32), range(32, 64),
        range(64, 96), range(96, 112), range(112, 120), range(120, 128)
    )

    def end_of_elaboration_phase(self):
        key_width  = self.parent.dut.key_width
        seed_width = self.parent.dut.seed_width

        self.key_cvg  = dict()
        self.seed_cvg = dict()

        for ki in self.key_intervals:
            if key_width < ki.start:
                break
            self.key_cvg[ki] = False

        for si in self.seed_intervals:
            if seed_width < si.start:
                break
            self.seed_cvg[si] = False

    def write(self, transaction):
        key_width  = transaction.key.bit_length()
        seed_width = transaction.seed.bit_length()

        for ki in self.key_cvg.keys():
            if key_width in ki:
                self.key_cvg[ki] = True

        for si in self.seed_cvg.keys():
            if seed_width in si:
                self.seed_cvg[si] = True

    def report_phase(self):
        key_ranges_not_covered  = list()
        seed_ranges_not_covered = list()

        for key_range, covered in self.key_cvg.items():
            if not covered:
                key_ranges_not_covered.append(key_range)

        for seed_range, covered in self.seed_cvg.items():
            if not covered:
                seed_ranges_not_covered.append(seed_range)

        report = f"Key coverage: {round(((len(self.key_cvg.keys()) - len(key_ranges_not_covered)) / len(self.key_cvg.keys())) * 100, 4)}%\n"

        if len(key_ranges_not_covered) > 0:
            report += f"Key ranges not covered: {key_ranges_not_covered}\n"

        report += f"Seed coverage: {round(((len(self.seed_cvg.keys()) - len(seed_ranges_not_covered)) / len(self.seed_cvg.keys())) * 100, 4)}%\n"

        if len(seed_ranges_not_covered) > 0:
            report += f"Seed ranges not covered: {seed_ranges_not_covered}\n"

        self.logger.info(report)
