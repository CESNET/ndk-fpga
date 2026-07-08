# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
from cocotb.triggers import RisingEdge
from cocotbext.ofm.axi4stream.transaction import Axi4StreamBaseTransaction
from dataclasses import asdict
from cocotbext.ofm.utils.signals import filter_bytes_by_bitmask


# import the correct BusMonitor based on the cocotb version
if cocotb.__version__ >= "2.0.0":
    from cocotbext.ofm.base.monitors import BusMonitor
else:
    from cocotb_bus.monitors import BusMonitor


class Axi4Stream(BusMonitor):
    _signals = ["TVALID", "TREADY"]
    _optional_signals = ["TDATA", "TLAST", "TSTRB", "TKEEP", "TID", "TDEST", "TUSER"]

    _optional_data_signals = \
        tuple(signal for signal in _optional_signals if signal != "TREADY")

    def __init__(self, *args, aux_signals=False, trans_type: Axi4StreamBaseTransaction | dict = dict, **kwargs):
        super().__init__(*args, **kwargs)

        self.aux_signals = aux_signals
        self.__trans_type = trans_type

        if issubclass(self.__trans_type, Axi4StreamBaseTransaction):
            self.__transaction = self.__trans_type()
        elif self.__trans_type is not dict:
            raise TypeError("Unsupported transaction type requested from Axi4Stream (passed as trans_type).")

        os = Axi4Stream._optional_signals if isinstance(Axi4Stream._optional_signals, dict) else {s: s for s in self._optional_signals}
        self.__recv_signals = {k: s for k, s in os.items() if hasattr(self.bus, s)}

        self.frame_cnt = 0

    async def _monitor_recv(self):
        re = RisingEdge(self.clock)

        while True:
            await re

            if self.bus.TVALID.value and self.bus.TREADY.value:
                # returns a whole frame as Axi4StreamTransaction
                if issubclass(self.__trans_type, Axi4StreamBaseTransaction):
                    word = {k: getattr(self.bus, s).value.buff[::-1] for k, s in self.__recv_signals.items()}

                    for name, value in asdict(self.__transaction).items():
                        if not hasattr(self.bus, name):
                            continue

                        width    = len(getattr(self.bus, name))
                        old_val  = getattr(self.__transaction, name)

                        if isinstance(value, int):
                            word_val = int.from_bytes(word[name], "little")
                            new_val  = (old_val << width) + word_val

                        elif isinstance(value, bytes):
                            if name == "TDATA" and hasattr(self.bus, "TKEEP"):
                                keep = int.from_bytes(word["TKEEP"], "little")
                                word_val = filter_bytes_by_bitmask(word[name], keep)
                            else:
                                word_val = word[name]

                            new_val = old_val + word_val

                        else:
                            raise TypeError(f"Attribute {name} of transaction passed to Axi4Stream monitor is of unsupported type: {type(value)}.")

                        setattr(self.__transaction, name, new_val)

                    last = int.from_bytes(word["TLAST"], "little")

                    if last:
                        self._recv(self.__transaction)
                        self.frame_cnt += 1
                        self.__transaction = self.__trans_type()

                # returns only one word as a dictionary, for backwards compatibility
                else:
                    word = {k: getattr(self.bus, s).value.buff for k, s in self.__recv_signals.items()}

                    self._recv(word)
                    self.frame_cnt += 1
