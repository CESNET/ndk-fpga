# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from dataclasses import dataclass
from typing import Optional, Tuple

import nfb
from ofm.comp.mfb_tools.debug.generator import MfbGenerator
from ofm.comp.mfb_tools.logic.speed_meter import SpeedMeter

@dataclass
class StreamNodes:
    """A helpful class to encapsulate information about the nodes of a GlsStream."""
    tx_sm_name: str
    rx_sm_name: str
    gen_name: str
    rx_mux_offset: int
    tx_mux_offset: int

class GlsStream:
    """Top (left2right) or bottom (right2left) part of the GenLoopSwitch.

    Contains the appropriate Generator and Speed Meter objects and address offsets of the Multiplexers.

    Usage:
    Methods like `gen_start` and `gen_stop` that abstract or simplify the usage of the generator.
    Other methods/properties are accessible though the generator and speed meter objects.

    Example:
    gls = GenLoopSwitch()
    gls.l2r.gen.frame_length = 512
    gls.l2r.gen.enable = True
    dma_rx_speed = gls.l2r.tx_sm_measure()
    """

    def __init__(self, dev, node, comp, stream_nodes, sm_exist):
        self._comp = comp
        self._rx_mux = stream_nodes.rx_mux_offset
        self._tx_mux = stream_nodes.tx_mux_offset

        if sm_exist:
            self.tx_sm = SpeedMeter(dev=dev, node=node.get_subnode(stream_nodes.tx_sm_name), lightweight=True)
            self.rx_sm = SpeedMeter(dev=dev, node=node.get_subnode(stream_nodes.rx_sm_name), lightweight=True)
        self.gen = MfbGenerator(dev=dev, node=node.get_subnode(stream_nodes.gen_name))
        # self.player = ...

    # ############
    # Multiplexers
    # ############
    @property
    def mux_generator(self) -> int:
        """Indicates the input (data source) of the Generator MUX.

        Set or get the MUX's state, (de)coded as follows:
            0 - RX Stream (default)
            1 - MFB Generator
            2 - Frame Player

        Warning:
            The Frame Player should not be used to transmit data to the RX DMA because
            FW support for DMA headers is not implemented!
        """
        return self._comp.read32(self._rx_mux)

    @mux_generator.setter
    def mux_generator(self, n: int) -> None:
        self._comp.write32(self._rx_mux, n)

    @property
    def mux_loopback(self) -> int:
        """Indicates the input (data source) of the Loopback MUX.

        Set or get the MUX's state, (de)coded as follows:
            0 - output of the Generator MUX (default)
            1 - input of the r2l stream (loopback)
        """
        return self._comp.read32(self._tx_mux)

    @mux_loopback.setter
    def mux_loopback(self, n: int) -> None:
        self._comp.write32(self._tx_mux, n)

    @property
    def input(self) -> int:
        """Indicates the data source for the Stream's output.

        The data source is (de)coded as follows:
            0 - Forward RX Stream
            1 - MFB Generator
            2 - Frame Player
            3 - Loopback TX Stream
        """
        if self.mux_loopback == 1:
            return 3
        return self.mux_generator

    @input.setter
    def input(self, n: int) -> None:
        if n == 3:
            self.mux_loopback = 1
        else:
            self.mux_loopback = 0
            self.mux_generator = n

    # ############
    # Speed Meters
    # ############
    def tx_sm_measure(self, freq: int = 2*10**8) -> Tuple[float, float | None]:
        """Measure throughput speed on the TX interface of this Stream, return [bps]."""
        return GenLoopSwitch.sm_measure(self.tx_sm)

    def rx_sm_measure(self, freq: int = 2*10**8) -> Tuple[float, float | None]:
        """Measure throughput speed on the RX interface of this Stream, return [bps]."""
        return GenLoopSwitch.sm_measure(self.rx_sm)

    # #############
    # MFB Generator
    # #############
    def gen_start(
        self,
        en_path: bool = False,
        length: Optional[int] = None,
        min_ch: Optional[int] = None,
        max_ch: Optional[int] = None,
    ) -> None:
        """Start generating frames, optionally also configure the Generator beforehand.

        Args:
            en_path: if set, configure the MUXes to transmit the Generator's data to the output.
            length: configure the length of the generated frames.
            min_ch, max_ch: define the range of channels (channel IDs), each ID is sent with a frames as metadata.
        """

        if en_path:
            self.input = 1
        if length is not None:
            self.gen.frame_length = length
        if min_ch is not None:
            self.gen.minimum_channel = min_ch
        if max_ch is not None:
            self.gen.maximum_channel = max_ch

        self.gen.enabled = True

    def gen_stop(self) -> None:
        """Stop generating frames and return MUXes to their default state (both to 0)."""
        self.gen.enabled = False
        while self.gen.enabled:
            continue
        self.input = 0

    # ############
    # Frame Player (not yet supported)
    # ############
    def player_start(
        self,
        en_path: bool = False,
    ) -> None:
        """Start transmitting stored frames, optionally also configure the Player beforehand.

        Args:
            en_path: if set, configure the MUXes to transmit the Player's data to the output.
        """
        # Pynfb module for the Frame Player has not yet been implemented. MI access could be used.
        raise NotImplementedError("Unable to use the Frame Player at this time.")
        if en_path:
            self.input = 2
        self.player.enable = True

    def player_stop(self) -> None:
        """Stop transmitting frames."""
        # Pynfb module for the Frame Player has not yet been implemented. MI access could be used.
        raise NotImplementedError("Unable to use the Frame Player at this time.")
        self.player.enable = False

# #########################
# The GEN LOOP SWITCH class
# #########################
class GenLoopSwitch(nfb.BaseComp):
    """Enables control over the Generator/Loopback Switch (GLS) FW component.

    Familiarity with the gen_loop_switch FW component (at least its documentation) is strongly
    advised.

    The user can control the (generator and loopback) multiplexers, generators, and speed meters
    using one of its "Stream" instances. The GLS is virtually split into two Streams: left2right
    and right2left. Each of them manages what is forwarded to its output.

    Example:
    The left2right Stream (l2r) selects the source of data forwarded out of the right side.
    The data source can be:
    - data from this Streams input (straight connection),
    - data from the other stream's input (= loopback on the right side using MUX_A),
    - or a generator (MFB Generator / Frame Player - not supported).

    Usage:
    To loop data on the right side, set `gls.l2r.mux_loopback = 1` or `gls.l2r.input = 3`.
    To generate data to the right side using a MFB Generator, the simplest way is to use the
    gen_start method like so: `gls.l2r.gen_start(en_path=True)`.
    To get the full configuration of the (l2r) MFB Generator: `gls.l2r.gen.get_configuration()`.
    To measure speed on the right side on the TX interface:
     - option 1: `GenLoopSwitch.sm_measure(gls.l2r.tx_sm)`
     - option 2: `gls.l2r.tx_sm_measure()`
    """

    DT_COMPATIBLE = "cesnet,ofm,gen_loop_switch"

    _REG_MUX_A = 0x00 # The "Loopback MUX" for the left2right Stream
    _REG_MUX_B = 0x04 # The "Loopback MUX" for the right2left Stream
    _REG_MUX_C = 0x08 # The "Generator MUX" for the left2right Stream
    _REG_MUX_D = 0x0C # The "Generator MUX" for the right2left Stream

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        l2r_nodes = StreamNodes(
            # The names are taken from the Device Tree (they must correspond).
            tx_sm_name = "l2r_tx_speed_meter",
            rx_sm_name = "l2r_rx_speed_meter",
            gen_name = "mfb_gen2dma",
            rx_mux_offset = self._REG_MUX_C,
            tx_mux_offset = self._REG_MUX_A,
        )
        r2l_nodes = StreamNodes(
            # The names are taken from the Device Tree (they must correspond).
            tx_sm_name = "r2l_tx_speed_meter",
            rx_sm_name = "r2l_rx_speed_meter",
            gen_name = "mfb_gen2eth",
            rx_mux_offset = self._REG_MUX_D,
            tx_mux_offset = self._REG_MUX_B,
        )

        # Checking for the presence of SpeedMeters, may not be available in older versions of FW.
        # There should always be all SpeedMeters or none.
        self.speedmeters_exist = True
        if not self._node.exist_subnode(l2r_nodes.tx_sm_name):
            print(f"Warning: SpeedMeters of the {self._node.name} not found in the Device Tree.")
            print(f"         Unable to use methods to measure speed.")
            print(f"         Try using a newer FW.")
            self.speedmeters_exist = False

        self.l2r = GlsStream(self._dev, self._node, self._comp, l2r_nodes, self.speedmeters_exist)
        self.r2l = GlsStream(self._dev, self._node, self._comp, r2l_nodes, self.speedmeters_exist)

    @staticmethod
    def sm_measure(sm: SpeedMeter, to: float = 0.1, freq: Optional[int] = 2*10**8) -> Tuple[float, float | None]:
        """Use the given SpeedMeter to measure the throughput speed, return [bps]."""
        return sm.measure(to, freq)
