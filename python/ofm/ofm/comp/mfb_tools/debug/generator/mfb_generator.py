import sys
from typing import Any

import nfb


class MfbGenerator(nfb.BaseComp):
    DT_COMPATIBLE = "cesnet,ofm,mfb_generator"

    # Register addresses
    _REG_CONTROL         = 0x00
    _REG_LENGTH          = 0x04
    _REG_CHANNEL_INCR    = 0x08
    _REG_CHANNEL_MIN_MAX = 0x0C
    _REG_DST_MAC_LOW     = 0x10
    _REG_DST_MAC_HIGH    = 0x14
    _REG_SRC_MAC_LOW     = 0x18
    _REG_SRC_MAC_HIGH    = 0x1C
    _REG_FRAME_CNT_LOW   = 0x20
    _REG_FRAME_CNT_HIGH  = 0x24

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    # ################
    # Command register
    # ################
    def start(self) -> None:
        """Set the generator to active state (start generating frames).

        The only other bit that could be set by writing to this address is the Clear bit, which is
        not desired. Hence, write32() is used instead of set_bit() as reading the value of this
        register first does not really make sense.
        """
        self._comp.write32(self._REG_CONTROL, 1)

    def stop(self) -> None:
        """Set the generator to inactive state (stop generating frames).

        The only other bit that could be set by writing to this address is the Clear bit, which is
        not desired. Hence, write32() is used instead of set_bit() as reading the value of this
        register first does not really make sense."""
        self._comp.write32(self._REG_CONTROL, 0)

    def clear(self) -> None:
        """Clear the generator's frame counters."""
        self._comp.set_bit(self._REG_CONTROL, 4)

    @property
    def enabled(self) -> bool:
        """Returns True if the generator has been enabled."""
        return self._comp.get_bit(self._REG_CONTROL, 0)

    @property
    def generating(self) -> bool:
        """Returns True if packets are being generated.

        Makes sense to check when generating bursts.
        """
        return self._comp.get_bit(self._REG_CONTROL, 1)

    @property
    def clearing(self) -> bool:
        """Returns True if frame counters are being cleared/reset.

        Does not make sense to check as it is asserted for only a single clock cycle issuing the
        clear command (it is not realistic to get other value than 0).
        """
        return self._comp.get_bit(self._REG_CONTROL, 1)

    # #####################
    # Frame Length register
    # #####################
    @property
    def frame_length(self) -> int:
        """Get the size of the generated frames."""
        return self._comp.read32(self._REG_LENGTH)

    @frame_length.setter
    def frame_length(self, length: int) -> None:
        """Set the generator to generate frames of the given length."""
        self._comp.write32(self._REG_LENGTH, length)

    # ##########################
    # Channel Increment register
    # ##########################
    @property
    def channel_increment(self) -> int:
        """Get the number by which channel ID of each generated frame is incremented."""
        return self._comp.read8(self._REG_CHANNEL_INCR)

    @channel_increment.setter
    def channel_increment(self, incr: int) -> None:
        """Increment each frame's channel ID by the set amount.

        Warning: this feature is buggy (in FW), especially when also setting the min and max
                 channel. Undefined behaviour when set above the number of available DMA channels
                 (when transmitting to the DMA).
        """
        if incr > 2**8-1:
            raise OverflowError(f"Max value for Channel Increment is 2**8-1 (got {incr})!")
        # Workaround for the unsupported MI ByteEnable (can't use _comp.write8()):
        # 1. Read the full 32-bit value,
        # 2. apply mask to clear the lowest 8 bits,
        # 3. use OR to insert the new value to the lowest 8 bits.
        val = (self._comp.read32(self._REG_CHANNEL_INCR) & 0xffffff00) | incr
        self._comp.write32(self._REG_CHANNEL_INCR, val)
        # self._comp.write8(self._REG_CHANNEL_INCR, incr) # if the Generator supported MI BE

    @property
    def channel_increment_reversed(self) -> bool:
        """Returns True if bit-reversed channel IDs are used."""
        return self._comp.get_bit(self._REG_CHANNEL_INCR, 8)

    @channel_increment_reversed.setter
    def channel_increment_reversed(self, reverse: bool) -> None:
        """Use bit-reversed value of the channel ID when set to True."""
        self._comp.set_bit(self._REG_CHANNEL_INCR, 8, reverse)

    @property
    def bursting(self) -> bool:
        """Returns True if packets are being sent in bursts."""
        return self._comp.get_bit(self._REG_CHANNEL_INCR, 9)

    @bursting.setter
    def bursting(self, enable: bool) -> None:
        """Configure the generator to send packets in bursts."""
        raise NotImplementedError("Reliable bursting has not yet been implemented.")
        # self._comp.set_bit(self._REG_CHANNEL_INCR, 9, enable)

    @property
    def burst_size(self) -> int:
        """Returns the number of packets generated with each `MfbGenerator.start()`."""
        return self._comp.read16(self._REG_CHANNEL_INCR+2)

    @burst_size.setter
    def burst_size(self, burst: int) -> None:
        """Set the number of packets that will be generated with each `MfbGenerator.start()`."""
        # Workaround similar to the one in the channel_increment setter
        val = (burst << 16) | self._comp.read16(self._REG_CHANNEL_INCR)
        self._comp.write32(self._REG_CHANNEL_INCR, val)
        # self._comp.write16(self._REG_CHANNEL_INCR+2, burst) # if the Generator supported MI BE

    # ########################
    # Channel Min Max register
    # ########################
    @property
    def minimum_channel(self) -> int:
        """Get the lowest channel ID that will be used."""
        return self._comp.read16(self._REG_CHANNEL_MIN_MAX)

    @minimum_channel.setter
    def minimum_channel(self, channel: int) -> None:
        """Set the lowest channel ID that will be used."""
        if channel > 2**16-1:
            raise OverflowError(f"Max value for Minimum Channel is 2**16-1 (got {channel})!")
        val = (self.maximum_channel << 16) | channel
        self._comp.write32(self._REG_CHANNEL_MIN_MAX, val)
        # self._comp.write16(self._REG_CHANNEL_MIN_MAX, channel) # if the Generator supported MI BE

    @property
    def maximum_channel(self) -> int:
        """Get the highest channel ID that will be used."""
        return self._comp.read16(self._REG_CHANNEL_MIN_MAX+2)

    @maximum_channel.setter
    def maximum_channel(self, channel: int) -> None:
        """Set the highest channel ID that will be used."""
        val = (channel << 16) | self.minimum_channel
        self._comp.write32(self._REG_CHANNEL_MIN_MAX, val)
        # self._comp.write16(self._REG_CHANNEL_MIN_MAX+2, channel) # if the Generator supported MI BE

    # ################################
    # Destination MAC address register
    # ################################
    @property
    def dst_mac_address(self) -> bytes:
        """Get the destination MAC address that is a part of the generated frames.

        Returned value is six bytes in the little-endian format.
        For other formats use the convert_bytes2mac() method.
        """
        return self._comp.read(self._REG_DST_MAC_LOW, 6)

    @dst_mac_address.setter
    def dst_mac_address(self, dmac: bytes) -> None:
        """Configure the destination MAC address that will be a part of the generated frames.

        The value must be six bytes in the little-endian format.
        For other formats use the convert_mac2bytes() method.
        """
        if len(dmac) != 6:
            raise ValueError(f"MAC address must be 6 bytes long (got {len(dmac)})!")
        self._comp.write(self._REG_DST_MAC_LOW, dmac)

    @property
    def src_mac_address(self) -> bytes:
        """Get the source MAC address that is a part of the generated frames.

        Returned value is six bytes in the little-endian format.
        For other formats use the convert_bytes2mac() method.
        """
        return self._comp.read(self._REG_SRC_MAC_LOW, 6)

    @src_mac_address.setter
    def src_mac_address(self, smac: bytes) -> None:
        """Configure the source MAC address that will be a part of the generated frames.

        The value must be six bytes in the little-endian format.
        For other formats use the convert_mac2bytes() method.
        """
        if len(smac) != 6:
            raise ValueError(f"MAC address must be 6 bytes long (got {len(smac)})!")
        self._comp.write(self._REG_SRC_MAC_LOW, smac)

    def convert_bytes2mac(self, mac: bytes, sep: str = "") -> Any:
        """Conver a 6-byte little-endian MAC address into big-endian with an optional formatting.

        Args:
            mac: The MAC Address as six little-endian bytes.
            sep: The separator of the returned MAC Address (big-endian). Examples:
                    1) "" (unsupplied parameter) just changes the endianity
                    2) ":" returns a string, e.g.: "aa:bb:cc:dd:ee:ff"
                    3) "-" returns a string, e.g.: "aa-bb-cc-dd-ee-ff"

        Returns:
            The MAC address (big-endian) in the selected format.

        Raises:
            TypeError: when the `mac` argument is not a bytes object.
        """
        if not isinstance(mac, bytes):
            raise TypeError(f"The type of argument 'mac' must be 'bytes', got '{type(mac)}'!")

        mac_bige = mac[::-1] # reverse bytes (for big-endian)
        if sep:
            return sep.join(f'{byte:02x}' for byte in mac_bige)
        return mac_bige

    def convert_mac2bytes(self, mac: Any, sep: str = "") -> bytes:
        """Convert a MAC address into a 6-byte little-endian.

        Args:
            mac: The MAC Address in big-endian to be converted to bytes in little-endian.
            sep: The separator of the MAC Address (big-endian). Applicable when `mac` is a string.

        Examples:
            1) `mac` is an instance of 'bytes': b'\xaa\xbb\xcc\xdd\xee\xff' -> b'\xff\xee\xdd\xcc\xbb\xaa'
               (only endianity is changed and `sep` is ignored),
            2) `mac` is a string: "aa:bb:cc:dd:ee:ff" -> b'\xff\xee\xdd\xcc\xbb\xaa'
                (if `sep` is supplied, it is used, else the third character of the `mac` is used).

        Returns:
            Six little-endian bytes representing the given MAC address.

        Raises:
            ValueError: when one of the arguments is invalid.
            TypeError: when the 'mac' argument is of unsupported type.
        """

        if isinstance(mac, bytes):
            return mac[::-1] # just reverse the bytes; no separator expected in this case

        if isinstance(mac, str):
            if not sep:
                sep = mac[2] # select the third character as the separator
            try:
                mac_parts = mac.split(sep)
                if len(mac_parts) != 6:
                    raise ValueError
            except ValueError:
                raise ValueError(f"Could not split the input MAC address ({mac}) using the '{sep}' as a separator.")
            # Hoping all parts will be hexadecimal values, else another try-except needed.
            return bytes(int(part, 16) for part in reversed(mac_parts))

        raise TypeError(f"Unsupported type of the MAC address ({type(mac)})!")

    # ####################
    # Frame count register
    # ####################
    @property
    def frame_count(self) -> int:
        """Get the number of generated frames."""
        return int.from_bytes(self._comp.read(self._REG_FRAME_CNT_LOW, 8), byteorder=sys.byteorder)
