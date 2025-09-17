# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>
#            Jakub Cabal <cabal@cesnet.cz>

import sys
import logging
from dataclasses import dataclass, fields
from typing import Any, Optional, List

import nfb


@dataclass
class GeneratorConfig:
    enabled: bool
    frame_length: int
    channel_increment: int
    channel_increment_reversed: bool
    bursting: bool
    burst_size: int
    minimum_channel: int
    maximum_channel: int
    dst_mac_address: bytes
    src_mac_address: bytes
    src_ip_address_mask: int
    generating: Optional[bool] = None # Read-only
    frame_count: Optional[int] = None # Read-only


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
    _REG_SRC_IP_MASK     = 0x28

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._logger = logging.getLogger("MfbGenerator")
        self._cfg_type_d = {
            f.name : f.type for f in fields(GeneratorConfig)
            if "Optional" not in str(f.type) # filter out read only values
        }

    # ################
    # Command register
    # ################
    @property
    def enabled(self) -> bool:
        """The generator is running."""
        return self._comp.get_bit(self._REG_CONTROL, 0)

    @enabled.setter
    def enabled(self, en: bool) -> None:
        self._comp.write32(self._REG_CONTROL, int(en))
        while bool(self.generating) != en:
            pass

    @property
    def generating(self) -> bool:
        """Packets are being generated.

        Its value should correspond with the `enabled` property.
        Makes sense to check when generating bursts.
        """
        return self._comp.get_bit(self._REG_CONTROL, 1)

    def clear(self):
        """Clear packet counters."""
        self._comp.set_bit(self._REG_CONTROL, 4)

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
        if enable:
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

    @staticmethod
    def convert_bytes2mac(mac: bytes, sep: str = "") -> Any:
        """Convert a 6-byte little-endian MAC address into big-endian with an optional formatting.

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

    @staticmethod
    def convert_mac2bytes(mac: Any, sep: str = "") -> bytes:
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
        """Get the number of generated frames (may overflow frequently due to low cnt width)."""
        return int.from_bytes(self._comp.read(self._REG_FRAME_CNT_LOW, 8), byteorder=sys.byteorder)

    # ################
    # IP mask register
    # ################
    @property
    def src_ip_address_mask(self) -> int:
        """Get the mask of the generated SRC IP address."""
        if self._node.get_property("version").value >= 2:
            return self._comp.read32(self._REG_SRC_IP_MASK)
        return 0

    @src_ip_address_mask.setter
    def src_ip_address_mask(self, mask: int) -> None:
        """Set the mask to generate SRC IP address."""
        if self._node.get_property("version").value >= 2:
            self._comp.write32(self._REG_SRC_IP_MASK, mask)
        else:
            self._logger.warning("Unable to set SRC IP address mask in this generator version. Try using a newer FW.")

    # #############
    # Configuration
    # #############
    def get_configuration(self) -> GeneratorConfig:
        """Returns the full configuration of the generator (all properties)."""
        # TODO: optimize this by reducing the amount of MI Reads
        conf = GeneratorConfig(
            enabled=self.enabled,
            generating=self.generating,
            frame_length=self.frame_length,
            channel_increment=self.channel_increment,
            channel_increment_reversed=self.channel_increment_reversed,
            bursting=self.bursting,
            burst_size=self.burst_size,
            minimum_channel=self.minimum_channel,
            maximum_channel=self.maximum_channel,
            dst_mac_address=self.dst_mac_address,
            src_mac_address=self.src_mac_address,
            src_ip_address_mask=self.src_ip_address_mask,
            frame_count=self.frame_count,
        )
        return conf

    def configure(self, conf: GeneratorConfig) -> None:
        """Configures the Generator while ignoring read-only items."""
        self.frame_length = conf.frame_length
        self.channel_increment = conf.channel_increment
        self.channel_increment_reversed = conf.channel_increment_reversed
        self.bursting = conf.bursting
        self.burst_size = conf.burst_size
        self.minimum_channel = conf.minimum_channel
        self.maximum_channel = conf.maximum_channel
        self.dst_mac_address = conf.dst_mac_address
        self.src_mac_address = conf.src_mac_address
        self.src_ip_address_mask = conf.src_ip_address_mask
        self.enabled = conf.enabled

    def _convert_attr(self, attr_name: str, attr_value: str) -> Any:
        if "mac" in attr_name:
            return MfbGenerator.convert_mac2bytes(attr_value)

        if "mask" in attr_name:
            return int(attr_value, 16)

        prop_type = self._cfg_type_d[attr_name]
        return prop_type(attr_value)

    def configure_attr(self, attr_name: str, str_value: str):
        """Configure a config attribute.

        This method aims to enable dynamic configuration using string names of data class
        arguments and string values, that are going to be converted to int/bytes/bool.
        For other usages, property setters are recommended.

        Args:
            attr_name: Attribute name of GeneratorConfig data class.
                       NOTE that read-only attributes are not allowed.
            str_value: Value to be set for given attribute.

        Raises:
            ValueError: If an invalid attribute name is passed.
            AttributeError: If there is an inconsistency between this class's properties and
                            GeneratorConfig attributes.
            IOError: If the given attribute cannot be configured.
        """

        if attr_name not in self._cfg_type_d.keys():
            attrs_str = ",\n\t".join(self._cfg_type_d.keys())
            raise ValueError(
                f"Cannot configure {attr_name},"
                f" not in supported list of attributes:\n\t{attrs_str}"
            )

        if attr_name not in dir(self):
            raise AttributeError("Internal error!")

        if attr_name == "src_ip_address_mask":
            version = self._node.get_property("version").value
            if version < 2:
                raise IOError(
                    f"Cannot set src_ip_address_mask, version of MFB generator is {version},"
                    f" but minimal version 2 is required"
                )

        prop_obj = getattr(type(self), attr_name)
        value = self._convert_attr(attr_name, str_value)
        prop_obj.fset(self, value)

    def get_fconfiguration(self) -> List:
        """Returns formatted configuration of the generator as a list of [item, value] lists."""
        conf = self.get_configuration()
        conf.dst_mac_address = MfbGenerator.convert_bytes2mac(conf.dst_mac_address, ':')
        conf.src_mac_address = MfbGenerator.convert_bytes2mac(conf.src_mac_address, ':')
        lst = []
        for field in fields(conf):
            value = getattr(conf, field.name)
            # Convert src_ip_address_mask to hex if it exists
            if field.name == "src_ip_address_mask":
                if self._node.get_property("version").value >= 2:
                    value = hex(value)
                else:
                    value = "UNSUPPORTED!"
            # Convert booleans to strings for tabulation
            if isinstance(value, bool):
                value = str(value)
            lst.append([field.name, value])
        return lst
