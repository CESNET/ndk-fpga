# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from typing import Optional, Any
from . import math as mathext
from math import log2


# TODO
# add undefined value, like U and X
# comparing of Binary and different classes, for example int -> Binary should before comparison return int representation

"""
IMPORTANT INFO:
    - number stored in Binary has fixed parameters that can be only changed
      by redefinition of these parameters (for example, if number is stored
      as unsigned, all of it represenations will be unsigned until self.signed
      is set to True.)
    - if arithmetic operation includes Binary, the result is always Binary. Binary
      can be only "escaped" by using representation functions (such as bin, int, ...)
    - keep in mind that BinaryVector is still Binary with few extensions. So when
      it comes to arithmetic operation and so on it will behave just like Binary would
      (at this time, may be chagned in the future).
"""


class BinaryConvertions:
    """
    Collection of operations with binary numbers represented by list of ones and zeros.

    They are intended for Binary, but they can be usefull if you can't or don't want to use
    Binary for whatever reason.
    """

    def invert_bits(binary: list):
        """
        Changes value of positive bits to negative and vice versa.
        (basically the operation ~).
        """
        return [(1, 0)[n] for n in binary]

    def negate_bits(binary: list):
        """
        Switches positive number represented by bits to a negative and
        vice versa (basically the operation -).
        """
        binary = BinaryConvertions.invert_bits(binary)
        num = BinaryConvertions.bin_to_int(binary) + 1
        return BinaryConvertions.int_to_bin(num, bits=len(binary))

    def reorder_bytes(value: int, in_endian: str, out_endian: str, bits: Optional[int] = None) -> int:
        """
        Changes endian from big to little and vice versa.
        """

        assert in_endian in ["little", "big"] and out_endian in ["little", "big"]

        if bits is None:
            bits = value.bit_length()

        if in_endian == out_endian:
            return value

        buff = value.to_bytes(mathext.ceildiv(8, bits), in_endian)

        return int.from_bytes(buff, out_endian)

    def reverse_bits(binary: list):
        """
        Changes order of bits from MSB to LSB and vice versa.
        """
        return [binary[len(binary)-i-1] for i in range(len(binary))]

    def bin_to_int(binary: list, *, signed: bool = False) -> int:
        """
        Converts binary number represented by list of ones and zeros to
        a integer.

        Args:
            binary: list of ones and zeros.
            signed: if the binary should be interpreted as signed (True) or unsigned (False).
            bigEndian: if the endian is big (True) or little (False). Applies only to multibyte values.

        Returns:
            value of binary number as integer.
        """
        assert all(item in [0, 1] for item in binary)

        sign: int = 1

        if len(binary) == 0:
            return 0

        if signed and binary[0] == 1:
            binary = BinaryConvertions.negate_bits(binary)
            sign = -1

        return sign * sum([binary[i] * (2**(len(binary)-i-1)) for i in range(len(binary))])

    def bin_to_string(binary: list, *, base: Optional[int] = 2):
        """
        Converts list of 0 and 1 to a string represenation of the
        number of specified base represented by 0 and 1.
        """
        conv_funcs = {2: bin, 8: oct, 10: int, 16: hex}
        binstr = "".join([str(n) for n in binary])
        return str(conv_funcs[base](int(binstr, base=2)))

    def bin_to_bytes(binary: list, *, nbytes: int = None, endian: str = 'little'):
        """
        Converts binary number to string of bytes.

        Args:
            binary: list of ones and zeros.
            nbytes: number of bytes of the output byte string. If not passed, the value
                    is determined by ceildiv function.
            endian: which endian the final bytestring should have, options = ('big', 'little')

        Returns:
            byte string.
        """
        assert endian in [None, 'big', 'little']

        endian = 'big' if endian is None else endian

        nbytes = mathext.ceildiv(8, len(binary)) if nbytes is None else nbytes

        buff = bytearray(nbytes)

        for i in range(nbytes):
            buff[i] = BinaryConvertions.bin_to_int(binary[i*8 : (i+1)*8])

        return bytes(buff)

    def int_to_bin(num: int, *, bits: int = None) -> list:
        """
        Converts integer to a binary number represented
        by a list of ones and zeros.

        Args:
            num: integer to be converted.
            bits: number of bits of the final binary. If not passed,
                  the number is displayed on the smallest possible
                  number of bits

        Returns:
            binary representation of the passed integer.
        """

        binary = list()

        sign = -1 if num < 0 else 1

        if num == 0:
            bits = 1 if bits is None else bits
            return [0] * bits

        num_shifted = sign * num

        while num_shifted != 0:
            binary.insert(0, num_shifted % 2)
            num_shifted = num_shifted >> 1

        if sign == -1:
            binary = [1] + BinaryConvertions.negate_bits(binary)

        if (bits is not None):
            if bits < len(binary):
                raise RuntimeError(f"Cannot display {num} on {bits} bits.")

            if sign == -1:
                binary = [1] * (bits - len(binary)) + binary

            else:
                binary = [0] * (bits - len(binary)) + binary

        return binary

    def str_to_bin(string: str, *, base: Optional[int] = 2) -> list:
        """
        Converts number passed as a string to a list ones and zeros.
        For non-binary numbers, it is necessary to specify the base
        of the passed number.

        Args:
            string: number represented by a string.
            base : base of the passed number.

        Returns:
            Passed number as list of ones and zeros.
        """
        return BinaryConvertions.int_to_bin(int(string, base=base))

    def bytes_to_bin(buff: bytes) -> list:
        binary = list()

        assert len(buff) > 0

        for byte in buff:
            binary += BinaryConvertions.int_to_bin(byte, bits=8)

        return binary


class Binary:
    """
    Class for easier storing of and working with binary numbers.

    Attributes:
        value: integer value of the object.
        bits: number or bits of the binary representation.
        base: base of the stored number, can be 2, 8, 10 or 16.
        endian: how should be the data interpreted, (None, 'big', 'little').
        signed: if the stored number is signed or unsigned.
    """

    def __init__(self, value: Any = None, *, bits: Optional[int] = None, base: Optional[int] = 2, endian: Optional[str] = "little", signed: Optional[bool] = False):
        # setting value and endian to default values
        self._value = 0
        self._endian = "little"

        # setting up main attributes. Order should be kept, or else it might break
        self.base: int = base
        self.signed: bool = signed
        self.bits: int = bits
        self.endian: Optional[str] = endian
        self.value: int = value

    @property
    def value(self) -> int:
        return self._value

    @value.setter
    def value(self, value) -> None:
        """
        Setter of internal value. Supported types are list, int, str, bytes, Binary and None.
        Through this attribute can the value of Binary class be changed.
        When passing through a string, it's also possible to input the number in decimal,
        octal or hexadecimal, however it's necessary to specify the base using the Binary.base
        attribute.

        Examples:
            >>> b = Binary()
            >>> b.value = [1,0,1]
            >>> b.value = 5
            >>> b.value = b'\x05'
            >>> b.value = Binary(5)
            >>> b.value = None  # this will be stored as 0.
            >>> b.value = "101"  # b.base = 2 by default, so this will be stored as 5.
            >>> b.base = 8; b.value = "101"  # this will be stored as 65.
            >>> b.base = 10; b.value = "101"  # this will be stored as 101.
            >>> b.base = 16; b.value = "101"  # this will be stored as 257.
            >>> b.value = "abba"  # you can also use letters, this will be stored as 43962.
        """

        if value is None:
            self._value = 0

        elif type(value) is type(self):
            self.bits  = value.bits if self._bits is None else self.bits
            self._value = value.value

        elif isinstance(value, list):
            self.bits  = len(value) if self._bits is None else self.bits
            self._value = BinaryConvertions.bin_to_int(value, signed=self.signed)

        elif isinstance(value, int):
            self._value = BinaryConvertions.reorder_bytes(value, "little", self.endian, bits=self.bits)

        elif isinstance(value, str):
            self.bits = len(value) * int(log2(self._base)) if self._bits is None else self.bits
            bin = BinaryConvertions.str_to_bin(value, base=self._base)
            self._value = BinaryConvertions.bin_to_int(bin, self.signed)

        elif isinstance(value, bytes):
            self.bits = len(value) * 8 # implicit alligning
            self._value = int.from_bytes(value, self.endian)

        else:
            raise TypeError(f"Incompatible type ({type(value)}) passed to Binary.value. Supported types are: list, int, str, bytes, Binary, None.")

    @property
    def bits(self) -> int:
        """
        Returns number of bits of the stored number.
        """
        if self._bits is None:
            return 1 if self._value.bit_length() == 0 else self._value.bit_length()
        else:
            return self._bits

    @bits.setter
    def bits(self, value) -> None:
        """
        Sets number of bits of the stored number. The binary number will be extended or shortened accordingly.
        """
        assert type(value) is int or value is None
        self._bits = value
        self.value = self.int

    @property
    def endian(self):
        """
        Returns set endian.
        """
        return self._endian

    @endian.setter
    def endian(self, value: str):
        """
        Sets endian of the stored multibyte number.
        If None, the number has big endian, but the number of bits isn't extended to be divisible by 8 (so not alligned to bytes).
        If big, the number has big endian and number of bits is extended.
        If little, the number has little endian and number of bits is extended.
        """
        assert value in ['big', 'little']
        self.value = BinaryConvertions.reorder_bytes(self.value, self._endian, value, bits=self.bits)
        self._endian = value

    @property
    def signed(self):
        """
        Returns if the stored number is signed (True) or unsigned (False)
        """
        return self._signed

    @signed.setter
    def signed(self, value: bool):
        """
        Sets if the stored number is signed (True) or unsigned (False).
        """
        assert type(value) is bool
        self._signed = value

    @property
    def base(self):
        """
        Returns the base of the stored number (2, 8, 10 or 16).
        """
        return self._base

    @base.setter
    def base(self, value):
        """
        Sets the base of the stored number (possible bases: 2, 8, 10, 16)
        """
        if value not in (2, 8, 10, 16):
            raise ValueError(f"Unsupported base {value}.")

        self._base = value

    @property
    def bin(self) -> list:
        """
        Returns binary representation of the stored number as list of ones and zeros.
        This is also how the number is stored internally.
        """
        return BinaryConvertions.int_to_bin(self._value, bits=self.bits)

    @property
    def int(self) -> int:
        """
        Returns the stored number as decimal integer.
        """
        return self._value

    @property
    def hex(self) -> str:
        """
        Returns the stored number as a hexadecimal string.
        """
        return hex(self.int)

    @property
    def octal(self) -> str:
        """
        Returns the stored number as a octal string.
        """
        return oct(self.int)

    @property
    def binstr(self) -> str:
        """
        Returns the stored number as a binary string.
        """
        return bin(self.value)

    @property
    def stored(self) -> Any:
        """
        Returns the number that was originally stored (taking into account numbers original base and endian).
        """
        if self.endian == "little":
            return {2: self.binstr, 8: self.octal, 10: self.int, 16: self.hex}.get(self.base, None)
        else:
            return type(self)(BinaryConvertions.reorder_bytes(self.value, "little", "big", bits=self.bits), bits=self.bits, base=self.base, signed=self.signed).stored

    @property
    def bytes(self) -> bytes:
        """
        Returns the stored number as bytes.
        """
        return self.value.to_bytes(mathext.ceildiv(8, self.bits), self.endian, signed=self.signed)

    @property
    def maxint(self) -> int:
        """
        Returns maximum value as int.
        """
        return mathext.bitmask(self.bits) if not self.signed else mathext.bitmask(self.bits - 1)

    def flipped(self):
        """
        Returns a copy of this Binary object with inverted bits (for each bit in binary => [0 -> 1, 1 -> 0]).
        """
        value = mathext.bitmask(self._bits) & (~self._value)
        return Binary(value, bits=self._bits, endian=self.endian, signed=self.signed)

    def flip(self):
        """
        Inverts bits of this Binary object (for each bit in binary => [0 -> 1, 1 -> 0]).
        """
        self._value = self.flipped().value
        return self

    def reversed(self):
        """
        Returns a copy of this Binary object with a reversed bit order (for example "1011" -> "1101").
        """
        return Binary(BinaryConvertions.reverse_bits(self.bin), bits=self._bits, endian=self.endian, signed=self.signed)

    def reverse(self):
        """
        Reverses bit order of this Binary object (for example "1011" -> "1101").
        """
        self.value = self.reversed().value
        return self

    def flipped_endian(self):
        """
        Changes endian from little to big and vice versa.
        """
        return Binary(self.bytes[::-1], bits=self._bits, endian=self.endian, signed=self.signed)

    def negated(self):
        """
        Returns a copy of this Binary object with negated bits (for each bit in binary => [0 -> 1, 1 -> 0] && binary += 1).
        """
        return Binary(~self._value, bits=self._bits, endian=self.endian, signed=self.signed)

    def negate(self):
        """
        Negates bits of this Binary object (for each bit in binary => [0 -> 1, 1 -> 0] && binary += 1).
        """
        self.value = ~self._value
        return self

    def joined(self, other: Any):
        """
        Returns a copy of this Binary extended by another Binary object with the value of argument 'other'.
        """
        other = Binary(other, endian=self.endian, signed=self.signed)
        return Binary(self.bin + other.bin, endian=self.endian, signed=self.signed)

    def join(self, other: Any):
        """
        Appends Binary object with the value of argument 'other' to this Binary object.
        """
        self.bits = (self.joined(other)).bits
        self.value = (self.joined(other)).value
        return self

    # representations
    def __repr__(self) -> str:
        return self.binstr

    def __str__(self) -> str:
        return self.binstr

    # item handling
    def __getitem__(self, index):
        """
        Returns slice of this Binary object wrapped in a new Binary object.
        """
        if isinstance(index, slice):
            start = index.start if index.start is not None else 0
            stop  = index.stop if index.stop is not None else self.bits
            bits  = abs(stop - start)
            bitmask = mathext.bitmask(bits)
            value   = (self._value >> start) & bitmask
        elif isinstance(index, int):
            bits = 1
            value   = (self._value >> index) & 1
        else:
            raise ValueError("Invalid index type passed to __getitem__ of Binary object.")

        return Binary(value, bits=bits, signed=self.signed)

    def __setitem__(self, index, value):
        """
        Sets slice of this Binary object to the passed value.
        """
        if isinstance(value, bytes):
            value = int.from_bytes(value, self.endian)
        elif isinstance(value, str):
            value = int(value, 2)
        elif isinstance(value, list):
            value = BinaryConvertions.bin_to_int(value, signed=self.signed)
        elif isinstance(value, Binary):
            value = value.int
        else:
            if not isinstance(value, int):
                raise ValueError("Unsupported value passed to __setitem__ of Binary object.")

        if isinstance(index, slice):
            start   = index.start if index.start is not None else 0
            stop    = index.stop if index.stop is not None else self.bits
            slc_len = abs(stop - start)

            if (bc := value.bit_length()) > slc_len:
                raise ValueError(f"Value {value} of length {bc} bits doesn't fit into slice of {slc_len} bits.")

            bitmask = mathext.bitmask(slc_len)
            self.value = (self._value & (~(bitmask << start))) + (value << start)

        elif isinstance(index, int):
            assert value in [0, 1]
            self.value = (self._value & (~(1 << index))) + (value << index)
        else:
            raise ValueError("Invalid index type passed to __getitem__ of Binary object.")

    # math operators - result is always Binary
    def __add__(self, other: Any):
        return Binary(self.int + Binary(other).int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __radd__(self, other: Any):
        return self.__add__(other)

    def __sub__(self, other: Any):
        return Binary(self.int - Binary(other).int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __rsub__(self, other: Any):
        return Binary(Binary(other).int - self.int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __mul__(self, other: Any):
        return Binary(Binary(other).int * self.int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __rmul__(self, other: Any):
        return self.__mul__(other)

    def __floordiv__(self, other: Any):
        return Binary(self.int // Binary(other).int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __rfloordiv__(self, other: Any):
        return Binary(Binary(other).int // self.int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __mod__(self, other: Any):
        return Binary(Binary(other).int % self.int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __rmod__(self, other: Any):
        return Binary(self.int % Binary(other).int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __pow__(self, other: Any):
        return Binary(Binary(other).int ** self.int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __rpow__(self, other: Any):
        return Binary(self.int ** Binary(other).int, bits=self._bits, endian=self.endian, signed=self.signed)

    def __truediv__(self, other: Any):
        raise SyntaxError("Cannot use truediv (/) with binary value. Use floordiv (//) instead.")

    def __rtruediv__(self, other: Any):
        raise SyntaxError("Cannot use truediv (/) with binary value. Use floordiv (//) instead.")

    # bitwise operators - result is always Binary
    def __invert__(self):
        return self.flipped()

    def __neg__(self):
        return self.negated()

    def __and__(self, other):
        other = Binary(other, bits=self._bits)
        return Binary([self[i] & other[i] for i in range(self.bits)], bits=self._bits, endian=self.endian, signed=self.signed)

    def __rand__(self, other):
        other = Binary(other, bits=self._bits)
        return Binary([other[i] & self[i] for i in range(other.bits)], bits=self._bits, endian=self.endian, signed=self.signed)

    def __or__(self, other):
        other = Binary(other, bits=self._bits)
        return Binary([self[i] | other[i] for i in range(self.bits)], bits=self._bits, endian=self.endian, signed=self.signed)

    def __ror__(self, other):
        other = Binary(other, bits=self._bits)
        return Binary([other[i] | self[i] for i in range(other.bits)], bits=self._bits, endian=self.endian, signed=self.signed)

    def __xor__(self, other):
        other = Binary(other, bits=self._bits)
        return Binary([self[i] ^ other[i] for i in range(self.bits)], bits=self._bits, endian=self.endian, signed=self.signed)

    def __rxor__(self, other):
        other = Binary(other, bits=self._bits)
        return Binary([other[i] ^ self[i] for i in range(other.bits)], bits=self._bits, endian=self.endian, signed=self.signed)

    def __lshift__(self, other: int):
        assert type(other) is int
        return Binary(self.value << other, bits=self._bits, endian=self.endian, signed=self.signed)

    def __rshift__(self, other: int):
        assert type(other) is int
        return Binary(self.value >> other, bits=self._bits, endian=self.endian, signed=self.signed)

    # conditional
    def __bool__(self):
        return self.int != 0


class BinaryVector(Binary):
    """
    Vector of binary numbers.
    In reality it's just Binary devided into smaller sections of fixed lenght that can be indexed (aka 'items').
    """

    def __init__(self, item_count: int, item_bits: int, items: list = None, **kwargs):
        super().__init__(bits=item_count * item_bits, **kwargs)
        self._item_bits = item_bits

        if items is not None:
            self._item_count = len(items[:item_count])
            for i in range(self.item_count):
                self[i] = items[i]
        else:
            self._item_count = item_count
            self.value = 0 if self.value is None else self.value

        self.item_count = item_count

    @property
    def item_count(self):
        return self._item_count

    @item_count.setter
    def item_count(self, new_item_count):
        assert type(new_item_count) is int
        assert new_item_count > 0

        if new_item_count == self._item_count:
            return
        elif new_item_count > self._item_count:
            self.join(Binary(0, bits=(new_item_count - self._item_count) * self._item_bits))
        else:
            self.value = Binary(self[: new_item_count * self._item_bits]).int

        self._item_count = new_item_count
        self.bits = self.item_count * self.item_bits

    @property
    def item_bits(self):
        return self._item_bits

    @item_bits.setter
    def item_bits(self, new_item_bits):
        assert type(new_item_bits) is int
        assert new_item_bits > 0

        if new_item_bits == self._item_bits:
            return

        new_vector: BinaryVector = BinaryVector(self.item_count, new_item_bits, self.vint)
        self._item_bits = new_item_bits
        self.value = 0
        self.bits = self.item_count * self.item_bits
        self.value = new_vector.value

    @property
    def vbin(self):
        """
        Returns list of stored items, items are represented by list of ones and zeros.
        """
        return [self[i].bin for i in range(len(self.bin) // self._item_bits)]

    @property
    def vint(self):
        """
        Returns list of stored items, items are represented by decimal integers.
        """
        return [self[i].int for i in range(len(self.bin) // self._item_bits)]

    @property
    def vhex(self):
        """
        Returns list of stored items, items are represented by hexadecimal strings.
        """
        return [self[i].hex for i in range(len(self.bin) // self._item_bits)]

    @property
    def voctal(self):
        """
        Returns list of stored items, items are represented by octal strings.
        """
        return [self[i].octal for i in range(len(self.bin) // self._item_bits)]

    @property
    def vbinstr(self):
        """
        Returns list of stored items, items are represented by binary strings.
        """
        return [self[i].binstr for i in range(len(self.bin) // self._item_bits)]

    @property
    def vstored(self):
        """
        Returns list of stored items, items are returned in the form they were stored in (see Binary.stored for more info).
        """
        return [self[i].stored for i in range(len(self.bin) // self._item_bits)]

    @property
    def vbytes(self):
        """
        Returns list of stored items, items are represented by bytes.
        """
        return [self[i].bytes for i in range(len(self.bin) // self._item_bits)]

    def vreversed(self):
        return BinaryVector(self.item_count, self.item_bits, [self[self.item_count-i-1].int for i in range(self.item_count)])

    # vector operations
    def vadd(self, other: Any):
        """
        Vector add operation. Can be preformed between two vectors or vector and constant.
        Result is stored in the caller object
        """
        # vector + vector
        if type(other) is type(self):
            for i in range(self.item_count):
                self[i] = self[i] + other[i]

        # vector + constant
        else:
            for i in range(self.item_count):
                self[i] = self[i] + Binary(other)

    def vsub(self, other: Any):
        # vector - vector
        if type(other) is type(self):
            for i in range(self.item_count):
                self[i] = self[i] - other[i]

        # vector - constant
        else:
            for i in range(self.item_count):
                self[i] = self[i] - Binary(other)

    def vmul(self, other: Any):
        # vector * vector
        if type(other) is type(self):
            for i in range(self.item_count):
                self[i] = self[i] * other[i]

        # vector * constant
        else:
            for i in range(self.item_count):
                self[i] = self[i] * Binary(other)

    def vdiv(self, other: Any):
        # vector // vector
        if type(other) is type(self):
            for i in range(self.item_count):
                self[i] = self[i] // other[i]

        # vector // constant
        else:
            for i in range(self.item_count):
                self[i] = self[i] // Binary(other)

    def vmod(self, other: Any):
        # vector % vector
        if type(other) is type(self):
            for i in range(self.item_count):
                self[i] = self[i] % other[i]

        # vector % constant
        else:
            for i in range(self.item_count):
                self[i] = self[i] % Binary(other)

    # item handling
    def __getitem__(self, index) -> Binary:
        """
        Returns indexed item. Multi-item slices don't work at this time.
        """

        if isinstance(index, int):
            slc = slice(index * self._item_bits, (index + 1) * self._item_bits)
        elif isinstance(index, slice):
            start = index.start if index.start is not None else 0
            stop  = index.stop if index.stop is not None else self.bits
            slc   = slice(start * self._item_bits, abs(stop - start) * self._item_bits)

        return super().__getitem__(slc)

    def __setitem__(self, index, value):
        """
        Modifies indexed item. Multi-item slices don't work at this time.
        """
        if isinstance(index, int):
            slc = slice(index * self._item_bits, (index + 1) * self._item_bits)
        elif isinstance(index, slice):
            start = index.start if index.start is not None else 0
            stop  = index.stop if index.stop is not None else self.bits
            slc   = slice(start * self._item_bits, abs(stop - start) * self._item_bits)

        super().__setitem__(slc, value)


class BinarySignals:
    """
    Interface for converting values read from cocotb.bus to Binary and BinaryVector.
    """

    def __init__(self, parent, *, params: Optional[dict] = {}):
        self.__parent = parent
        self.__params = params

        for sig_name in self.__parent._signals:
            if sig_name in self.__params.keys():
                if not isinstance(self.__params[sig_name], Binary):
                    raise TypeError("Invalid type passed to BinarySignals params.")
            else:
                self.__params[sig_name] = Binary()

    def __getattr__(self, name):
        if name not in self.__params.keys():
            raise KeyError(f"Unknown signal name '{name}'")

        sig = getattr(self.__parent.bus, name)

        if sig is None:
            sig_val = "0"
        else:
            sig_val = sig.value.binstr

        if "U" in sig_val:
            sig_val = "0"

        sig_obj = self.__params[name]
        sig_obj.value = sig_val

        return sig_obj
