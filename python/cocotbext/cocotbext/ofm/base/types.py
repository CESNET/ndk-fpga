# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.types import Array, LogicArray, Range
from typing import Optional


class LogicArray2D(Array):
    """
    A two-dimensional array of LogicArray items.

    The first dimension represents the number of items, the second dimension
    represents the width of each item. Supports convenient construction using
    the syntax ``LogicArray2D(array_range)(la_range)``.
    """

    def __new__(cls, array_range: int | Range, la_range: Optional[int | Range] = None):
        """
        Enable the two-step construction syntax ``LogicArray2D(Range | int)(Range | int)``.

        When called with a single argument, returns a factory that accepts the
        inner range and creates the final ``LogicArray2D`` instance.
        """
        if la_range is None:
            return lambda la_range: LogicArray2D(array_range, la_range)

        if isinstance(array_range, int):
            array_range = Range(array_range - 1, "downto", 0)
        if isinstance(la_range, int):
            la_range = Range(la_range - 1, "downto", 0)

        # handle nil length array
        if len(array_range) <= 0 or len(la_range) <= 0:
            return None

        return super().__new__(cls)

    def __init__(self, array_range: int | Range, la_range: Optional[int | Range] = None):
        """Initialize the 2D array with the given outer and inner ranges."""
        if isinstance(array_range, int):
            array_range = Range(array_range - 1, "downto", 0)
        if isinstance(la_range, int):
            la_range = Range(la_range - 1, "downto", 0)

        self._item_range: Range = la_range

        items = [LogicArray(0, la_range) for _ in range(len(array_range))]
        super().__init__(items, array_range)

    @property
    def item_range(self) -> int:
        """Return the ``Range`` of the inner ``LogicArray`` items."""
        return self._item_range

    def serialize(self) -> LogicArray:
        """Concatenate all inner ``LogicArray`` items into a single large ``LogicArray``."""
        direction = self.range.direction
        item_width = len(self._item_range)

        if direction == "downto":
            la_range = Range(len(self.range) * item_width - 1, "downto", 0)
        else:
            la_range = Range(0, "to", len(self.range) * item_width - 1)

        logic_array = LogicArray(0, la_range)

        if direction == "downto":
            for i in range(len(self)):
                logic_array[(i + 1) * item_width - 1 : i * item_width] = self[i]
        else:
            for i in range(len(self)):
                logic_array[i * item_width : (i + 1) * item_width - 1] = self[i]

        return logic_array

    def deserialize(self, logic_array: LogicArray) -> None:
        """
        Fill the inner ``LogicArray`` items with values from a flat ``LogicArray``.

        The input ``LogicArray`` is split into chunks according to the width of
        the inner items.
        """
        assert len(logic_array) % len(self) == 0, f"LogicArray of length {len(logic_array)} does not fit into {items} items."

        item_width = len(self._item_range)

        if logic_array.range.direction == "downto":
            for i in range(len(self)):
                self[i][:] = logic_array[(i + 1) * item_width - 1 : i * item_width]

        else:
            for i in range(len(self)):
                self[i][:] = logic_array[i * item_width : (i + 1) * item_width - 1]

    @classmethod
    def from_logicarray(logic_array: LogicArray, items: Optional[int] = None, direction: str = "auto") -> "LogicArray2D":
        """
        Create a ``LogicArray2D`` from a flat ``LogicArray``.

        Similar to :meth:`deserialize`, but creates and returns a new
        ``LogicArray2D`` instance. The ``direction`` parameter controls the
        direction of the outer range: ``"auto"`` inherits the direction from
        the input ``LogicArray``, while ``"downto"`` and ``"to"`` force the
        corresponding direction.
        """
        # checking the validity of the arguments
        assert len(logic_array) % items == 0, f"LogicArray of length {len(logic_array)} does not fit into {items} items."
        assert direction in ["auto", "downto", "to"], f"Deserialization direction must be 'auto', 'downto' or 'to', not '{direction}'."

        la_range: Range = logic_array.range

        # get direction from the original logic array
        if direction == "auto":
            direction = la_range.direction

        if direction == "downto":
            array_range = Range(items - 1, "downto", 0)
        else:
            array_range = Range(0, "to", items - 1)

        la2d = LogicArray2D(array_range)(la_range)

        la2d.deserialize(logic_array)

        return la2d
