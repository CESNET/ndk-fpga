# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

"""Address range tracker to prevent overlapping memory accesses."""

from typing import List, Tuple, Optional, Dict
from random import randint


class AddressRangeTracker:
    """
    Tracks address ranges that are currently in use (written to RAM but not yet read).
    Ensures new address allocations don't overlap with existing ranges.

    Supports tracking by packet ID, allowing ranges to be freed when complete
    packets are received rather than individual PCIe responses.
    """

    def __init__(self, max_addr: int):
        """
        Args:
            max_addr: Maximum valid address
        """
        self.max_addr = max_addr
        # List of (start_addr, end_addr) tuples representing in-use ranges
        # end_addr is exclusive (i.e., range is [start, end))
        self.in_use_ranges: List[Tuple[int, int]] = []
        # Map packet ID to (start_addr, length) for tracking by ID
        self._range_by_id: Dict[int, Tuple[int, int]] = {}

    def add_range(self, start: int, length: int, pkt_id: int = None, allow_wrap: bool = False) -> bool:
        """
        Add a new address range to track.

        Args:
            start: Starting address
            length: Length of the range in bytes
            pkt_id: Optional packet ID to associate with this range for later removal
            allow_wrap: If True, the range can wrap around from end to beginning

        Returns:
            True if range was added successfully, False if it overlaps with existing range
        """
        end = start + length

        # Check for overlap with existing ranges
        # For wrap-around ranges, we need to check both the high and low parts
        for existing_start, existing_end in self.in_use_ranges:
            if self._ranges_overlap_wrap(start, end, existing_start, existing_end, allow_wrap):
                return False

        self.in_use_ranges.append((start, end))
        if pkt_id is not None:
            self._range_by_id[pkt_id] = (start, length)
        return True

    def remove_range(self, start: int, length: int) -> bool:
        """
        Remove an address range from tracking (when read is complete).

        Args:
            start: Starting address
            length: Length of the range in bytes

        Returns:
            True if range was found and removed, False otherwise
        """
        end = start + length
        target = (start, end)

        if target in self.in_use_ranges:
            self.in_use_ranges.remove(target)
            return True
        return False

    def remove_range_by_id(self, pkt_id: int) -> bool:
        """
        Remove an address range by packet ID.

        This is used when a complete packet is received on the response interface,
        which may consist of multiple PCIe read completions.

        Args:
            pkt_id: Packet ID associated with the range

        Returns:
            True if range was found and removed, False otherwise
        """
        if pkt_id not in self._range_by_id:
            return False

        start, length = self._range_by_id.pop(pkt_id)
        return self.remove_range(start, length)

    def find_non_overlapping_address(self, length: int, max_attempts: int = 1000, allow_wrap: bool = False) -> Optional[int]:
        """
        Find a random address that doesn't overlap with any in-use range.

        Args:
            length: Required length of the range
            max_attempts: Maximum number of random attempts before giving up
            allow_wrap: If True, allow addresses that wrap around from end to beginning

        Returns:
            A valid starting address or None if no space available
        """
        if length > self.max_addr:
            raise ValueError(f"Requested length ({length}) is greater than the whole address range ({self.max_addr}).")

        for _ in range(max_attempts):
            # Generate random address
            if allow_wrap:
                # Allow any address from 0 to max_addr-1
                addr = randint(0, self.max_addr - 1)
            else:
                # Current behavior: only addresses that don't wrap
                addr = randint(0, self.max_addr - length)

            end = addr + length

            # Check if it overlaps with any in-use range
            overlaps = False
            for existing_start, existing_end in self.in_use_ranges:
                if self._ranges_overlap_wrap(addr, end, existing_start, existing_end, allow_wrap):
                    overlaps = True
                    break

            if not overlaps:
                return addr

        return None

    def _ranges_overlap(self, start1: int, end1: int, start2: int, end2: int) -> bool:
        """
        Check if two ranges overlap.
        Ranges are [start, end) - inclusive start, exclusive end.
        """
        return start1 < end2 and start2 < end1

    def _ranges_overlap_wrap(self, start1: int, end1: int, start2: int, end2: int, allow_wrap: bool) -> bool:
        """
        Check if two ranges overlap, with optional wrap-around support.

        Args:
            start1, end1: First range [start1, end1)
            start2, end2: Second range [start2, end2)
            allow_wrap: If True, handle wrap-around ranges correctly

        Returns:
            True if ranges overlap, False otherwise
        """
        if not allow_wrap:
            # Standard overlap check
            return self._ranges_overlap(start1, end1, start2, end2)

        # With wrap-around, a range can span across max_addr boundary
        # We need to check if either range wraps around

        # Normalize ranges to be within [0, max_addr)
        # A range wraps if end > max_addr
        wraps1 = end1 > self.max_addr
        wraps2 = end2 > self.max_addr

        if not wraps1 and not wraps2:
            # Neither wraps - standard overlap check
            return self._ranges_overlap(start1, end1, start2, end2)

        if wraps1 and wraps2:
            # Both wrap - they overlap if their "wrapped parts" overlap
            # Wrapped part of range 1: [0, end1 % max_addr) and [start1 % max_addr, max_addr)
            # But since both wrap, we check if the non-wrapped portions don't cover everything
            # Actually, if both wrap, they always overlap (they both cover the middle)
            # unless one is completely contained in the other's "hole"
            # The "hole" of a wrapped range is [end1 % max_addr, start1 % max_addr)
            # This is complex - let's simplify by checking if the ranges together don't cover everything

            # Simpler approach: check if there's any gap in either range
            # Range 1 covers: [start1, max_addr) U [0, end1 - max_addr)
            # Range 2 covers: [start2, max_addr) U [0, end2 - max_addr)
            # They don't overlap only if one's covered area is completely outside the other's

            # Actually, if both wrap, they always overlap because they both include
            # addresses near max_addr and addresses near 0
            return True

        # One wraps, one doesn't
        if wraps1:
            # Range 1 wraps: [start1, max_addr) U [0, end1 - max_addr)
            # Range 2 doesn't wrap: [start2, end2)
            # They don't overlap if range2 is completely in the "hole" of range1
            # Hole of range1: [end1 - max_addr, start1)
            hole_start = end1 - self.max_addr
            hole_end = start1
            # Range2 doesn't overlap with wrapped range1 if it's entirely in the hole
            if start2 >= hole_start and end2 <= hole_end:
                return False
            return True

        else:  # wraps2
            # Range 2 wraps: [start2, max_addr) U [0, end2 - max_addr)
            # Range 1 doesn't wrap: [start1, end1)
            # Same logic as above, just swap
            hole_start = end2 - self.max_addr
            hole_end = start2
            if start1 >= hole_start and end1 <= hole_end:
                return False
            return True

    def is_range_available(self, start: int, length: int, allow_wrap: bool = False) -> bool:
        """
        Check if a range is available (doesn't overlap with any in-use range).

        Args:
            start: Starting address
            length: Length of the range
            allow_wrap: If True, handle wrap-around ranges correctly

        Returns:
            True if range is available, False otherwise
        """
        end = start + length
        for existing_start, existing_end in self.in_use_ranges:
            if self._ranges_overlap_wrap(start, end, existing_start, existing_end, allow_wrap):
                return False
        return True

    def __len__(self) -> int:
        """Return the number of tracked ranges."""
        return len(self.in_use_ranges)
