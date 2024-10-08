-- fl_watch_addr_pkg.vhd: fl_watch address space
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.addr_space.all;

-- ----------------------------------------------------------------------------
--                      FL_WATCH Address Package Declaration
-- ----------------------------------------------------------------------------
package fl_watch_addr_pkg is

   -- Control register
   constant FL_WATCH_CTRL_OFFSET : std_logic_vector(31 downto 0) := X"00000000";
   constant FL_WATCH_CTRL        : std_logic_vector(31 downto 0) :=
                                   FL_WATCH_BASE_ADDR + FL_WATCH_CTRL_OFFSET;

   -- Offset 0x4 is reserved for future use

   -- Offset of first frame counter
   constant FL_WATCH_FCNT0_OFFSET : std_logic_vector(31 downto 0) := X"00000008";
   constant FL_WATCH_FCNT0        : std_logic_vector(31 downto 0) :=
                                   FL_WATCH_BASE_ADDR + FL_WATCH_FCNT0_OFFSET;

   -- Other addresses are generic, see documentation for details.
   -- (Width of one frame counter is generic, number of these counters is generic
   --  and optionally there are also counters of invalid frames.)

end fl_watch_addr_pkg;

package body fl_watch_addr_pkg is
end fl_watch_addr_pkg;
