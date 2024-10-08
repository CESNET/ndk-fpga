-- mi32_pkg.vhd: MI32 interface specification
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

package mi32_pkg is

   -- Universal 32 bit memory interface
   type t_mi32 is record
      DWR      : std_logic_vector(31 downto 0);           -- Input Data
      ADDR     : std_logic_vector(31 downto 0);           -- Address
      RD       : std_logic;                               -- Read Request
      WR       : std_logic;                               -- Write Request
      BE       : std_logic_vector(3  downto 0);           -- Byte Enable
      DRD      : std_logic_vector(31 downto 0);           -- Output Data
      ARDY     : std_logic;                               -- Address Ready
      DRDY     : std_logic;                               -- Data Ready
   end record;

   type t_mi32_array is array (natural range <>) of t_mi32;

end mi32_pkg;

package body mi32_pkg is
end mi32_pkg;
