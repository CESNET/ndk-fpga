-- fl_pkg.vhd: FrameLink Package
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        FrameLink Package
-- ----------------------------------------------------------------------------
package fl_pkg is

   -- FrameLink - data width 8 - no DREM signal
   type t_fl8 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic;
      DATA        : std_logic_vector(7 downto 0);
   end record;

   -- FrameLink - data width 16
   type t_fl16 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic;
      DATA        : std_logic_vector(15 downto 0);
      DREM        : std_logic_vector(0 downto 0);
   end record;

   -- FrameLink - data width 32
   type t_fl32 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic;
      DATA        : std_logic_vector(31 downto 0);
      DREM        : std_logic_vector(1 downto 0);
   end record;

   -- FrameLink - data width 64
   type t_fl64 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic;
      DATA        : std_logic_vector(63 downto 0);
      DREM        : std_logic_vector(2 downto 0);
   end record;

   -- FrameLink - data width 128
   type t_fl128 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic;
      DATA        : std_logic_vector(127 downto 0);
      DREM        : std_logic_vector(3 downto 0);
   end record;

   -- FrameLink - data width 256
   type t_fl256 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic;
      DATA        : std_logic_vector(255 downto 0);
      DREM        : std_logic_vector(4 downto 0);
   end record;

end fl_pkg;


-- ----------------------------------------------------------------------------
--                        FrameLink Package
-- ----------------------------------------------------------------------------
package body fl_pkg is

end fl_pkg;

