-- uh_completer.vhd: UH Completer unit for FlowMon
-- Copyright (C) 2007 CESNET
-- Author: Martin Louda <sandin@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- log2 function
use work.math_pack.all;
-- package with FL records
use work.fl_pkg.all;
-- package with LB records
use work.mi32_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity uh_completer is
   generic(
      -- defines completed data size in bytes
      -- allowed values are: 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024
      UH_SIZE  : integer := 64;
      -- erase (fill with zeroes) data from memory after reading it
      -- set to false for debugging purposes (see documentation)
      ERASE    : boolean := true
   );
   port(
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- ==============
      -- Data interface
      -- ==============

      -- HFE output
      DI       : inout t_fl32;
      -- UH header
      DO       : inout t_fl16;

      -- ===================
      -- SW memory interface
      -- ===================

      MI       : inout t_mi32
   );
end entity uh_completer;

-- ------------------------------------------------------------------------
--                        Architecture declaration
-- ------------------------------------------------------------------------
architecture full of uh_completer is

-- ------------------------------------------------------------------------
--                        Architecture body
-- ------------------------------------------------------------------------
begin

   COMPLETER_I: entity work.completer
   generic map(
      DATA_SIZE   => UH_SIZE,
      DATA_WIDTH  => 16,
      ADDR_WIDTH  => 16,
      FL_IN_WIDTH => 32,
      ALIGN_OLD   => true,
      ERASE       => ERASE
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      --
      IN_DATA        => DI.DATA,
      IN_REM         => DI.DREM,
      IN_SOF_N       => DI.SOF_N,
      IN_EOF_N       => DI.EOF_N,
      IN_SOP_N       => DI.SOP_N,
      IN_EOP_N       => DI.EOP_N,
      IN_SRC_RDY_N   => DI.SRC_RDY_N,
      IN_DST_RDY_N   => DI.DST_RDY_N,
      --
      OUT_DATA       => DO.DATA,
      OUT_REM        => DO.DREM,
      OUT_SOF_N      => DO.SOF_N,
      OUT_EOF_N      => DO.EOF_N,
      OUT_SOP_N      => DO.SOP_N,
      OUT_EOP_N      => DO.EOP_N,
      OUT_SRC_RDY_N  => DO.SRC_RDY_N,
      OUT_DST_RDY_N  => DO.DST_RDY_N,
      --
      MI             => MI
   );

   -- ---------------------------------------------------------------------

end architecture full;
