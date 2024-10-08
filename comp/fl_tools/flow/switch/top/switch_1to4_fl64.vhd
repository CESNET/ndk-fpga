-- switch_1to4_fl64.vhd: 64b FrameLink Switch
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity switch_1to4_fl64 is
   generic(
      -- Switch informationn byte offset
      IFC_BYTE_OFFSET : integer;
      -- Switch information nibble offset: 0 - low; 1 - high
      IFC_NIBBLE_OFFSET : integer
   );
   port(

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      RX             : inout t_fl64;

      -- output interfaces
      TX0            : inout t_fl64;
      TX1            : inout t_fl64;
      TX2            : inout t_fl64;
      TX3            : inout t_fl64

   );
end entity switch_1to4_fl64;

architecture full of switch_1to4_fl64 is
begin

   SWITCH_1TO4_FL64_I: entity work.fl_switch_1to4
   generic map(
      -- FrameLink data width
      FL_DATA_WIDTH => 64,
      -- Switch informationn byte offset
      IFC_BYTE_OFFSET => IFC_BYTE_OFFSET,
      -- Switch information nibble offset: 0 - low; 1 - high
      IFC_NIBBLE_OFFSET => IFC_NIBBLE_OFFSET
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      RX_SOF_N       => RX.SOF_N,
      RX_SOP_N       => RX.SOP_N,
      RX_EOP_N       => RX.EOP_N,
      RX_EOF_N       => RX.EOF_N,
      RX_SRC_RDY_N   => RX.SRC_RDY_N,
      RX_DST_RDY_N   => RX.DST_RDY_N,
      RX_DATA        => RX.DATA,
      RX_REM         => RX.DREM,

      -- output interfaces
      TX0_SOF_N      => TX0.SOF_N,
      TX0_SOP_N      => TX0.SOP_N,
      TX0_EOP_N      => TX0.EOP_N,
      TX0_EOF_N      => TX0.EOF_N,
      TX0_SRC_RDY_N  => TX0.SRC_RDY_N,
      TX0_DST_RDY_N  => TX0.DST_RDY_N,
      TX0_DATA       => TX0.DATA,
      TX0_REM        => TX0.DREM,

      TX1_SOF_N      => TX1.SOF_N,
      TX1_SOP_N      => TX1.SOP_N,
      TX1_EOP_N      => TX1.EOP_N,
      TX1_EOF_N      => TX1.EOF_N,
      TX1_SRC_RDY_N  => TX1.SRC_RDY_N,
      TX1_DST_RDY_N  => TX1.DST_RDY_N,
      TX1_DATA       => TX1.DATA,
      TX1_REM        => TX1.DREM,

      TX2_SOF_N      => TX2.SOF_N,
      TX2_SOP_N      => TX2.SOP_N,
      TX2_EOP_N      => TX2.EOP_N,
      TX2_EOF_N      => TX2.EOF_N,
      TX2_SRC_RDY_N  => TX2.SRC_RDY_N,
      TX2_DST_RDY_N  => TX2.DST_RDY_N,
      TX2_DATA       => TX2.DATA,
      TX2_REM        => TX2.DREM,

      TX3_SOF_N      => TX3.SOF_N,
      TX3_SOP_N      => TX3.SOP_N,
      TX3_EOP_N      => TX3.EOP_N,
      TX3_EOF_N      => TX3.EOF_N,
      TX3_SRC_RDY_N  => TX3.SRC_RDY_N,
      TX3_DST_RDY_N  => TX3.DST_RDY_N,
      TX3_DATA       => TX3.DATA,
      TX3_REM        => TX3.DREM
   );

end architecture full;

