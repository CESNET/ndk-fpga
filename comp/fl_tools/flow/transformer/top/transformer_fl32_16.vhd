-- transformer_fl32_16.vhd: 16-bit -> 32bit FrameLink cover of FL_TRANSFORMER
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id:$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- package with FL records
use work.fl_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FL_TRANSFORMER_FL32_16 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      RX             : inout t_fl32;
      TX             : inout t_fl16
   );
end entity FL_TRANSFORMER_FL32_16;

architecture full of FL_TRANSFORMER_FL32_16 is
begin

   FL_TRANSFORMER : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH  => 32,
         TX_DATA_WIDTH  => 16
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- RX interface
         RX_DATA        => RX.DATA,
         RX_REM         => RX.DREM,
         RX_SOF_N       => RX.SOF_N,
         RX_EOF_N       => RX.EOF_N,
         RX_SOP_N       => RX.SOP_N,
         RX_EOP_N       => RX.EOP_N,
         RX_SRC_RDY_N   => RX.SRC_RDY_N,
         RX_DST_RDY_N   => RX.DST_RDY_N,
         -- TX interface
         TX_DATA        => TX.DATA,
         TX_REM         => TX.DREM,
         TX_SOF_N       => TX.SOF_N,
         TX_EOF_N       => TX.EOF_N,
         TX_SOP_N       => TX.SOP_N,
         TX_EOP_N       => TX.EOP_N,
         TX_SRC_RDY_N   => TX.SRC_RDY_N,
         TX_DST_RDY_N   => TX.DST_RDY_N
      );

end architecture full;

