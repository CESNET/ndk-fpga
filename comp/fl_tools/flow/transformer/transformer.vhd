-- transformer.vhd: Implementation of FrameLink Transformer component.
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of FL_TRANSFORMER is

begin

   -- ---------------------------------------------------------------------
   --                   Main logic
   -- ---------------------------------------------------------------------

   -- data widths are equal
   GEN_ARCH_EQUAL:
   if (RX_DATA_WIDTH = TX_DATA_WIDTH) generate
      TX_DATA        <= RX_DATA;
      TX_REM         <= RX_REM;
      TX_SOF_N       <= RX_SOF_N;
      TX_EOF_N       <= RX_EOF_N;
      TX_SOP_N       <= RX_SOP_N;
      TX_EOP_N       <= RX_EOP_N;
      TX_SRC_RDY_N   <= RX_SRC_RDY_N;
      RX_DST_RDY_N   <= TX_DST_RDY_N;
   end generate;

   -- RX data width > TX data width
   GEN_ARCH_DOWN:
   if (RX_DATA_WIDTH > TX_DATA_WIDTH) generate
      FL_TRANSFORMER_DOWN_U: entity work.FL_TRANSFORMER_DOWN
         generic map(
            RX_DATA_WIDTH  => RX_DATA_WIDTH,
            TX_DATA_WIDTH  => TX_DATA_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            --
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            RX_SOF_N       => RX_SOF_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            --
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM,
            TX_SOF_N       => TX_SOF_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N
         );
   end generate;

   -- RX data width < TX data width
   GEN_ARCH_UP:
   if (RX_DATA_WIDTH < TX_DATA_WIDTH) generate
      FL_TRANSFORMER_UP_U: entity work.FL_TRANSFORMER_UP
         generic map(
            RX_DATA_WIDTH  => RX_DATA_WIDTH,
            TX_DATA_WIDTH  => TX_DATA_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            --
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            RX_SOF_N       => RX_SOF_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            --
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM,
            TX_SOF_N       => TX_SOF_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N
         );
   end generate;

end architecture full;
