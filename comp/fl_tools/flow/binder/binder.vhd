-- binder.vhd: FrameLink Binder top architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- Binder declarations
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_BINDER is
begin

   -- generate SIMPLE Binder
   GEN_SIMPLE_BINDER: if SIMPLE_BINDER and not STUPID_BINDER generate
      FL_BINDER : entity work.FL_BINDER_SIMPLE
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            FRAME_PARTS    => FRAME_PARTS,
            QUEUE_CHOOSING => QUEUE_CHOOSING
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX_SOF_N       => RX_SOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            -- output FrameLink interface
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;


   -- generate STUPID Binder
   GEN_STUPID_BINDER: if STUPID_BINDER and not SIMPLE_BINDER generate
      FL_BINDER : entity work.FL_BINDER_STUPID
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            FRAME_PARTS    => FRAME_PARTS
            -- QUEUE_CHOOSING => QUEUE_CHOOSING
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX_SOF_N       => RX_SOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            -- output FrameLink interface
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;

   -- generate NFIFO2FIFO Binder
   GEN_NFIFO2FIFO_BINDER: if not SIMPLE_BINDER and not STUPID_BINDER  generate
      FL_BINDER : entity work.FL_BINDER_NFIFO2FIFO
         generic map(
            INPUT_WIDTH    => INPUT_WIDTH,
            INPUT_COUNT    => INPUT_COUNT,
            OUTPUT_WIDTH   => OUTPUT_WIDTH,
            LUT_MEMORY     => LUT_MEMORY,
            LUT_BLOCK_SIZE => LUT_BLOCK_SIZE,
            FRAME_PARTS    => FRAME_PARTS,
            QUEUE_CHOOSING => QUEUE_CHOOSING
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input FrameLink interface
            RX_SOF_N       => RX_SOF_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_EOF_N       => RX_EOF_N,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_DATA        => RX_DATA,
            RX_REM         => RX_REM,
            -- output FrameLink interface
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N,
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM
         );
   end generate;

end architecture full;
