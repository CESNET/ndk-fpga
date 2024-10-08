-- transformer_empty.vhd: Empty architecture of FrameLink Transformer
-- component.
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
architecture empty of FL_TRANSFORMER is

signal empty_sig  : std_logic_vector(8+RX_DATA_WIDTH+log2(RX_DATA_WIDTH/8)-1 downto 0);

begin
   empty_sig <=   CLK   & -- 1
                  RESET & -- 1 = 2
                  --
                  RX_DATA        & -- RX_DATA_WIDTH
                  RX_REM         & -- log2(RX_DATA_WIDTH/8)
                  RX_SOF_N       & -- 1
                  RX_EOF_N       & -- 1
                  RX_SOP_N       & -- 1
                  RX_EOP_N       & -- 1
                  RX_SRC_RDY_N   & -- 1 = 5 + RX_DATA_WIDTH + log2(RX_DATA_WIDTH/8)
                  --
                  TX_DST_RDY_N; -- 1 = 1
                  --------------------
                  -- = 8 + RX_DATA_WIDTH + log2(RX_DATA_WIDTH/8)

   RX_DST_RDY_N   <= 'Z';
   --
   TX_DATA        <= (others => 'Z');
   TX_REM         <= (others => 'Z');
   TX_SOF_N       <= 'Z';
   TX_EOF_N       <= 'Z';
   TX_SOP_N       <= 'Z';
   TX_EOP_N       <= 'Z';
   TX_SRC_RDY_N   <= 'Z';

end architecture empty;
