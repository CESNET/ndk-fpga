-- binder_empty.vhd: FrameLink Binder empty architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture empty of FL_BINDER is

   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig : std_logic_vector(3 + 5*INPUT_COUNT +
   INPUT_COUNT*INPUT_WIDTH + INPUT_COUNT*log2(INPUT_WIDTH/8)-1 downto 0);

begin
   empty_sig <= CLK              & -- 1
                RESET            & -- 1
                RX_SOF_N         & -- INPUT_COUNT
                RX_SOP_N         & -- INPUT_COUNT
                RX_EOP_N         & -- INPUT_COUNT
                RX_EOF_N         & -- INPUT_COUNT
                RX_SRC_RDY_N     & -- INPUT_COUNT
                RX_DATA          & -- INPUT_COUNT*INPUT_WIDTH
                RX_REM           & -- INPUT_COUNT*log2(INPUT_WIDTH/8)
                TX_DST_RDY_N;      -- 1
                -- --------------------------------------------
                -- 3 + 5*INPUT_WIDTH + INPUT_COUNT*INPUT_WIDTH +
                -- + INPUT_COUNT*log2(INPUT_WIDTH/8)

   -- output signals
   RX_DST_RDY_N   <= (others => '0');
   TX_SOF_N       <= '1';
   TX_SOP_N       <= '1';
   TX_EOP_N       <= '1';
   TX_EOF_N       <= '1';
   TX_SRC_RDY_N   <= '1';
   TX_DATA        <= (others => '0');
   TX_REM         <= (others => '0');

end architecture empty;
