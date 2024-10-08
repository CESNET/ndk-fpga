-- fifo_arch_full.vhd: Frame Link protocol generic FIFO (empty architecture)
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

architecture empty of FL_FIFO is

signal empty_sig : std_logic_vector(8+DATA_WIDTH+log2(DATA_WIDTH/8)-1 downto 0);

begin
   -- Input and In/Out signals
   empty_sig <=  CLK            &  --   1
                 RESET          &  --   1
                 RX_DATA        &  --     DATA_WIDTH
                 RX_REM         &  --     log2(DATA_WIDTH/8)
                 RX_SOP_N       &  --   1
                 RX_EOP_N       &  --   1
                 RX_SOF_N       &  --   1
                 RX_EOF_N       &  --   1
                 RX_SRC_RDY_N   &  --   1
                 TX_DST_RDY_N;     --   1
                 -------------------------------------------
                                   --   8 + DATA_WDTH + log2(DATA_WIDTH/8)

   RX_DST_RDY_N <= '1';
   TX_DATA     <= (others => '0');
   TX_REM      <= (others => '0');
   TX_SRC_RDY_N <= '1';
   TX_SOP_N    <= '1';
   TX_EOP_N    <= '1';
   TX_SOF_N    <= '1';
   TX_EOF_N    <= '1';
   LSTBLK      <= '0';
   FULL        <= '0';
   EMPTY       <= '0';
   STATUS      <= (others => '0');

end architecture empty;
