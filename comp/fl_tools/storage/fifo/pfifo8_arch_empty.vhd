-- pfifo8_arch_full.vhd: á bit Frame Link protocol generic packet FIFO (empty architecture)
-- Copyright (C) 2007 CESNET
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

architecture empty of FL_PFIFO8 is

signal empty_sig : std_logic_vector(9+8-1 downto 0);

begin
   -- Input and In/Out signals
   empty_sig <=  CLK            &  --   1
                 RESET          &  --   1
                 RX_DATA        &  --   8
                 RX_SOP_N       &  --   1
                 RX_EOP_N       &  --   1
                 RX_SOF_N       &  --   1
                 RX_EOF_N       &  --   1
                 RX_SRC_RDY_N   &  --   1
                 TX_DST_RDY_N   &  --   1
                 DISCARD;          --   1
                 -------------------------------------------
                                   --   9 + 8

   RX_DST_RDY_N <= '1';
   TX_DATA     <= (others => '0');
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
