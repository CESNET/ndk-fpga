-- watch_arch_norec_empty.vhd: Empty FL_WATCH_NOREC architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--	      Jan Stourac <xstour03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 and min functions
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture empty of FL_WATCH_NOREC is

   signal gnd_vect : std_logic_vector(6*INTERFACES+2*32+4+4-1 downto 0);

begin

   -- inputs grounded
   gnd_vect <= CLK
             & RESET
             & SOF_N
             & EOF_N
             & SOP_N
             & EOP_N
             & DST_RDY_N
             & SRC_RDY_N
             & MI_DWR
             & MI_ADDR
             & MI_RD
             & MI_WR
             & MI_BE;

   -- outputs inactive
   FRAME_ERR <= (others => '0');
   MI_DRD    <= (others => 'X');
   MI_ARDY   <= '0';
   MI_DRDY   <= '0';

end architecture empty;
