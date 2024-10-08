-- switch_empty.vhd: FrameLink 1-N switch empty architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture empty of fl_switch_1toN is
begin

   CLK   => open,
   RESET => open,

   RX_DATA  => open,
   RX_REM   => open,
   RX_SOF_N => open,
   RX_EOF_N => open,
   RX_SOP_N => open,
   RX_EOP_N => open,
   RX_SRC_RDY_N   => '1',
   RX_DST_RDY_N   => open,

   TX_DATA  => (others => 'X'),
   TX_REM   => (others => 'X'),
   TX_SOF_N => (others => 'X'),
   TX_EOF_N => (others => 'X'),
   TX_SOP_N => (others => 'X'),
   TX_EOP_N => (others => 'X'),
   TX_SRC_RDY_N   => (others => '1'),
   TX_DST_RDY_N   => open,

end architecture;

