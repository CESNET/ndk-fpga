-- hins_plus_empty.vhd
--!
--! \file
--! \brief FLU plus header insert empty architecture
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! \name  FLU plus header insert empty architecture
architecture empty of HINS_PLUS is

begin

   RX_DST_RDY <= '1';

   HDR_NEXT   <= '1';

   TX_DATA <= (others => '0');
   TX_CHANNEL <= (others => '0');
   TX_SOP_POS <= (others => '0');
   TX_EOP_POS <= (others => '0');
   TX_SOP <= '0';
   TX_EOP <= '0';
   TX_SRC_RDY <= '1';

end architecture empty;

