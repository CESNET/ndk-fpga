-- hins_empty.vhd
--!
--! \file
--! \brief FLU header insert empty architecture
--! \author Lukas Kekely <kekely@cesnet.cz>
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

--! \name  FLU header insert empty architecture
architecture empty of HINS is

begin

   RX_DST_RDY <= '1';

   HDR_NEXT   <= '1';

   TX_DATA <= (others => '0');
   TX_SOP_POS <= (others => '0');
   TX_EOP_POS <= (others => '0');
   TX_SOP <= '0';
   TX_EOP <= '0';
   TX_SRC_RDY <= '1';

end architecture empty;

