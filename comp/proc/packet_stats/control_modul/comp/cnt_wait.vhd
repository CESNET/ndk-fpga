-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity CNT_WAIT is
   generic(
      CNT_WIDTH : integer := 10
   );
   port(
      CLK       : in  std_logic;
      RESET     : in  std_logic;
      TR_NUM    : in  std_logic_vector(CNT_WIDTH-1 downto 0);
      TR_RDY    : in  std_logic;
      CNT_END   : out std_logic
   );
end entity;

architecture FULL of CNT_WAIT is
   signal cnt_value : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal cnt_zero  : std_logic;
begin

   cnt_zero <= '1' when cnt_value = conv_std_logic_vector(0, CNT_WIDTH) else
               '0';

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if RESET = '1' then
            cnt_value <= (others => '0');
         else
            if(TR_RDY = '1') then
               cnt_value <= TR_NUM;
            elsif(cnt_zero = '0') then
               cnt_value <= cnt_value - 1;
            end if;
         end if;
      end if;
   end process;

   CNT_END <= '0' when TR_RDY = '1' or cnt_zero = '0' else
              '1';

end architecture;

