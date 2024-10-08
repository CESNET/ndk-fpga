--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

entity CNT_TRAN is
   generic (
      CNT_WIDTH   : integer := 10
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;
      ADD_TR      : in std_logic;
      ADD_RDY     : in std_logic;
      RM_TR       : in std_logic;
      RM_RDY      : in std_logic;
      TRANS_NUM   : out std_logic_vector(CNT_WIDTH-1 downto 0)
   );
end entity;

architecture FULL of CNT_TRAN is
   signal cnt_up     : std_logic;
   signal cnt_down   : std_logic;
   signal cnt_value  : std_logic_vector(CNT_WIDTH-1 downto 0);
begin

   cnt_up <= ADD_TR and ADD_RDY;
   cnt_down <= RM_TR and RM_RDY;
   TRANS_NUM <= cnt_value;

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if RESET = '1' then
            cnt_value <= (others => '0');
         else
            if(cnt_up = '1' and cnt_down = '0') then
               cnt_value <= cnt_value + 1;
            end if;
            if(cnt_up = '0' and cnt_down = '1') then
               cnt_value <= cnt_value - 1;
            end if;
         end if;
      end if;
   end process;

end architecture;
