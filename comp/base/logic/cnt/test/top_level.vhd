--
-- top_level.vhd: Top Level
-- Copyright (C) 2003 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use WORK.cnt_types.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fpga is
port(
   RESET :  in std_logic;
   CLK   :  in std_logic;

   CE    :  in std_logic;
   LD    :  in std_logic;

   NUM1  :  in std_logic_vector(31 downto 0);
   NUM2  :  in std_logic_vector(31 downto 0);

--   DI    :  in std_logic_vector(31 downto 0);
   DO    : out std_logic_vector(31 downto 0)
);
end entity fpga;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fpga is

   signal do_i    : std_logic_vector(31 downto 0);
   signal ce_i    : std_logic;
   signal reg_ce  : std_logic;
   signal gnd     : std_logic;

begin
   gnd <= '0';
   -- for ilustrating of benefit of fast counter cnt_en signal is delayed
   ce_i <= '1' when (reg_ce='1' and (NUM1=NUM2)) else '0';--reg_ce;--

process(RESET, CLK)
begin
if (RESET = '1') then
      reg_ce <='0';
   elsif (CLK'event AND CLK = '1') then
      reg_ce <= CE;
   end if;
end process;

--process(RESET, CLK)
--begin
--   if (RESET = '1') then
--      do_i <= (others => '0');
--   elsif (CLK'event AND CLK = '1') then
--      if (ce_i='1') then
--         if (LD='1') then
--	    do_i <= (others=>'0');
--	 else
--	    do_i <= do_i + 1;
--         end if;
--      end if;
--   end if;
--end process;

CNT_U: entity work.cnt
generic map(
   WIDTH => 32,
   DIR   => up,
   CLEAR => true
)
port map(
  CLK   => CLK,
  RESET => RESET,
  CE    => ce_i,
  CLR   => LD,
  DO    => DO
);

  DO <= do_i;
end architecture behavioral;

