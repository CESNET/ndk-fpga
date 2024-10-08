--
-- cnt.vhd: Fast counter with generic width and direction
-- Copyright (C) 2014 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--            Lukas Kekely <kekely@cesnet.cz>
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

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cnt is
   generic (
      WIDTH : integer := 32;
      DIR   : TCNT := up;
      CLEAR : boolean := false
   );
   port(
      RESET     : in  std_logic;
      CLK       : in  std_logic;
      CE        : in  std_logic;
      CLR       : in  std_logic;
      DO        : out std_logic_vector(WIDTH-1 downto 0)
   );
end entity cnt;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of cnt is

signal reg_cnt   : std_logic_vector(WIDTH-1 downto 0);
signal clear_sig : std_logic := '0';

begin
   clear_gen : if CLEAR generate
      clear_sig <= CLR;
   end generate;

   up_cnt_gen : if DIR=up generate
      cnt : process(CLK)
      begin
         if CLK'event and CLK='1' then
            if RESET='1' or clear_sig='1' then
               reg_cnt <= (others => '0');
            elsif CE='1' then
               reg_cnt <= reg_cnt+1;
            end if;
         end if;
      end process;
   end generate;

   down_cnt_gen : if DIR=down generate
      cnt : process(CLK)
      begin
         if CLK'event and CLK='1' then
            if RESET='1' or clear_sig='1' then
               reg_cnt <= (others => '0');
            elsif CE='1' then
               reg_cnt <= reg_cnt-1;
            end if;
         end if;
      end process;
   end generate;

   DO <= reg_cnt;
end architecture full;

