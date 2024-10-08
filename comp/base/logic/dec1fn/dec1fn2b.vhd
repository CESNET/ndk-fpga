--
-- dec1fn_enable.vhd: Decoder 1 from n with ENABLE
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dec1fn2b is
   generic(
      ITEMS       : integer := 8
   );
   port(
      ADDR        : out std_logic_vector(log2(ITEMS)-1 downto 0);
      ENABLE      : in std_logic;
      DI          : in std_logic_vector(ITEMS-1 downto 0)
   );
end entity dec1fn2b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dec1fn2b is


begin

process(DI, ENABLE)
begin
   ADDR  <= (others => '0');
   if ENABLE = '1' then
      for i in 0 to (ITEMS-1) loop
         if (DI(i) = '1') then
            ADDR <= conv_std_logic_vector(i, log2(ITEMS));
         end if;
      end loop;
   end if;
end process;

end architecture behavioral;

