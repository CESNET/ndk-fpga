--
-- dec1fn_enable.vhd: Decoder 1 from n with ENABLE
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
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
entity dec1fn_enable is
   generic(
      ITEMS       : integer
   );
   port(
      ADDR        : in std_logic_vector(max(1,log2(ITEMS))-1 downto 0);
      ENABLE      : in std_logic;
      DO          : out std_logic_vector(ITEMS-1 downto 0)
   );
end entity dec1fn_enable;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dec1fn_enable is


begin

fake_gen : if ITEMS=1 generate
   DO(0) <= ENABLE;
end generate;

real_gen : if ITEMS>1 generate
   process(ADDR, ENABLE)
   begin
      DO    <= (others => '0');
      if ENABLE = '1' then
         for i in 0 to (ITEMS-1) loop
            if (conv_std_logic_vector(i, log2(ITEMS)) = ADDR) then
               DO(i) <= '1';
            end if;
         end loop;
      end if;
   end process;
end generate;

end architecture behavioral;
