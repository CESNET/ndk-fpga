  --
-- dec1fn.vhd: Decoder 1 from n
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dec1fn is
   generic(
      ITEMS       : integer := 8
   );
   port(
      ADDR        : in  std_logic_vector(max(1,log2(ITEMS))-1 downto 0);
      DO          : out std_logic_vector(ITEMS-1 downto 0)
   );
end entity dec1fn;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dec1fn is


begin

fake_gen : if ITEMS=1 generate
   DO(0) <= '1';
end generate;

real_gen : if ITEMS>1 generate
   process(ADDR)
   begin
      DO    <= (others => '0');
      for i in 0 to (ITEMS-1) loop
         if (conv_std_logic_vector(i, log2(ITEMS)) = ADDR) then
            DO(i) <= '1';
         end if;
      end loop;
   end process;
end generate;

end architecture behavioral;

