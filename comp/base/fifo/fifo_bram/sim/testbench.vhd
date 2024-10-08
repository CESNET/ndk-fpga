--
-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor xpusvi00@stud.fit.vutbr.cz
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_WIDTH  : integer   := 18;
   constant clkper      : time      := 10 ns;

   signal clk      : std_logic;
   signal reset    : std_logic;
   signal wr       : std_logic;
   signal di       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal full     : std_logic;
   signal lstblk   : std_logic;
   signal rd       : std_logic;
   signal do       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal dv       : std_logic;



-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.fifo_bram
generic map(
   ITEMS       => 16,
   BLOCK_SIZE  => 4,
   DATA_WIDTH  => TEST_WIDTH
)
port map(
   CLK      => clk,
   RESET    => reset,

   -- Write interface
   WR       => wr,
   DI       => di,
   FULL     => full,
   LSTBLK   => lstblk,

   -- Read interface
   RD       => rd,
   DO       => do,
   DV       => dv
);

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
   reset <= '1';
   rd    <= '0';
   wr    <= '0';
   di    <= (others => '0');

   wait for 4*clkper;
   reset <= '0';

   wait for 20*clkper;
   wait for 2 ns;

   -- fill fifo
   wr    <= '1';
   for i in 1 to 20 loop
      di    <= conv_std_logic_vector(i, di'length);
      wait for clkper;
   end loop;
   wr    <= '0';

   wait for 10*clkper;

   -- two cycles of reading will result in one data output
   rd    <='1';
   wait for clkper;
   rd    <='0';
   wait for 10*clkper;
   rd    <='1';
   wait for clkper;
   rd    <='0';
   wait for 10*clkper;

   -- empty fifo
   rd    <= '1';
   for i in 1 to 14 loop
      wait for clkper;
   end loop;
   rd    <= '0';

   -- final part is interesting
   wait for clkper;
   rd    <= '1';
   wait for clkper;
   rd    <= '0';

   wait for clkper;
   rd    <= '1';
   wait for clkper;
   rd    <= '0';


   wait for 20*clkper;
   -- write ...
   wr    <= '1';
   for i in 1 to 8 loop
      di    <= conv_std_logic_vector(i, di'length);
      wait for clkper;
   end loop;
   -- ... and read at once
   rd    <= '1';
   for i in 9 to 20 loop
      di    <= conv_std_logic_vector(i, di'length);
      wait for clkper;
   end loop;

   wr    <= '0';
   wait for 10*clkper;

   rd    <= '0';
   wr    <= '0';

   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
