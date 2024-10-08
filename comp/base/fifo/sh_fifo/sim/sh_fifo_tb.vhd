--
-- sh_fifo_tb.vhd: Testbench for Shift-registers FIFO
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Mikusek <petr.mikusek@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant FIFO_WIDTH  : integer   := 32;
   constant FIFO_DEPTH  : integer   := 4;
   constant USE_INREG   : boolean   := true;
   constant USE_OUTREG  : boolean   := true;

   constant clkper      : time      := 10 ns;

   -- ------------------ Signals declaration ----------------------------------
   signal clk           : std_logic;
   signal reset         : std_logic;

   -- write interface
   signal din           : std_logic_vector(FIFO_WIDTH-1 downto 0)
                        := (others => '0');
   signal we            : std_logic := '0';
   signal full          : std_logic;

   -- read interface
   signal dout          : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal re            : std_logic := '0';
   signal empty         : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut : entity work.sh_fifo
      generic map (
         FIFO_WIDTH     => FIFO_WIDTH,
         FIFO_DEPTH     => FIFO_DEPTH,
         USE_INREG      => USE_INREG,
         USE_OUTREG     => USE_OUTREG
      )
      port map (
         CLK      => clk,
         RESET    => reset,

         -- write interface
         DIN      => din,
         WE       => we,
         FULL     => full,

         -- read interface
         DOUT     => dout,
         RE       => re,
         EMPTY    => empty
      );

-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- Data input generator (counter)
dingen : process
begin
   din <= din + 1 after 0.1*clkper;
   wait for clkper;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
begin
   reset <= '1';

   we <= '0';
   re <= '0';

   wait for 16.1*clkper;
   reset <= '0';

   wait for clkper;

   -- write until full
   we <= '1';
   wait until full = '1';
   wait for 1.1*clkper;
   we <= '0';

   wait for clkper;

   -- read until empty
   re <= '1';
   wait until empty = '1';
   wait for 1.1*clkper;
   re <= '0';

   wait for clkper;

   -- write always and read intermittently until full
   we <= '1';
   re <= '1';
   wait for clkper;
   while true loop
      re <= not re;
      wait for clkper;
      if (full = '1') then
         exit;
      end if;
   end loop;

   we <= '0';
   re <= '0';
   wait for clkper;

   -- read always and write intermittently until empty
   re <= '1';
   we <= '0';
   wait for clkper;
   while true loop
      we <= not we;
      wait for clkper;
      if (empty = '1') then
         exit;
      end if;
   end loop;

   -- read out possible hanging data in pipeline
   we <= '0';
   re <= '1';
   wait until empty = '1';
   wait for 1.1*clkper;
   re <= '0';

   wait;
end process;

end architecture behavioral;
