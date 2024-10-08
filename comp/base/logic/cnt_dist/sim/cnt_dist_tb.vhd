--
-- cnt_dist_tb.vhd: Testbench for array of counters in distram
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;

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
constant WIDTH : integer := 4;
constant COUNT : integer := 5;

signal clk     : std_logic;
signal reset   : std_logic;
signal flag    : std_logic_vector(COUNT-1 downto 0);
signal flag_dv : std_logic;
signal clr     : std_logic;
signal addr    : std_logic_vector(LOG2(COUNT)-1 downto 0);
signal do      : std_logic_vector(WIDTH-1 downto 0);
signal rdy     : std_logic;

begin

uut : entity work.cnt_dist
generic map(
   WIDTH        => WIDTH,
   COUNT        => COUNT
)
port map(
   RESET   => reset,
   CLK     => clk,
   FLAG    => flag,
   FLAG_DV => flag_dv,
   CLR     => clr,
   ADDR    => addr,
   DO      => do,
   RDY     => rdy
);

clk_p : process
begin
   clk <= '1';
   wait for 4 ns;
   clk <= '0';
   wait for 4 ns;
end process;

-- main testbench process
tb : process
begin
   -- reset counter
   reset   <= '1';
   flag    <= (others=>'0');
   flag_dv <= '0';
   clr     <= '0';
   addr    <= (others=>'0');
   wait for 50 ns;
   reset <= '0';

   -- increase counter 4, 1 and 0
   wait until (clk'event and clk='1');
   flag    <= "10011";
   flag_dv <= '1';
   wait until (clk'event and clk='1');
   flag_dv <= '0';
   -- wait until unit is ready
   wait until rdy='1';--(clk'event and clk='1' and

   -- increase cnt 4 (takes only 1 period)
   flag    <= "10000";
   flag_dv <= '1';
   wait until (clk'event and clk='1');
   flag_dv <= '0';
   -- wait until unit is ready
   wait until rdy='1';--(clk'event and clk='1' and

   -- increase cnt 1 and 0
   flag    <= "00011";
   flag_dv <= '1';
   wait until (clk'event and clk='1');
   flag_dv <= '0';
   -- wait until unit is ready
   wait until rdy='1';--(clk'event and clk='1' and

   -- read all counters
   addr <= conv_std_logic_vector(1, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(2, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(3, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(4, addr'length);
   wait until (clk'event and clk='1');

   -- clear counter 4 (address is set to cnt 4, so we see result)
   clr <= '1';
   flag <= "10000";
   flag_dv <= '1';
   wait until (clk'event and clk='1');
   flag_dv <= '0';
   --clr <= '0';
   -- wait until unit is ready
   wait until rdy='1';--(clk'event and clk='1' and
   clr <= '0';

   -- check cnt 0 (should be not empty)
   addr <= conv_std_logic_vector(0, addr'length);
   wait until (clk'event and clk='1');

   -- clear all counters
   clr <= '1';
   flag <= "11111";
   flag_dv <= '1';
   wait until (clk'event and clk='1');
   flag_dv <= '0';
   --clr <= '0';
   -- wait until unit is ready
   wait until rdy='1';--(clk'event and clk='1' and
   clr <= '0';

   -- read all counters
   addr <= conv_std_logic_vector(0, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(1, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(2, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(3, addr'length);
   wait until (clk'event and clk='1');

   addr <= conv_std_logic_vector(4, addr'length);
   wait until (clk'event and clk='1');

   wait;
end process;

end architecture behavioral;
