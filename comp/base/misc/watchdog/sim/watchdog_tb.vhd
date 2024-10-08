--
-- watchdog_testbench.vhd: Component testbench.
-- Copyright (C) 2015 CESNET
-- Author(s): Adam Piecek <xpiece00@stud.fit.vutbr.cz>
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
use ieee.numeric_std.all;

-- math package - log2 function
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

   constant DATA_WIDTH     : positive := 10;
   constant EDGE_DETECT    : boolean  := false;
   constant COUNT          : positive := 9;
   constant COUNTER_WIDTH  : positive := 32;
   signal   TIMING         : boolean  := false;

   constant clkper      : time      := 10 ns;
   constant RESET_TIME  : time      := 3*clkper - 1ns ;

   signal clk           : std_logic;
   signal reset         : std_logic;

   signal data_in       : std_logic_vector(DATA_WIDTH-1 downto 0)
                                          := (others => '0');
   signal src_rdy_in    : std_logic;
   signal dst_rdy_in    : std_logic;

   signal data_out      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal src_rdy_out   : std_logic;
   signal dst_rdy_out   : std_logic;

   signal counter       : std_logic_vector(COUNTER_WIDTH-1 downto 0);
   signal locked        : std_logic;

   -- MI32
   signal dwr           : std_logic_vector(31 downto 0);
   signal addr          : std_logic_vector(31 downto 0);
   signal rd            : std_logic;
   signal wr            : std_logic;
   signal be            : std_logic_vector(3 downto 0);
   signal drd           : std_logic_vector(31 downto 0);
   signal ardy          : std_logic;
   signal drdy          : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut: entity work.watchdog_mi32
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         EDGE_DETECT    => EDGE_DETECT,
         COUNT          => COUNT,
         COUNTER_WIDTH  => COUNTER_WIDTH,
         TIMING         => TIMING
      )
      port map(
         -- Common interface
         CLK            => clk,
         RESET          => reset,

         DATA_IN        => data_in,
         SRC_RDY_IN     => src_rdy_in,
         DST_RDY_IN     => dst_rdy_in,

         DATA_OUT       => data_out,
         SRC_RDY_OUT    => src_rdy_out,
         DST_RDY_OUT    => dst_rdy_out,
         COUNTER        => counter,
         LOCKED         => locked,

         -- MI32
         DWR            => dwr,
         ADDR           => addr,
         RD             => rd,
         WR             => wr,
         BE             => be,
         DRD            => drd,
         ARDY           => ardy,
         DRDY           => drdy
     );

   be <= "0001";

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

      -- RESET ---------------------------------------------------------------
      wr <= '0';
      rd <= '0';
      addr <= (others => '0');
      dwr <= (others => '0');
      reset <= '1';
      src_rdy_in <= '1';
      dst_rdy_out <= '1';

      wait for RESET_TIME;
      reset <= '0';

      -- test IN signals-----
      wait for 4*clkper;
      src_rdy_in <= '0';
      wait for 4*clkper;
      src_rdy_in <= '1';
      wait for 4*clkper;
      wr <= '1';
      dwr(0) <= '1';
      wait for 2*clkper;
      dwr(0) <= '0';
      wait for clkper;
      wr <= '0';

      wait for 4*clkper;
      dst_rdy_out <= '0';
      wait for 4*clkper;
      reset <= '1';
      dst_rdy_out <= '1';
      wait for RESET_TIME;
      reset <= '0';
      rd <= '1';

      -- test wr signal
      dwr(0) <= '1';
      wait for 2*clkper;
      rd <= '0';
      wr <= '1';
      wait for 3*clkper;
      wr <= '1';
      rd <= '1';

      -- test keep_alive ---
      addr(2) <= '1';
      wait for (COUNT/2)*clkper;
      dwr(0) <= '1';
      wait for clkper;
      dwr(0) <= '0';

      wait for COUNT*clkper*2;
      rd <= '0';
      dwr(0) <= '1';
      wait for clkper*3;
      rd <= '1';
      dwr(0) <= '0';
      wait for clkper*4;
      rd <= '0';

      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';

      wait for 5*clkper;

      wait;
   end process;
end architecture behavioral;
