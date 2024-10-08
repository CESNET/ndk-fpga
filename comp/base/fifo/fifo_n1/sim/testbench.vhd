-- testbench.vhd: Testbench for fifo_n1
-- Copyright (C) 2017 CESNET
-- Author(s): Vaclav Hummel <xhumme00@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

   -- Constants declaration ---------------------------------------------------
   -- Synchronization
   constant C_CLK_PER    : time := 5.0 ns;
   constant C_RST_TIME : time := 10 * C_CLK_PER + 1 ns;

   -- Number of independent write ports
   constant WRITE_PORTS    : integer := 5;
   -- Set data width here
   constant DATA_WIDTH     : integer := 8;
   -- Set number of items per ONE memory
   -- Total size equals to WRITE_PORTS*ITEMS
   constant ITEMS          : integer := 4;

   constant ALMOST_FULL_OFFSET      : integer := 8;
   constant ALMOST_EMPTY_OFFSET     : integer := 8;


   -- Synchronization
   signal clk                                : std_logic;
   signal rst                                : std_logic;

   -- Write interface
   signal fifo_data_in  : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0); -- Data input
   signal fifo_src_rdy  : std_logic;
   signal fifo_we       : std_logic_vector(WRITE_PORTS-1 downto 0);  -- Write request
   signal fifo_full     : std_logic; -- FIFO is full
   signal fifo_afull    : std_logic; -- FIFO is almost full (see ALMOST_FULL_OFFSET)

   -- Read interface
   signal fifo_data_out       : std_logic_vector(DATA_WIDTH-1 downto 0); -- Data output
   signal fifo_re             : std_logic;  -- Read request
   signal fifo_empty          : std_logic;  -- FIFO is empty
   signal fifo_aempty         : std_logic;  -- FIFO is almost empty (see ALMOST_EMPTY_OFFSET)



-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- CROSSBAR SCHEDULER planner
   -- -------------------------------------------------------------------------

   uut: entity work.fifo_n1
   generic map(
      -- Number of independent write ports
      WRITE_PORTS => WRITE_PORTS,
      -- Set data width here
      DATA_WIDTH => DATA_WIDTH,
      -- Set number of items per ONE memory
      -- Total size equals to WRITE_PORTS*ITEMS
      ITEMS => ITEMS,

      ALMOST_FULL_OFFSET => ALMOST_FULL_OFFSET,
      ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET

   )
   port map(
      CLK => clk,
      RESET => rst,

      -- Write interface
      DATA_IN => fifo_data_in,
      WE => fifo_we and fifo_src_rdy,
      FULL => fifo_full,
      AFULL => fifo_afull,

      -- Read interface
      DATA_OUT => fifo_data_out,
      RE => fifo_re,
      EMPTY => fifo_empty,
      AEMPTY => fifo_aempty
   );

   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating clk
   clk_gen: process
   begin
      clk <= '1';
      wait for C_CLK_PER / 2;
      clk <= '0';
      wait for C_CLK_PER / 2;
   end process clk_gen;

   -- generating reset
   rst_gen: process
   begin
      rst <= '1';
      wait for C_RST_TIME;
      rst <= '0';
      wait;
   end process rst_gen;

   -- -------------------------------------------------------------------------
   --                          src_rdy and dst_rdy process
   -- -------------------------------------------------------------------------

   src_dstp: process
      variable seed1 : positive := DATA_WIDTH;
      variable seed2 : positive := WRITE_PORTS;

      variable rand : real;
      variable a    : integer;
   begin
         wait for C_CLK_PER - 1 ns;
         uniform(seed1, seed2, rand);
         a := integer(rand*1.0);
         fifo_src_rdy <= '1' when (a = 1) else '0';

         uniform(seed1, seed2, rand);
         a := integer(rand*1.0);
         fifo_re <= '1' when (a = 1) else '0';

         wait for 1 ns;
   end process;
   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   tb: process
   begin
      -- Wait for the reset

      fifo_data_in(0) <= "00000000";
      fifo_data_in(1) <= "00000000";
      fifo_data_in(2) <= "00000000";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00000000";

      fifo_we <= "00000";

      wait until rst = '0';
      wait for C_CLK_PER - 2 ns;

      -- Write
      fifo_data_in(0) <= "00000001";
      fifo_data_in(1) <= "00000010";
      fifo_data_in(2) <= "00000011";
      fifo_data_in(3) <= "00000100";
      fifo_data_in(4) <= "00000101";

      fifo_we <= "11111";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00000110";
      fifo_data_in(1) <= "00000000";
      fifo_data_in(2) <= "00000000";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00000000";

      fifo_we <= "00001";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00000000";
      fifo_data_in(1) <= "00000111";
      fifo_data_in(2) <= "00000000";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00000000";

      fifo_we <= "00010";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00000000";
      fifo_data_in(1) <= "00000000";
      fifo_data_in(2) <= "00000000";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00001000";

      fifo_we <= "10000";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00001001";
      fifo_data_in(1) <= "00000000";
      fifo_data_in(2) <= "00000000";
      fifo_data_in(3) <= "00001010";
      fifo_data_in(4) <= "00001011";

      fifo_we <= "11001";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00000000";
      fifo_data_in(1) <= "00001100";
      fifo_data_in(2) <= "00001101";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00001110";

      fifo_we <= "10110";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00001111";
      fifo_data_in(1) <= "00000000";
      fifo_data_in(2) <= "00010000";
      fifo_data_in(3) <= "00010001";
      fifo_data_in(4) <= "00010010";

      fifo_we <= "11101";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00010011";
      fifo_data_in(1) <= "00010100";
      fifo_data_in(2) <= "00010101";
      fifo_data_in(3) <= "00010110";
      fifo_data_in(4) <= "00000000";

      fifo_we <= "01111";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      for i in 0 to 18-1 loop
         -- No write
         fifo_data_in(0) <= "00000000";
         fifo_data_in(1) <= "00000000";
         fifo_data_in(2) <= "00000000";
         fifo_data_in(3) <= "00000000";
         fifo_data_in(4) <= "00000000";

         fifo_we <= "00000";

         wait for 1 ns;
         wait for C_CLK_PER - 1 ns;
   end loop;

      -- Write
      fifo_data_in(0) <= "00010111";
      fifo_data_in(1) <= "00011000";
      fifo_data_in(2) <= "00011001";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00011010";

      fifo_we <= "10111";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      -- Write
      fifo_data_in(0) <= "00011011";
      fifo_data_in(1) <= "00011100";
      fifo_data_in(2) <= "00011101";
      fifo_data_in(3) <= "00000000";
      fifo_data_in(4) <= "00011110";

      fifo_we <= "10111";

      wait for 1 ns;
      if (fifo_full = '1' or fifo_src_rdy = '0') then
         wait until ((clk'event and clk = '1') and fifo_full = '0' and fifo_src_rdy = '1');
      end if;
      wait for C_CLK_PER - 1 ns;

      wait;
   end process;
end architecture behavioral;
