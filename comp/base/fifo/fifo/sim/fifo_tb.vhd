--
-- fifo_tb.vhd: Testbench for FIFO
-- Copyright (C) 2003 CESNET
-- Author(s): Pecenka Tomas pecenka@liberouter.org
--            Pus Viktor pus@liberouter.org
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
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
   generic (
      data_width     : integer := 16;
      items          : integer := 16;
      block_size     : integer := 4
      );
end testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavior of testbench is

   component FIFO100_AUX is
    port(
         -- FIFO reset
         RESET     : in std_logic;   -- FIFO reset signal

         -- FIFO input part
         DATA_IN   : in std_logic_vector((data_width-1) downto 0); -- Data input
         WRITE_REQ : in std_logic;   -- Write request

         -- FIFO output part
         DATA_OUT  : out std_logic_vector((data_width-1) downto 0); -- Data output
         READ_REQ  : in std_logic;   -- Read request

         -- FIFO full and empty signals
         EMPTY     : out std_logic;  -- FIFO is empty
         FULL      : out std_logic;  -- FIFO is full
         LSTBLK    : out std_logic;  -- Last block remaining

         -- CLK inputs and outputs
         CLK_50    : in std_logic;   -- CLK_GEN 50MHz input
         CLK_LOCK  : out std_logic;  -- CLK_GEN 100MHz locked signal
         CLK_100   : out std_logic   -- CLK_GEN 100MHz clock signal

      );
   end component FIFO100_AUX;

   -- signals for component FIFO100_AUX
   signal reset     : std_logic;
   signal data_in   : std_logic_vector((data_width-1) downto 0);
   signal write_req : std_logic;
   signal data_out  : std_logic_vector((data_width-1) downto 0);
   signal read_req  : std_logic;
   signal empty     : std_logic;
   signal full      : std_logic;
   signal lstblk    : std_logic;
   signal clk_50    : std_logic;
   signal clk_lock  : std_logic;
   signal clk_100   : std_logic;

   -- Simulation constants
   constant  period      : time     := 20 ns;
   constant  half_period : time     := period / 2;

begin
   uut: FIFO100_AUX
    port map(
         RESET     => reset,     -- FIFO reset signal
         DATA_IN   => data_in,   -- Data input
         WRITE_REQ => write_req, -- Write request
         DATA_OUT  => data_out,  -- Data output
         READ_REQ  => read_req,  -- Read request
         EMPTY     => empty,     -- FIFO is empty
         FULL      => full,      -- FIFO is full
         LSTBLK    => lstblk,    -- Last block remaining
         CLK_50    => clk_50,    -- CLK_GEN 50MHz input
         CLK_LOCK  => clk_lock,  -- CLK_GEN 100MHz locked signal
         CLK_100   => clk_100    -- CLK_GEN 100MHz clock signal
      );

   -- Clk signal generator ----------------------------------------------------
   clk_gen : process
   begin
      clk_50 <= '1';
      wait for half_period;
      clk_50 <= '0';
      wait for half_period;
   end process;

   -- RESET signal generator --------------------------------------------------
   reset_gen : process
      variable i : integer;
   begin
      -- Reset
      reset <= '1';
      -- Wait until CLK not locked
      wait until clk_lock'event and clk_lock = '1';

      -- wait for 100 clocks
      for i in 1 to 100 loop
         wait until clk_100'event and clk_100='1';
      end loop;
      reset <= '0'; -- after 1 ns;
      wait; -- will wait forever
   end process;

   -- Counter - data generator ------------------------------------------------
   data_gen: process
      variable i : integer;
   begin

      data_in <= (others => '0');

      -- Wait while RESET is active
      wait until reset'event and reset = '0';

      -- inifinite loop
      loop
         for i in 0 to 2**data_in'length-1 loop
            data_in <= conv_std_logic_vector(i, data_in'length); -- after 1 ns;
            wait until clk_100'event and clk_100='1';
         end loop;
      end loop;
   end process;

   -- Control signal generator ------------------------------------------------
   tbcontrol : process
   begin

      write_req <='0';
      read_req  <='0';
      -- wait for reset
      wait until reset'event and reset = '0';

      -- testing FULL signal
      write_req <='1'; -- after 1 ns;
      read_req  <='0'; -- after 1 ns;
      wait until full='1';

      -- testing write to full FIFO
      wait until clk_100'event and clk_100='1';

      -- testing EMPTY signal - read from fifo
      write_req <='0'; -- after 1 ns;
      read_req  <='1'; -- after 1 ns;
      wait until empty='1';

      -- read from empty FIFO
      wait until clk_100'event and clk_100='1';

      -- testing transit throw fifo
      wait until clk_100'event and clk_100='1';
      read_req  <='0'; -- after 1 ns;
      write_req <='1'; -- after 1 ns;
      wait until clk_100'event and clk_100='1';
      read_req  <='1'; -- after 1 ns;

      wait;
   end process;

end;
