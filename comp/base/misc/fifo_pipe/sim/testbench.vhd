-- testbench.vhd: Testbench for merger from n inputs to m outputs
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
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

   -- Constants declaration ---------------------------------------------------

   -- Synchronization
   constant C_CLK_PER            : time := 5.0 ns;
   constant C_RST_TIME           : time := 10 * C_CLK_PER + 1 ns;

   --! \brief Data width
   constant DATA_WIDTH           : integer := 16;

   constant FALSE_FIFO_SIZE      : integer := 512;

   -- Signals declaration -----------------------------------------------------

   -- Synchronization
   signal clk                                : std_logic;
   signal rst                                : std_logic;

   signal rx_src_rdy        : std_logic := '0';
   signal rx_dst_rdy        : std_logic;
   signal rx_data           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_src_rdy        : std_logic;
   signal tx_dst_rdy        : std_logic := '0';
   signal tx_data           : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal false_fifo   : std_logic_vector(FALSE_FIFO_SIZE*DATA_WIDTH-1 downto 0);
   signal false_rd_ptr : unsigned(log2(FALSE_FIFO_SIZE)-1 downto 0) := (others => '0');
   signal false_wr_ptr : unsigned(log2(FALSE_FIFO_SIZE)-1 downto 0) := (others => '0');

   signal TEST_STATUS : std_logic := '1';

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- CROSSBAR SCHEDULER planner
   -- -------------------------------------------------------------------------

   uut: entity work.fifo_pipe
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      PIPE_N     => 4,
      OUT_REG    => false
   )
   port map(

      CLK => clk,
      RESET => rst,

      RX_SRC_RDY => rx_src_rdy,
      RX_DST_RDY => rx_dst_rdy,

      RX_DATA    => rx_data,

      TX_SRC_RDY => tx_src_rdy,
      TX_DST_RDY => tx_dst_rdy,

      TX_DATA    => tx_data
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

   tb: process
      variable seed1 : positive := 42;
      variable seed2 : positive := 42;

      variable rand  : real;
      variable X     : integer;

      variable     src_rdy_ch : integer := 50;
      variable not_src_rdy_ch : integer := 1;

      variable     dst_rdy_ch : integer := 1;
      variable not_dst_rdy_ch : integer := 0;

      variable rx_rdy : std_logic := '1';
      variable tx_rdy : std_logic := '0';

      variable d_i : unsigned(DATA_WIDTH-1 downto 0) := (others => '0');
      variable d_o : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');

      variable d_r : std_logic;

      variable i : integer;

      variable n_r_burst_ch : integer := 80;
      variable n_r_burst_s  : integer := 22;
      variable n_r_burst    : integer := 0;
   begin
      -- Wait for the reset
      if (rst='1') then
         wait until rst='0';
      end if;

      if (rx_src_rdy='1' and rx_rdy='1') then
         i := to_integer(false_wr_ptr);
         false_fifo((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH) <= std_logic_vector(d_i);
         false_wr_ptr <= false_wr_ptr+1;
         d_i := d_i+1;
      end if;

      if (rx_rdy='1' or rx_src_rdy='0') then
         rx_src_rdy <= '0';
         rx_data    <= std_logic_vector(d_i);

         uniform(seed1,seed2,rand);
         X := integer(rand*real(src_rdy_ch+not_src_rdy_ch));
         if (X<=src_rdy_ch) then
            rx_src_rdy <= '1';
         end if;

      end if;

      if (tx_rdy='1' or tx_dst_rdy='0') then

         tx_dst_rdy <= '0';
         d_r := '0';

         uniform(seed1,seed2,rand);
         X := integer(rand*real(dst_rdy_ch+not_dst_rdy_ch));
         if (X<=dst_rdy_ch and n_r_burst=0) then
            tx_dst_rdy <= '1';
            d_r := '1';
         elsif (n_r_burst>0) then
            n_r_burst := n_r_burst-1;
         end if;

         uniform(seed1,seed2,rand);
         X := integer(rand*real(n_r_burst_ch));
         if (X=0) then
            uniform(seed1,seed2,rand);
            X := integer(rand*real(n_r_burst_s));
            n_r_burst := n_r_burst + X;
         end if;

      end if;

      rx_rdy := rx_dst_rdy;
      tx_rdy := tx_src_rdy;
      d_o    := tx_data;

      if (tx_src_rdy='1' and d_r='1') then
         i := to_integer(false_rd_ptr);
         TEST_STATUS <= '1' when false_fifo((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)=tx_data else '0';
         false_rd_ptr <= false_rd_ptr+1;
      end if;

      wait for C_CLK_PER;
   end process;
end architecture behavioral;
