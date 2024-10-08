-- testbench.vhd: Testbench for MFB frame player
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

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

   constant CLK_PER     : time := 10 ns;
   constant RESET_TIME  : time := 10 * CLK_PER;

   constant REGIONS         : natural := 1;
   constant REGION_SIZE     : natural := 8;
   constant BLOCK_SIZE      : natural := 8;
   constant ITEM_WIDTH      : natural := 8;
   constant CNT_TICKS_WIDTH : natural := 4;
   constant CNT_BYTES_WIDTH : natural := log2(((2**CNT_TICKS_WIDTH)-1)*REGIONS*REGION_SIZE*BLOCK_SIZE);

   -- Signals declaration -----------------------------------------------------

   signal clk           : std_logic;
   signal reset         : std_logic;

   signal rx_sof_pos    : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   signal rx_eof_pos    : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   signal rx_sof        : std_logic_vector(REGIONS-1 downto 0);
   signal rx_eof        : std_logic_vector(REGIONS-1 downto 0);
   signal rx_src_rdy    : std_logic;
   signal rx_dst_rdy    : std_logic;

   signal cnt_ticks     : std_logic_vector(CNT_TICKS_WIDTH-1 downto 0); -- counter of clock ticks
   signal cnt_ticks_max : std_logic; -- maximum value flag of clock ticks counter
   signal cnt_bytes     : std_logic_vector(CNT_BYTES_WIDTH-1 downto 0); -- counter of valid bytes
   signal cnt_clear     : std_logic; -- reset all counters

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   --                              UUT
   -- -------------------------------------------------------------------------

   -- UUT instantiation
   uut: entity work.MFB_SPEED_METER
   generic map (
      REGIONS         => REGIONS,
      REGION_SIZE     => REGION_SIZE,
      BLOCK_SIZE      => BLOCK_SIZE,
      ITEM_WIDTH      => ITEM_WIDTH,
      CNT_TICKS_WIDTH => CNT_TICKS_WIDTH,
      CNT_BYTES_WIDTH => CNT_BYTES_WIDTH
   )
   port map(
      CLK           => clk,
      RST           => reset,

      RX_SOF_POS    => rx_sof_pos,
      RX_EOF_POS    => rx_eof_pos,
      RX_SOF        => rx_sof,
      RX_EOF        => rx_eof,
      RX_SRC_RDY    => rx_src_rdy,
      RX_DST_RDY    => rx_dst_rdy,

      CNT_TICKS     => cnt_ticks,
      CNT_TICKS_MAX => cnt_ticks_max,
      CNT_BYTES     => cnt_bytes,
      CNT_CLEAR     => cnt_clear
   );

   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating clk
   clk_gen: process
   begin
      clk <= '1';
      wait for CLK_PER / 2;
      clk <= '0';
      wait for CLK_PER / 2;
   end process;

   -- generating reset
   reset_gen: process
   begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process;

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   tb_rx_p : process
   begin
      cnt_clear  <= '0';
      rx_src_rdy <= '0';
      rx_dst_rdy <= '1';
      wait for 11*CLK_PER;
      wait until rising_edge(clk);

      -- frame 138B (state 100) - 64B
      rx_sof_pos <= std_logic_vector(to_unsigned(0,rx_sof_pos'length));
      rx_eof_pos <= std_logic_vector(to_unsigned(0,rx_eof_pos'length));
      rx_sof     <= (others => '1');
      rx_eof     <= (others => '0');
      rx_src_rdy <= '1';
      wait until rising_edge(clk);
      -- (state 001) - 64B
      rx_sof_pos <= std_logic_vector(to_unsigned(0,rx_sof_pos'length));
      rx_eof_pos <= std_logic_vector(to_unsigned(0,rx_eof_pos'length));
      rx_sof     <= (others => '0');
      rx_eof     <= (others => '0');
      rx_src_rdy <= '1';
      wait until rising_edge(clk);
      -- frame 72B (state 111) - 10B + 8B
      rx_sof_pos <= std_logic_vector(to_unsigned(7,rx_sof_pos'length));
      rx_eof_pos <= std_logic_vector(to_unsigned(9,rx_eof_pos'length));
      rx_sof     <= (others => '1');
      rx_eof     <= (others => '1');
      rx_src_rdy <= '1';

      rx_dst_rdy <= '0';
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      rx_dst_rdy <= '1';

      wait until rising_edge(clk);
      -- (state 011) - 64B
      rx_sof_pos <= std_logic_vector(to_unsigned(0,rx_sof_pos'length));
      rx_eof_pos <= std_logic_vector(to_unsigned(63,rx_eof_pos'length));
      rx_sof     <= (others => '0');
      rx_eof     <= (others => '1');
      rx_src_rdy <= '1';
      wait until rising_edge(clk);

      -- frame 64B (state 110)
      rx_sof_pos <= std_logic_vector(to_unsigned(0,rx_sof_pos'length));
      rx_eof_pos <= std_logic_vector(to_unsigned(63,rx_eof_pos'length));
      rx_sof     <= (others => '1');
      rx_eof     <= (others => '1');
      rx_src_rdy <= '1';
      wait until rising_edge(clk);
      rx_src_rdy <= '0';

      wait until rising_edge(clk);
      -- frame 64B (state 110)
      rx_src_rdy <= '1';

      wait until rising_edge(clk);
      rx_src_rdy <= '0';

      -- total clock 11
      -- total bytes 338B

      wait for 11*CLK_PER;
      wait until rising_edge(clk);
      cnt_clear  <= '1';
      wait until rising_edge(clk);
      cnt_clear  <= '0';

      wait;
   end process;

end architecture behavioral;
