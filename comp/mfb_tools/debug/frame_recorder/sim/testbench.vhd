-- testbench.vhd: Testbench for MFB frame player
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.std_logic_textio.all;

use work.mi_sim_pkg.all;
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

   constant REGIONS     : natural := 1;
   constant REGION_SIZE : natural := 8;
   constant BLOCK_SIZE  : natural := 8;
   constant ITEM_WIDTH  : natural := 8;

   -- Signals declaration -----------------------------------------------------

   signal clk           : std_logic;
   signal reset         : std_logic;

   signal rx_data       : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   signal rx_sof_pos    : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   signal rx_eof_pos    : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   signal rx_sof        : std_logic_vector(REGIONS-1 downto 0);
   signal rx_eof        : std_logic_vector(REGIONS-1 downto 0);
   signal rx_src_rdy    : std_logic;
   signal rx_dst_rdy    : std_logic;

   -- MI32 interface
   signal mi32_dwr      : std_logic_vector(31 downto 0);
   signal mi32_addr     : std_logic_vector(31 downto 0);
   signal mi32_be       : std_logic_vector(3 downto 0);
   signal mi32_rd       : std_logic;
   signal mi32_wr       : std_logic;
   signal mi32_ardy     : std_logic;
   signal mi32_drd      : std_logic_vector(31 downto 0);
   signal mi32_drdy     : std_logic;

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   --                              UUT
   -- -------------------------------------------------------------------------

   -- UUT instantiation
   uut: entity work.MFB_FRAME_RECORDER
   generic map (
      REGIONS      => REGIONS,
      REGION_SIZE  => REGION_SIZE,
      BLOCK_SIZE   => BLOCK_SIZE,
      ITEM_WIDTH   => ITEM_WIDTH
   )
   port map(
      CLK        => clk,
      RST        => reset,

      MI_DWR     => mi32_dwr,
      MI_ADDR    => mi32_addr,
      MI_RD      => mi32_rd,
      MI_WR      => mi32_wr,
      MI_BE      => mi32_be,
      MI_DRD     => mi32_drd,
      MI_ARDY    => mi32_ardy,
      MI_DRDY    => mi32_drdy,

      RX_DATA    => rx_data,
      RX_SOF_POS => rx_sof_pos,
      RX_EOF_POS => rx_eof_pos,
      RX_SOF     => rx_sof,
      RX_EOF     => rx_eof,
      RX_SRC_RDY => rx_src_rdy,
      RX_DST_RDY => rx_dst_rdy
   );

   -- -------------------------------------------------------------------------
   --                       MI32 simulation component
   -- -------------------------------------------------------------------------

   mi_sim_i : entity work.MI_SIM
   generic map (
      MI_SIM_ID => 0
   )
   port map (
      CLK => clk,
      RESET => reset,

      MI32_DWR  => mi32_dwr,
      MI32_ADDR => mi32_addr,
      MI32_BE   => mi32_be,
      MI32_RD   => mi32_rd,
      MI32_WR   => mi32_wr,
      MI32_ARDY => mi32_ardy,
      MI32_DRD  => mi32_drd,
      MI32_DRDY => mi32_drdy
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
      rx_src_rdy <= '0';
      wait for 20*CLK_PER;

      rx_data    <= std_logic_vector(to_unsigned(99999999,rx_data'length));
      rx_sof_pos <= std_logic_vector(to_unsigned(2,rx_sof_pos'length));
      rx_eof_pos <= std_logic_vector(to_unsigned(48,rx_eof_pos'length));
      rx_sof     <= (others => '1');
      rx_eof     <= (others => '1');
      wait for 5 * CLK_PER;

      rx_src_rdy <= '1';
      wait for 5 * CLK_PER;

      rx_src_rdy <= '0';
      wait until (rising_edge(clk));

      wait;
   end process;

   tb: process
      variable addr : std_logic_vector(31 downto 0) := (others => '0');
      variable data : std_logic_vector(31 downto 0);
      variable be   : std_logic_vector(3 downto 0);
   begin
      wait for CLK_PER;

      -- read status register
      addr := X"00000000";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- write control register - set fifo_in_en.
      addr := X"00000004";
      data := X"00000001";
      be   := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read control register
      addr := X"00000004";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read data registers
      data_l : for i in 0 to 15 loop
         addr := std_logic_vector(to_unsigned(((i+5)*4),32));
         data := X"00000000";
         be   := "1111";
         ReadData(addr, data, be, status(0), 0);
         wait for 5 * CLK_PER;
      end loop;

      -- read eof_pos register
      addr := X"00000010";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read sof_pos register
      addr := X"0000000C";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read data valid register - must be last write
      addr := X"00000008";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read status register
      addr := X"00000000";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- write control register - unset fifo_out_en
      addr := X"00000004";
      data := X"00000000";
      be   := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read status register
      addr := X"00000000";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      wait until (rising_edge(clk));

      wait;
   end process;
end architecture behavioral;
