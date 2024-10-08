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

   signal tx_data       : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   signal tx_sof_pos    : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   signal tx_eof_pos    : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   signal tx_sof        : std_logic_vector(REGIONS-1 downto 0);
   signal tx_eof        : std_logic_vector(REGIONS-1 downto 0);
   signal tx_src_rdy    : std_logic;
   signal tx_dst_rdy    : std_logic;

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
   uut: entity work.MFB_FRAME_PLAYER
   generic map (
      REGIONS      => REGIONS,
      REGION_SIZE  => REGION_SIZE,
      BLOCK_SIZE   => BLOCK_SIZE,
      ITEM_WIDTH   => ITEM_WIDTH,
      FIFO_DEPTH   => 512
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

      TX_DATA    => tx_data,
      TX_SOF_POS => tx_sof_pos,
      TX_EOF_POS => tx_eof_pos,
      TX_SOF     => tx_sof,
      TX_EOF     => tx_eof,
      TX_SRC_RDY => tx_src_rdy,
      TX_DST_RDY => tx_dst_rdy
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

      MI32_DWR => mi32_dwr,
      MI32_ADDR => mi32_addr,
      MI32_BE => mi32_be,
      MI32_RD => mi32_rd,
      MI32_WR => mi32_wr,
      MI32_ARDY => mi32_ardy,
      MI32_DRD => mi32_drd,
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

   tb: process
      variable addr : std_logic_vector(31 downto 0) := (others => '0');
      variable data : std_logic_vector(31 downto 0);
      variable be   : std_logic_vector(3 downto 0);
   begin
      tx_dst_rdy <= '1';
      wait for CLK_PER;

      -- read status register
      addr := X"00000000";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read control register
      addr := X"00000004";
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

      -- write data registers
      data_l : for i in 0 to 15 loop
         addr := std_logic_vector(to_unsigned(((i+5)*4),32));
         data := std_logic_vector(to_unsigned(i,32));
         be   := "1111";
         WriteData(addr, data, be, status(0), 0);
         wait for 5 * CLK_PER;
      end loop;

      -- write eof_pos register
      addr := X"00000010";
      data := X"0000003F";
      be   := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- write sof_pos register
      addr := X"0000000C";
      data := X"00000001";
      be   := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- write data valid register - must be last write
      addr := X"00000008";
      data := X"00000007";
      be   := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- read status register
      addr := X"00000000";
      data := X"00000000";
      be   := "1111";
      ReadData(addr, data, be, status(0), 0);
      wait for 5 * CLK_PER;

      -- write control register - set fifo_out_en and set repeater
      addr := X"00000004";
      data := X"0000000B";
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
