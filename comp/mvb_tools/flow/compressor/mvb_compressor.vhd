-- mvb_compressor.vhd: MVB COMPRESSOR
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MVB_COMPRESSOR is
   generic(
      -- =======================================================================
      -- MVB BUS CONFIGURATION:
      -- =======================================================================
      ITEMS      : natural := 2;
      ITEM_WIDTH : natural := 512
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK        : in  std_logic;
      RESET      : in  std_logic;
      -- =======================================================================
      -- INPUT MVB INTERFACE
      -- =======================================================================
      -- Standard MVB input port without limitations.
      RX_DATA    : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
      RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
      RX_SRC_RDY : in  std_logic;
      RX_DST_RDY : out std_logic;
      -- =======================================================================
      -- OUTPUT MVB INTERFACES
      -- =======================================================================
      -- Reading from output ports MUST be aligned to port 0!
      -- (i.e. to read 2 items from 4 output ports you must use ports 0 and 1)
      TX_DATA    : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
      TX_SRC_RDY : out std_logic_vector(ITEMS-1 downto 0);
      TX_DST_RDY : in  std_logic_vector(ITEMS-1 downto 0)
   );
end MVB_COMPRESSOR;

architecture FULL of MVB_COMPRESSOR is

   signal s_rx_data_arr         : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
   signal s_rx_valids           : std_logic_vector(ITEMS-1 downto 0);
   signal s_shake_din_arr       : slv_array_t(3*ITEMS-1 downto 0)(ITEM_WIDTH downto 0);
   signal s_shake_dout          : std_logic_vector(3*ITEMS*(ITEM_WIDTH+1)-1 downto 0);
   signal s_shake_dout_arr      : slv_array_t(3*ITEMS-1 downto 0)(ITEM_WIDTH downto 0);

   signal s_reg_en              : std_logic;
   signal s_reg_data            : slv_array_t(2*ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
   signal s_reg_vld             : std_logic_vector(2*ITEMS-1 downto 0);
   signal s_reg_vld_mask        : std_logic_vector(2*ITEMS-1 downto 0);
   signal s_reg_data_arr        : slv_array_t(2*ITEMS-1 downto 0)(ITEM_WIDTH downto 0);
   signal s_reg_data_masked_arr : slv_array_t(2*ITEMS-1 downto 0)(ITEM_WIDTH downto 0);

   signal s_tx_data_arr         : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
   signal s_tx_src_rdy          : std_logic_vector(ITEMS-1 downto 0);
   signal s_tx_accepted         : std_logic_vector(ITEMS-1 downto 0);
   signal s_tx_accepted_sum     : std_logic_vector(log2(ITEMS+1)-1 downto 0);
   signal s_saved               : std_logic_vector(ITEMS-1 downto 0);
   signal s_saved_sum           : std_logic_vector(log2(ITEMS+1)-1 downto 0);

   signal s_rx_dst_rdy          : std_logic;

begin

   s_rx_data_arr <= slv_array_downto_deser(RX_DATA,ITEMS,ITEM_WIDTH);
   s_rx_valids   <= s_rx_dst_rdy and RX_SRC_RDY and RX_VLD;

   -----------------------------------------------------------------------------
   -- SHAKER MODULE
   -----------------------------------------------------------------------------

   shake_din_array_g : for i in 0 to ITEMS-1 generate
      s_shake_din_arr(i+(2*ITEMS)) <= s_rx_data_arr(i) & s_rx_valids(i);
      s_shake_din_arr(i+ITEMS)     <= s_reg_data_masked_arr(i+ITEMS);
      s_shake_din_arr(i)           <= s_reg_data_masked_arr(i);
   end generate;

   shaker_i : entity work.MERGE_N_TO_M
   generic map (
      INPUTS     => 3*ITEMS,
      OUTPUTS    => 3*ITEMS,
      DATA_WIDTH => ITEM_WIDTH+1,
      OUTPUT_REG => false
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      INPUT_DATA  => slv_array_ser(s_shake_din_arr,3*ITEMS,ITEM_WIDTH+1),
      OUTPUT_DATA => s_shake_dout
   );

   s_shake_dout_arr <= slv_array_downto_deser(s_shake_dout,3*ITEMS,ITEM_WIDTH+1);

   -----------------------------------------------------------------------------
   -- SHAKER REGISTERS
   -----------------------------------------------------------------------------

   s_reg_en <= (or TX_DST_RDY) or s_rx_dst_rdy;

   shake_regs_g : for i in 0 to 2*ITEMS-1 generate
      reg_vld_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_reg_vld(i) <= '0';
            elsif (s_reg_en = '1') then
               s_reg_vld(i) <= s_shake_dout_arr(i)(0);
            end if;
         end if;
      end process;

      reg_data_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (s_reg_en = '1') then
               s_reg_data(i) <= s_shake_dout_arr(i)(ITEM_WIDTH downto 1);
            end if;
         end if;
      end process;

      s_reg_data_arr(i)(0) <= s_reg_vld(i);
      s_reg_data_arr(i)(ITEM_WIDTH downto 1) <= s_reg_data(i);

      s_reg_data_masked_arr(i)(0) <= s_reg_vld(i) and s_reg_vld_mask(i);
      s_reg_data_masked_arr(i)(ITEM_WIDTH downto 1) <= s_reg_data(i);
   end generate;

   meta_arrays_g : for i in 0 to ITEMS-1 generate
      s_tx_data_arr(i) <= s_reg_data(i);
      s_tx_src_rdy(i)  <= s_reg_vld(i);
      s_tx_accepted(i) <= s_tx_src_rdy(i) and TX_DST_RDY(i);
      s_saved(i)       <= s_reg_vld(i+ITEMS);
   end generate;

   s_reg_vld_mask(2*ITEMS-1 downto ITEMS) <= (others => '1');
   s_reg_vld_mask(ITEMS-1 downto 0) <= not s_tx_accepted;

   -----------------------------------------------------------------------------
   -- CONTROL LOGIC
   -----------------------------------------------------------------------------

   accepted_sum_i : entity work.SUM_ONE
   generic map(
      INPUT_WIDTH => ITEMS,
      OUTPUT_REG  => False
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      -- Input ports
      DIN      => s_tx_accepted,
      DIN_MASK => (others => '1'),
      DIN_VLD  => '1',
      -- Output ports
      DOUT     => s_tx_accepted_sum,
      DOUT_VLD => open
   );

   saved_sum_i : entity work.SUM_ONE
   generic map(
      INPUT_WIDTH => ITEMS,
      OUTPUT_REG  => False
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      -- Input ports
      DIN      => s_saved,
      DIN_MASK => (others => '1'),
      DIN_VLD  => '1',
      -- Output ports
      DOUT     => s_saved_sum,
      DOUT_VLD => open
   );

   s_rx_dst_rdy <= '1' when (unsigned(s_tx_accepted_sum) >= unsigned(s_saved_sum)) else '0';

   -----------------------------------------------------------------------------
   -- OUTPUT SIGNALS
   -----------------------------------------------------------------------------

   TX_DATA    <= slv_array_ser(s_tx_data_arr,ITEMS,ITEM_WIDTH);
   TX_SRC_RDY <= s_tx_src_rdy;
   RX_DST_RDY <= s_rx_dst_rdy;

end architecture;
