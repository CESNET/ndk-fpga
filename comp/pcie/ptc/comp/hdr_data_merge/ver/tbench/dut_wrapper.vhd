-- dut_wrapper.vhd:
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity DUT_WRAPPER is
   generic(
      -- =======================================================================
      -- MFB DATA BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MFB(2,1,8,32) for PCIe on UltraScale+
      MFB_REGIONS        : natural := 2;
      MFB_REGION_SIZE    : natural := 1;
      MFB_BLOCK_SIZE     : natural := 8;
      MFB_ITEM_WIDTH     : natural := 32;
      -- =======================================================================
      -- MVB HEADER BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MVB(2,128) for PCIe on UltraScale+
      MVB_ITEMS          : natural := 2;
      MVB_ITEM_WIDTH     : natural := 128+1;
      -- =======================================================================
      -- OTHER CONFIGURATION:
      -- =======================================================================
      -- Set maximum supported PCIe transaction size (HDR + payload) in dwords,
      -- is used to correctly set the data width of the word counter.
      MAX_PCIE_TRANS_SIZE : natural := 2052
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      -- DMA clock for MFB DATA input
      DMA_CLK        : in  std_logic;
      DMA_RESET      : in  std_logic;
      -- PCIE clock for MFB output and MVB header input
      PCIE_CLK       : in  std_logic;
      PCIE_RESET     : in  std_logic;
      -- =======================================================================
      -- INPUT MVB HEADER INTERFACE
      -- =======================================================================
      -- header of PCIe transaction + is payload flag
      RX_MVB_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
      -- valid of each header of PCIe transaction in MVB word
      RX_MVB_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- MVB word is valid
      RX_MVB_SRC_RDY : in  std_logic;
      -- MVB destination is ready
      RX_MVB_DST_RDY : out std_logic;
      -- =======================================================================
      -- INPUT MFB DATA INTERFACE (DMA CLK)
      -- =======================================================================
      RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_SRC_RDY : in  std_logic;
      RX_MFB_DST_RDY : out std_logic;
      -- =======================================================================
      -- OUTPUT MFB HEADER+DATA INTERFACE
      -- =======================================================================
      TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_SRC_RDY : out std_logic;
      TX_MFB_DST_RDY : in  std_logic;
      TX_MFB_BE      : out std_logic_vector(MFB_REGIONS*8-1 downto 0)
   );
end DUT_WRAPPER;

architecture FULL of DUT_WRAPPER is

   constant MFB_REGION_WIDTH   : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
   constant MFB_DATA_WIDTH     : natural := MFB_REGIONS*MFB_REGION_WIDTH;
   constant TRANS_SIZE_WIDTH   : natural := 11;
   -- HDM (Header Data Merge) MFB FIFO is ready for 16 MPS (256B) transaction
   constant HDM_MFB_FIFO_DEPTH : natural := (16*256*8)/MFB_DATA_WIDTH;
   -- CODAPA counter must hold all transaction (1 transaction per region) in HDM MFB FIFO
   constant CODAPA_CNT_WIDTH   : natural := log2(MFB_REGIONS*HDM_MFB_FIFO_DEPTH)+1;

   signal s_fifo_data            : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
   signal s_fifo_sof_pos         : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
   signal s_fifo_eof_pos         : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
   signal s_fifo_sof             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_eof             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_src_rdy         : std_logic;
   signal s_fifo_dst_rdy         : std_logic;

   signal s_codapa_inc_vld       : std_logic;
   signal s_codapa_inc           : std_logic_vector(log2(MFB_REGIONS+1)-1 downto 0);
   signal s_codapa_inc_cdc_full  : std_logic;
   signal s_codapa_inc_sync      : std_logic_vector(log2(MFB_REGIONS+1)-1 downto 0);
   signal s_codapa_inc_sync_vld  : std_logic;
   signal s_codapa_inc_cdc_empty : std_logic;
   signal s_codapa_inc_sync_reg  : std_logic_vector(log2(MFB_REGIONS+1)-1 downto 0);

   signal s_mvb_data             : std_logic_vector(MVB_ITEMS*(MVB_ITEM_WIDTH-1)-1 downto 0);
   signal s_mvb_be               : std_logic_vector(MVB_ITEMS*8-1 downto 0);
   signal s_mvb_payload          : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_mvb_payload_size     : std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);

   signal s_codapa_mvb_data            : std_logic_vector(MVB_ITEMS*(MVB_ITEM_WIDTH-1)-1 downto 0);
   signal s_codapa_mvb_be              : std_logic_vector(MVB_ITEMS*8-1 downto 0);
   signal s_codapa_mvb_payload         : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_codapa_mvb_type            : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_codapa_mvb_payload_size    : std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
   signal s_codapa_mvb_vld             : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal s_codapa_mvb_src_rdy         : std_logic;
   signal s_codapa_mvb_dst_rdy         : std_logic;

begin

   data_asfifo_i : entity work.MFB_ASFIFOX
   generic map(
      MFB_REGIONS     => MFB_REGIONS,
      MFB_REG_SIZE    => MFB_REGION_SIZE,
      MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
      MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH
   )
   port map(
      RX_CLK     => DMA_CLK,
      RX_RESET   => DMA_RESET,
      RX_DATA    => RX_MFB_DATA,
      RX_SOF_POS => RX_MFB_SOF_POS,
      RX_EOF_POS => RX_MFB_EOF_POS,
      RX_SOF     => RX_MFB_SOF,
      RX_EOF     => RX_MFB_EOF,
      RX_SRC_RDY => RX_MFB_SRC_RDY,
      RX_DST_RDY => RX_MFB_DST_RDY,

      TX_CLK     => PCIE_CLK,
      TX_RESET   => PCIE_RESET,
      TX_DATA    => s_fifo_data,
      TX_SOF_POS => s_fifo_sof_pos,
      TX_EOF_POS => s_fifo_eof_pos,
      TX_SOF     => s_fifo_sof,
      TX_EOF     => s_fifo_eof,
      TX_SRC_RDY => s_fifo_src_rdy,
      TX_DST_RDY => s_fifo_dst_rdy
   );

   sum_stored_eof_i : entity work.SUM_ONE
   generic map(
      INPUT_WIDTH => MFB_REGIONS,
      OUTPUT_REG  => True
   )
   port map(
      CLK      => PCIE_CLK,
      RESET    => PCIE_RESET,
      -- Input ports
      DIN      => s_fifo_eof,
      DIN_MASK => (others => '1'),
      DIN_VLD  => s_fifo_src_rdy and s_fifo_dst_rdy,
      -- Output ports
      DOUT     => s_codapa_inc,
      DOUT_VLD => s_codapa_inc_vld
   );

   --codapa_inc_cdc_i : entity work.ASFIFO_BRAM
   --generic map(
   --   ITEMS           => 128,
   --   DATA_WIDTH      => log2(MFB_REGIONS+1),
   --   RESET_DATA_PATH => false,
   --   AUTO_PIPELINE   => true
   --)
   --port map(
   --   CLK_WR => DMA_CLK,
   --   RST_WR => DMA_RESET,
   --   WR     => s_codapa_inc_vld,
   --   DI     => s_codapa_inc,
   --   FULL   => s_codapa_inc_cdc_full,
   --   STATUS => open,
--
   --   CLK_RD => PCIE_CLK,
   --   RST_RD => PCIE_RESET,
   --   RD     => '1',
   --   DO     => s_codapa_inc_sync,
   --   DO_DV  => s_codapa_inc_sync_vld,
   --   EMPTY  => s_codapa_inc_cdc_empty
   --);

   codapa_inc_sync_reg_p : process (PCIE_CLK)
   begin
      if (rising_edge(PCIE_CLK)) then
         if (PCIE_RESET = '1') then
            s_codapa_inc_sync_reg <= (others => '0');
         elsif (s_codapa_inc_vld = '1') then
            s_codapa_inc_sync_reg <= s_codapa_inc;
         else
            s_codapa_inc_sync_reg <= (others => '0');
         end if;
      end if;
   end process;

   mvb_g : for i in 0 to MVB_ITEMS-1 generate
      s_mvb_data((i+1)*(MVB_ITEM_WIDTH-1)-1 downto i*(MVB_ITEM_WIDTH-1)) <= RX_MVB_DATA((i+1)*MVB_ITEM_WIDTH-1 downto i*MVB_ITEM_WIDTH+1);
      s_mvb_be((i+1)*8-1 downto i*8) <= RX_MVB_DATA(i*MVB_ITEM_WIDTH+8+1-1 downto i*MVB_ITEM_WIDTH+1);
      s_mvb_payload(i) <= RX_MVB_DATA(i*MVB_ITEM_WIDTH);
      s_mvb_payload_size((i+1)*TRANS_SIZE_WIDTH-1 downto i*TRANS_SIZE_WIDTH) <= RX_MVB_DATA(i*MVB_ITEM_WIDTH+1+75-1 downto i*MVB_ITEM_WIDTH+1+64);
   end generate;

   codapa_checker_i : entity work.PTC_CODAPA_CHECKER
   generic map(
      MVB_ITEMS        => MVB_ITEMS,
      MVB_ITEM_WIDTH   => MVB_ITEM_WIDTH-1,
      TRANS_SIZE_WIDTH => TRANS_SIZE_WIDTH,
      CODAPA_INC_WIDTH => log2(MFB_REGIONS+1),
      CODAPA_CNT_WIDTH => CODAPA_CNT_WIDTH
   )
   port map(
      CLK            => PCIE_CLK,
      RESET          => PCIE_RESET,

      RX_MVB_DATA         => s_mvb_data,
      RX_MVB_BE           => s_mvb_be,
      RX_MVB_PAYLOAD      => s_mvb_payload,
      RX_MVB_PAYLOAD_SIZE => s_mvb_payload_size,
      RX_MVB_TYPE         => (others => '1'),
      RX_MVB_VLD          => RX_MVB_VLD,
      RX_MVB_SRC_RDY      => RX_MVB_SRC_RDY,
      RX_MVB_DST_RDY      => RX_MVB_DST_RDY,

      RX_CODAPA_INC  => s_codapa_inc_sync_reg,

      TX_MVB_DATA         => s_codapa_mvb_data,
      TX_MVB_BE           => s_codapa_mvb_be,
      TX_MVB_PAYLOAD      => s_codapa_mvb_payload,
      TX_MVB_PAYLOAD_SIZE => s_codapa_mvb_payload_size,
      TX_MVB_TYPE         => s_codapa_mvb_type,
      TX_MVB_VLD          => s_codapa_mvb_vld,
      TX_MVB_SRC_RDY      => s_codapa_mvb_src_rdy,
      TX_MVB_DST_RDY      => s_codapa_mvb_dst_rdy
   );

   dut_i : entity work.PTC_HDR_DATA_MERGE
   generic map(
      MFB_REGIONS         => MFB_REGIONS,
      MFB_REGION_SIZE     => MFB_REGION_SIZE,
      MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
      MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
      MVB_ITEMS           => MVB_ITEMS,
      MVB_ITEM_WIDTH      => MVB_ITEM_WIDTH-1,
      TRANS_SIZE_WIDTH    => TRANS_SIZE_WIDTH,
      MFB_FIFO_DEPTH      => HDM_MFB_FIFO_DEPTH
   )
   port map(
      CLK            => PCIE_CLK,
      RESET          => PCIE_RESET,

      RX_MVB_DATA         => s_codapa_mvb_data,
      RX_MVB_BE           => s_codapa_mvb_be,
      RX_MVB_PAYLOAD      => s_codapa_mvb_payload,
      RX_MVB_PAYLOAD_SIZE => s_codapa_mvb_payload_size,
      RX_MVB_TYPE         => s_codapa_mvb_type,
      RX_MVB_VLD          => s_codapa_mvb_vld,
      RX_MVB_SRC_RDY      => s_codapa_mvb_src_rdy,
      RX_MVB_DST_RDY      => s_codapa_mvb_dst_rdy,

      RX_MFB_DATA    => s_fifo_data,
      RX_MFB_SOF_POS => s_fifo_sof_pos,
      RX_MFB_EOF_POS => s_fifo_eof_pos,
      RX_MFB_SOF     => s_fifo_sof,
      RX_MFB_EOF     => s_fifo_eof,
      RX_MFB_SRC_RDY => s_fifo_src_rdy,
      RX_MFB_DST_RDY => s_fifo_dst_rdy,

      TX_MFB_DATA    => TX_MFB_DATA,
      TX_MFB_SOF_POS => TX_MFB_SOF_POS,
      TX_MFB_EOF_POS => TX_MFB_EOF_POS,
      TX_MFB_SOF     => TX_MFB_SOF,
      TX_MFB_EOF     => TX_MFB_EOF,
      TX_MFB_SRC_RDY => TX_MFB_SRC_RDY,
      TX_MFB_DST_RDY => TX_MFB_DST_RDY,
      TX_MFB_BE      => TX_MFB_BE
   );

end architecture;
