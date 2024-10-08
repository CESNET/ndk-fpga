-- dma2mfb.vhd: DMA to MFB+MVB interface convertor
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------
-- Converts DMA Up interface to MFB+MVB Down interface.
-- MFB and MVB can have multiple regions.
-- DMA only has 1 region.

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity DMA2MFB is
   generic (
      -- =======================
      -- TX MVB characteristics
      -- =======================

      -- number of headers
      MVB_ITEMS       : integer := 2;
      -- =======================
      -- TX MFB characteristics
      -- =======================

      -- number of regions in word
      MFB_REGIONS     : integer := 2;
      -- number of blocks in region
      MFB_REG_SIZE    : integer := 1;
      -- number of items in block
      MFB_BLOCK_SIZE  : integer := 8;
      -- Width of one item (in bits)
      MFB_ITEM_WIDTH  : integer := 32;

      -- Width of MVB and DMA headers is defined in dma_bus_pack
      -- Width of MFB data and DMA data is MFB_REGIONS * MFB_REG_SIZE * MFB_BLOCK_SIZE * MFB_ITEM_WIDTH

      -- Only extract Read request headers to output MVB
      -- Write request headers will be propagated in TX_MFB_HDR signal
      EXTRACT_READ_ONLY : boolean := false;

      -- Enables a small (32 items) FIFO on the MFB output
      -- This eliminates througput problems, which might be caused by the unit propagating MVB header
      -- only after all MFB data of the previous transaction have been sent out.
      OUT_FIFO_EN : boolean := false;
      -- Target device
      DEVICE      : string  := "NONE"
   );
   port(
      -- ========================================================================
      -- Common interface
      -- ========================================================================

      CLK             : in  std_logic;
      RESET           : in  std_logic;

      -- ========================================================================
      -- RX DMA interface
      -- ========================================================================

      RX_DMA_UP_HDR     : in  std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);
      RX_DMA_UP_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_DMA_UP_SOP     : in  std_logic;
      RX_DMA_UP_EOP     : in  std_logic;
      RX_DMA_UP_SRC_RDY : in  std_logic;
      RX_DMA_UP_DST_RDY : out std_logic;

      -- ========================================================================
      -- TX MVB interface
      -- ========================================================================

      TX_MVB_UP_HDR      : out std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
      TX_MVB_UP_VLD      : out std_logic_vector(MVB_ITEMS                -1 downto 0);
      TX_MVB_UP_SRC_RDY  : out std_logic;
      TX_MVB_UP_DST_RDY  : in  std_logic;

      -- ========================================================================
      -- TX MFB interface
      -- ========================================================================

      TX_MFB_UP_HDR     : out std_logic_vector(MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
      TX_MFB_UP_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX_MFB_UP_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_UP_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_UP_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
      TX_MFB_UP_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX_MFB_UP_SRC_RDY : out std_logic;
      TX_MFB_UP_DST_RDY : in  std_logic
   );
end entity DMA2MFB;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of DMA2MFB is

   -- ========================================================================
   -- Constants
   -- ========================================================================

   constant EOF_POS_WIDTH : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));

   ---------------------------------------------------------------------------

   ---------------------------------------------------------------------------
   -- Signals
   ---------------------------------------------------------------------------

   signal header_sent_reg      : std_logic; -- transaction header already send
   signal header_len_reg       : unsigned(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low downto 0);
   signal header_type          : std_logic_vector(1-1 downto 0); -- currently valid header type
   signal header_len           : unsigned(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low downto 0);
   signal is_write             : std_logic;
   signal request_length_sub1  : std_logic_vector(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low downto 0);

   signal pre_fifo_tx_mfb_up_hdr       : std_logic_vector(MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
   signal pre_fifo_tx_mfb_up_data      : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
   signal pre_fifo_tx_mfb_up_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal pre_fifo_tx_mfb_up_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal pre_fifo_tx_mfb_up_sof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
   signal pre_fifo_tx_mfb_up_eof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
   signal pre_fifo_tx_mfb_up_src_rdy   : std_logic;
   signal pre_fifo_tx_mfb_up_dst_rdy   : std_logic;

   ---------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- Interface conversion
   -- -------------------------------------------------------------------------

   header_rdy_reg_pr : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RX_DMA_UP_SRC_RDY='1' and TX_MVB_UP_DST_RDY='1' and (pre_fifo_tx_mfb_up_dst_rdy='1' or is_write='0')) then
            header_sent_reg <= '1';
            header_len_reg  <= header_len;
         end if;

         if (RX_DMA_UP_SRC_RDY='1' and RX_DMA_UP_DST_RDY='1' and RX_DMA_UP_EOP='1') then
            header_sent_reg <= '0';
         end if;

         if (RESET='1') then
            header_sent_reg <= '0';
         end if;
      end if;
   end process;

   header_type <= RX_DMA_UP_HDR(DMA_REQUEST_TYPE) when header_sent_reg='0' else DMA_TYPE_WRITE; -- only write transactions are sent in multiple CLK ticks
   is_write    <= '1' when header_type=DMA_TYPE_WRITE else '0';
   header_len  <= unsigned(RX_DMA_UP_HDR(DMA_REQUEST_LENGTH)) when header_sent_reg='0' else header_len_reg;
   request_length_sub1 <= std_logic_vector(header_len - 1);

   dma2mfb_pr : process (all)
   begin
      TX_MVB_UP_HDR                             <= (others => '0');
      TX_MVB_UP_HDR(DMA_UPHDR_WIDTH-1 downto 0) <= RX_DMA_UP_HDR;
      TX_MVB_UP_VLD                             <= (others => '0');
      TX_MVB_UP_VLD(0)                          <= RX_DMA_UP_SRC_RDY and (not header_sent_reg);
      TX_MVB_UP_SRC_RDY                         <= '1' when RX_DMA_UP_SRC_RDY='1' and header_sent_reg='0' and (pre_fifo_tx_mfb_up_dst_rdy='1' or is_write='0') and (is_write='0' or (not EXTRACT_READ_ONLY)) else '0';

      pre_fifo_tx_mfb_up_hdr(DMA_UPHDR_WIDTH-1 downto 0) <= RX_DMA_UP_HDR;
      pre_fifo_tx_mfb_up_data    <= RX_DMA_UP_DATA;
      pre_fifo_tx_mfb_up_src_rdy <= RX_DMA_UP_SRC_RDY and is_write and TX_MVB_UP_DST_RDY;

      pre_fifo_tx_mfb_up_sof     <= (0 => (RX_DMA_UP_SOP and is_write), others => '0');
      pre_fifo_tx_mfb_up_sof_pos <= (others => '0');

      pre_fifo_tx_mfb_up_eof  <= (others => '0');
      pre_fifo_tx_mfb_up_eof(to_integer(unsigned(request_length_sub1(
               EOF_POS_WIDTH+log2(MFB_REGIONS)-1 downto EOF_POS_WIDTH))))
               <= (RX_DMA_UP_EOP and is_write);
      for i in 0 to MFB_REGIONS-1 loop
         pre_fifo_tx_mfb_up_eof_pos(EOF_POS_WIDTH*(i+1)-1 downto EOF_POS_WIDTH*i)
               <= std_logic_vector(unsigned(request_length_sub1(EOF_POS_WIDTH-1 downto 0)));
      end loop;

      RX_DMA_UP_DST_RDY <= TX_MVB_UP_DST_RDY and (pre_fifo_tx_mfb_up_dst_rdy or (not is_write));
   end process;

   -- -------------------------------------------------------------------------

   tx_mfb_gen : if (OUT_FIFO_EN=false) generate

      -- -------------------------------------------------------------------------
      -- TX MFB propagation
      -- -------------------------------------------------------------------------

      TX_MFB_UP_HDR     <= pre_fifo_tx_mfb_up_hdr    ;
      TX_MFB_UP_DATA    <= pre_fifo_tx_mfb_up_data   ;
      TX_MFB_UP_SOF     <= pre_fifo_tx_mfb_up_sof    ;
      TX_MFB_UP_EOF     <= pre_fifo_tx_mfb_up_eof    ;
      TX_MFB_UP_SOF_POS <= pre_fifo_tx_mfb_up_sof_pos;
      TX_MFB_UP_EOF_POS <= pre_fifo_tx_mfb_up_eof_pos;
      TX_MFB_UP_SRC_RDY <= pre_fifo_tx_mfb_up_src_rdy;
      pre_fifo_tx_mfb_up_dst_rdy <= TX_MFB_UP_DST_RDY;

      -- -------------------------------------------------------------------------

   else generate

      -- -------------------------------------------------------------------------
      -- TX MFB FIFO
      -- -------------------------------------------------------------------------

      tx_mfb_fifox_i : entity work.MFB_FIFOX
      generic map (
         REGIONS             => MFB_REGIONS    ,
         REGION_SIZE         => MFB_REG_SIZE   ,
         BLOCK_SIZE          => MFB_BLOCK_SIZE ,
         ITEM_WIDTH          => MFB_ITEM_WIDTH ,
         FIFO_DEPTH          => 32             ,
         RAM_TYPE            => string'("AUTO"),
         DEVICE              => DEVICE         ,
         ALMOST_FULL_OFFSET  => 0              ,
         ALMOST_EMPTY_OFFSET => 0
      )
      port map (
         CLK         => CLK  ,
         RST         => RESET,

         RX_DATA     => pre_fifo_tx_mfb_up_data   ,
         RX_SOF      => pre_fifo_tx_mfb_up_sof    ,
         RX_EOF      => pre_fifo_tx_mfb_up_eof    ,
         RX_SOF_POS  => pre_fifo_tx_mfb_up_sof_pos,
         RX_EOF_POS  => pre_fifo_tx_mfb_up_eof_pos,
         RX_SRC_RDY  => pre_fifo_tx_mfb_up_src_rdy,
         RX_DST_RDY  => pre_fifo_tx_mfb_up_dst_rdy,

         TX_DATA     => TX_MFB_UP_DATA   ,
         TX_SOF      => TX_MFB_UP_SOF    ,
         TX_EOF      => TX_MFB_UP_EOF    ,
         TX_SOF_POS  => TX_MFB_UP_SOF_POS,
         TX_EOF_POS  => TX_MFB_UP_EOF_POS,
         TX_SRC_RDY  => TX_MFB_UP_SRC_RDY,
         TX_DST_RDY  => TX_MFB_UP_DST_RDY,

         FIFO_STATUS => open,
         FIFO_AFULL  => open,
         FIFO_AEMPTY => open
      );

      -- -------------------------------------------------------------------------

   end generate;

end architecture;
