-- mfb2dma.vhd: MFB+MVB to DMA interface convertor
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
-- Converts MFB+MVB Down interface to DMA Down interface.
-- MFB and MVB can have multiple regions.
-- DMA only has 1 region. Might leads to decrease of throughput.

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity MFB2DMA is
   generic (
      -- =======================
      -- RX MVB characteristics
      -- =======================

      -- number of headers
      MVB_ITEMS       : integer := 4;
      -- =======================
      -- RX MFB characteristics
      -- =======================

      MFB_REGIONS     : integer := 4;
      -- Width of one region (in bits)
      MFB_REG_WIDTH   : integer := 256;

      -- Width of MVB and DMA headers is defined in dma_bus_pack
      -- Width of MFB data and DMA data is MFB_REGIONS * MFB_REG_WIDTH

      -- Use RX MVB as source of DMA Headers
      -- When set to false, MFB_HDR signal is used instead
      USE_MVB         : boolean := true;

      -- Size of input FIFOX MULTI (in words)
      -- The minimum value is 2
      INPUT_FIFO_SIZE : integer := 8;

      DEVICE          : string  := "ULTRASCALE"
   );
   port(
      -- ========================================================================
      -- Common interface
      -- ========================================================================

      CLK             : in  std_logic;
      RESET           : in  std_logic;

      -- ========================================================================
      -- RX MVB interface
      --
      -- Only when USE_MVB=true
      -- ========================================================================

      RX_MVB_DOWN_HDR      : in  std_logic_vector(MVB_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0) := (others => '0');
      RX_MVB_DOWN_VLD      : in  std_logic_vector(MVB_ITEMS                  -1 downto 0) := (others => '0');
      RX_MVB_DOWN_SRC_RDY  : in  std_logic := '0';
      RX_MVB_DOWN_DST_RDY  : out std_logic;

      -- ========================================================================
      -- RX MFB interface
      -- ========================================================================

      -- Only when USE_MVB=false; valid on SOF
      RX_MFB_DOWN_HDR     : in  std_logic_vector(MFB_REGIONS*DMA_DOWNHDR_WIDTH-1 downto 0) := (others => '0');
      RX_MFB_DOWN_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
      RX_MFB_DOWN_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_DOWN_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_DOWN_SRC_RDY : in  std_logic;
      RX_MFB_DOWN_DST_RDY : out std_logic;
      -- Only 1 block region size is supported!
      -- -- No shared regions.
      -- -- SOF_POS and EOF_POS are "don't care".
      --RX_MFB_DOWN_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      --RX_MFB_DOWN_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);

      -- ========================================================================
      -- TX DMA interface
      -- ========================================================================

      TX_DMA_DOWN_HDR     : out std_logic_vector(DMA_DOWNHDR_WIDTH-1 downto 0);
      TX_DMA_DOWN_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
      TX_DMA_DOWN_SOP     : out std_logic;
      TX_DMA_DOWN_EOP     : out std_logic;
      TX_DMA_DOWN_SRC_RDY : out std_logic;
      TX_DMA_DOWN_DST_RDY : in  std_logic
   );
end entity MFB2DMA;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of MFB2DMA is

   -- ========================================================================
   -- Constants
   -- ========================================================================

   constant INPUT_FIFOXM_SIZE : integer := max(MVB_ITEMS,MFB_REGIONS)*INPUT_FIFO_SIZE;
   constant DMA_LEN_WIDTH : integer := DMA_COMPLETION_LENGTH'high-DMA_COMPLETION_LENGTH'low+1;

   ---------------------------------------------------------------------------

   ---------------------------------------------------------------------------
   -- Signals
   ---------------------------------------------------------------------------

   -- MVB input register to increase latency
   signal rx_mvb_down_in_reg_hdr      : std_logic_vector(MVB_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
   signal rx_mvb_down_in_reg_vld      : std_logic_vector(MVB_ITEMS                  -1 downto 0);
   signal rx_mvb_down_in_reg_src_rdy  : std_logic;
   signal rx_mvb_down_in_reg_dst_rdy  : std_logic;

   -- Extended RX MFB signals
   signal RX_MFB_DOWN_DATA_ext    : std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
   signal RX_MFB_DOWN_SOF_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal RX_MFB_DOWN_EOF_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal RX_MFB_DOWN_VLD_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal RX_MFB_DOWN_SRC_RDY_ext : std_logic;
   signal RX_MFB_DOWN_DST_RDY_ext : std_logic;

   -- MVB fifox multi interface
   signal mvb_fifoxm_di     : std_logic_vector(MVB_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
   signal mvb_fifoxm_wr     : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal mvb_fifoxm_full   : std_logic;
   signal mvb_fifoxm_do     : std_logic_vector(1*DMA_DOWNHDR_WIDTH-1 downto 0);
   signal mvb_fifoxm_rd     : std_logic_vector(1-1 downto 0);
   signal mvb_fifoxm_empty  : std_logic_vector(1-1 downto 0);

   -- MFB fifox multi interface
   signal mfb_fifoxm_di     : std_logic_vector(MFB_REGIONS*(DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)-1 downto 0); -- regions *  msb( data + SOF + EOF )lsb
   signal mfb_fifoxm_wr     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal mfb_fifoxm_full   : std_logic;
   signal mfb_fifoxm_do     : std_logic_vector(MFB_REGIONS*(DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)-1 downto 0);
   signal mfb_fifoxm_rd     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal mfb_fifoxm_empty  : std_logic_vector(MFB_REGIONS-1 downto 0);

   -- MFB fifoxm output data separation
   signal mfb_fifoxm_do_hdr      : std_logic_vector(MFB_REGIONS*DMA_DOWNHDR_WIDTH-1 downto 0);
   signal mfb_fifoxm_do_data     : std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
   signal mfb_fifoxm_do_sof      : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal mfb_fifoxm_do_eof      : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal mfb_fifoxm_do_sof_vld  : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal mfb_fifoxm_do_eof_vld  : std_logic_vector(MFB_REGIONS-1 downto 0);

   -- fifoxm read enable signals
   signal read_header_reg : std_logic;
   signal mfb_reg_wanted  : std_logic_vector(MFB_REGIONS+1-1 downto 0);
   signal allow_read      : std_logic;

   -- output DMA register
   signal out_dma_down_hdr_reg  : std_logic_vector(DMA_DOWNHDR_WIDTH-1 downto 0);
   signal out_dma_down_data_reg : std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
   signal out_dma_down_sop_reg  : std_logic;
   signal out_dma_down_eop_reg  : std_logic;
   signal out_dma_down_reg_vld  : std_logic;

   ---------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- RX MFB extention unit
   -- -------------------------------------------------------------------------

   RX_MVB_DOWN_DST_RDY <= rx_mvb_down_in_reg_dst_rdy;

   rx_mvb_input_reg_pr : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (rx_mvb_down_in_reg_dst_rdy='1' and RX_MVB_DOWN_SRC_RDY='1') then
            rx_mvb_down_in_reg_hdr     <= RX_MVB_DOWN_HDR;
            rx_mvb_down_in_reg_vld     <= RX_MVB_DOWN_VLD;
            rx_mvb_down_in_reg_src_rdy <= RX_MVB_DOWN_SRC_RDY;
         elsif (rx_mvb_down_in_reg_dst_rdy='1') then
            rx_mvb_down_in_reg_src_rdy <= '0';
         end if;

         if (RESET='1') then
            rx_mvb_down_in_reg_src_rdy <= '0';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- RX MFB extention unit
   -- -------------------------------------------------------------------------

   rx_mfb_ext_i : entity work.MFB_AUXILIARY_SIGNALS
   generic map(
      REGIONS     => MFB_REGIONS  ,
      REGION_SIZE => 1            ,
      BLOCK_SIZE  => 1            ,
      ITEM_WIDTH  => MFB_REG_WIDTH,

      REGION_AUX_EN => True       ,
      BLOCK_AUX_EN  => False      ,
      ITEM_AUX_EN   => False
   )
   port map(
      CLK   => CLK  ,
      RESET => RESET,

      RX_DATA       => RX_MFB_DOWN_DATA       ,
      RX_SOF_POS    => (others => '0')        ,
      RX_EOF_POS    => (others => '0')        ,
      RX_SOF        => RX_MFB_DOWN_SOF        ,
      RX_EOF        => RX_MFB_DOWN_EOF        ,
      RX_SRC_RDY    => RX_MFB_DOWN_SRC_RDY    ,
      RX_DST_RDY    => RX_MFB_DOWN_DST_RDY    ,

      TX_DATA       => RX_MFB_DOWN_DATA_ext   ,
      TX_SOF_POS    => open                   ,
      TX_EOF_POS    => open                   ,
      TX_SOF        => RX_MFB_DOWN_SOF_ext    ,
      TX_EOF        => RX_MFB_DOWN_EOF_ext    ,
      TX_REGION_VLD => RX_MFB_DOWN_VLD_ext    ,
      TX_SRC_RDY    => RX_MFB_DOWN_SRC_RDY_ext,
      TX_DST_RDY    => RX_MFB_DOWN_DST_RDY_ext
   );

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- MVB input FIFOX multi
   -- -------------------------------------------------------------------------

   mvb_fifoxm_input_gen : for i in 0 to MVB_ITEMS-1 generate
      mvb_fifoxm_wr(i) <= rx_mvb_down_in_reg_vld(i) and rx_mvb_down_in_reg_src_rdy;
   end generate;
   mvb_fifoxm_di              <= rx_mvb_down_in_reg_hdr;
   rx_mvb_down_in_reg_dst_rdy <= not mvb_fifoxm_full;

   mvb_fifoxm_gen : if (USE_MVB) generate
      mvb_fifoxm_i : entity work.FIFOX_MULTI
      generic map(
         DATA_WIDTH  => DMA_DOWNHDR_WIDTH,
         ITEMS       => INPUT_FIFOXM_SIZE,
         WRITE_PORTS => MVB_ITEMS        ,
         READ_PORTS  => 1                ,
         RAM_TYPE    => "AUTO"           ,
         ALMOST_FULL_OFFSET  => 0,
         ALMOST_EMPTY_OFFSET => 0,
         SAFE_READ_MODE      => true,
         DEVICE      => DEVICE
      )
      port map(
         CLK    => CLK  ,
         RESET  => RESET,

         DI     => mvb_fifoxm_di   ,
         WR     => mvb_fifoxm_wr   ,
         FULL   => mvb_fifoxm_full ,
         DO     => mvb_fifoxm_do   ,
         RD     => mvb_fifoxm_rd   ,
         EMPTY  => mvb_fifoxm_empty
      );
   else generate
      -- Fake allways ready to eliminate connected logic
      mvb_fifoxm_full  <= '0';
      mvb_fifoxm_empty <= (others => '0');
   end generate;

   mvb_fifoxm_rd(0) <= '1' when (TX_DMA_DOWN_DST_RDY='1' or out_dma_down_reg_vld='0') and allow_read='1' and read_header_reg='1' and mfb_fifoxm_empty(0)='0' else '0';

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- MFB input FIFOX multi
   -- -------------------------------------------------------------------------

   mfb_fifoxm_input_gen : for i in 0 to MFB_REGIONS-1 generate
      mfb_fifoxm_wr(i) <= RX_MFB_DOWN_VLD_ext(i) and RX_MFB_DOWN_SRC_RDY_ext;
      mfb_fifoxm_di((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+1+1-1 downto (DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+MFB_REG_WIDTH+1+1) <= RX_MFB_DOWN_HDR(DMA_DOWNHDR_WIDTH*(i+1)-1 downto DMA_DOWNHDR_WIDTH*i);
      mfb_fifoxm_di((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+MFB_REG_WIDTH+1+1-1 downto (DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+1+1) <= RX_MFB_DOWN_DATA_ext(MFB_REG_WIDTH*(i+1)-1 downto MFB_REG_WIDTH*i);
      mfb_fifoxm_di((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+1)  <= RX_MFB_DOWN_SOF_ext(i);
      mfb_fifoxm_di((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i)    <= RX_MFB_DOWN_EOF_ext(i);
   end generate;
   RX_MFB_DOWN_DST_RDY_ext <= not mfb_fifoxm_full;

   mfb_fifoxm_i : entity work.FIFOX_MULTI
   generic map(
      DATA_WIDTH  => DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2,
      ITEMS       => INPUT_FIFOXM_SIZE,
      WRITE_PORTS => MFB_REGIONS      ,
      READ_PORTS  => MFB_REGIONS      ,
      RAM_TYPE    => "AUTO"           ,
      SAFE_READ_MODE      => false,
      ALMOST_FULL_OFFSET  => 0,
      ALMOST_EMPTY_OFFSET => 0,
      DEVICE      => DEVICE
   )
   port map(
      CLK    => CLK  ,
      RESET  => RESET,

      DI     => mfb_fifoxm_di   ,
      WR     => mfb_fifoxm_wr   ,
      FULL   => mfb_fifoxm_full ,
      DO     => mfb_fifoxm_do   ,
      RD     => mfb_fifoxm_rd   ,
      EMPTY  => mfb_fifoxm_empty
   );

   mfb_fifoxm_out_gen : for i in 0 to MFB_REGIONS-1 generate
      mfb_fifoxm_rd(i) <= '1' when (TX_DMA_DOWN_DST_RDY='1' or out_dma_down_reg_vld='0') and mfb_reg_wanted(i)='1' and allow_read='1' and (read_header_reg='0' or mvb_fifoxm_empty(0)='0') else '0';
      mfb_fifoxm_do_hdr(DMA_DOWNHDR_WIDTH*(i+1)-1 downto DMA_DOWNHDR_WIDTH*i) <= mfb_fifoxm_do((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+1+1-1 downto (DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+MFB_REG_WIDTH+1+1);
      mfb_fifoxm_do_data(MFB_REG_WIDTH*(i+1)-1 downto MFB_REG_WIDTH*i) <= mfb_fifoxm_do((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+MFB_REG_WIDTH+1+1-1 downto (DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+1+1);
      mfb_fifoxm_do_sof(i) <= mfb_fifoxm_do((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i+1);
      mfb_fifoxm_do_eof(i) <= mfb_fifoxm_do((DMA_DOWNHDR_WIDTH+MFB_REG_WIDTH+2)*i);

      mfb_fifoxm_do_sof_vld(i) <= '1' when mfb_fifoxm_do_sof(i)='1' and mfb_fifoxm_empty(i)='0' else '0';
      mfb_fifoxm_do_eof_vld(i) <= '1' when mfb_fifoxm_do_eof(i)='1' and mfb_fifoxm_empty(i)='0' else '0';
   end generate;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- wanted regions and header reading checking
   -- -------------------------------------------------------------------------

   wanted_reg_pr : process (mfb_fifoxm_do_eof_vld)
   begin
      mfb_reg_wanted(0) <= '1';
      for i in 1 to MFB_REGIONS+1-1 loop
         mfb_reg_wanted(i) <= (nor mfb_fifoxm_do_eof_vld(i-1 downto 0));
      end loop;
   end process;

   -- check for incomplete MFB word data
   read_allow_pr : process (mfb_fifoxm_do_eof,mfb_fifoxm_empty)
   begin
      allow_read <= '1';

      for i in 0 to MFB_REGIONS-1 loop
         if (mfb_fifoxm_empty(i)='1') then
            allow_read <= '0';
         end if;

         exit when (mfb_fifoxm_do_eof(i)='1');
      end loop;
   end process;

   read_header_reg_pr : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (TX_DMA_DOWN_DST_RDY='1' or out_dma_down_reg_vld='0') then
            if (read_header_reg='1') then
               -- want to read start of new packet
               if (mvb_fifoxm_empty(0)='0' and mfb_fifoxm_empty(0)='0' and mfb_reg_wanted(MFB_REGIONS)='1' and allow_read='1') then
                  -- reading start of packet, that continues to next word
                  read_header_reg <= '0';
               end if;
            else
               -- reading packet rest
               if (mfb_reg_wanted(MFB_REGIONS)='0') then
                  -- reading end of packet
                  read_header_reg <= '1';
               end if;
            end if;
         end if;

         if (RESET='1') then
            read_header_reg <= '1';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- Outout register
   -- -------------------------------------------------------------------------

   out_reg_pr : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (TX_DMA_DOWN_DST_RDY='1' or out_dma_down_reg_vld='0') then
            if (mfb_fifoxm_do_sof_vld(0)='1') then
               if (USE_MVB) then
                  out_dma_down_hdr_reg <= mvb_fifoxm_do;
               else
                  out_dma_down_hdr_reg <= mfb_fifoxm_do_hdr(DMA_DOWNHDR_WIDTH-1 downto 0);
               end if;
            end if;
            out_dma_down_data_reg <= mfb_fifoxm_do_data;
            out_dma_down_sop_reg  <= mfb_fifoxm_do_sof(0);
            out_dma_down_eop_reg  <= not mfb_reg_wanted(MFB_REGIONS);

            out_dma_down_reg_vld  <= '1' when mfb_fifoxm_empty(0)='0' and allow_read='1' and (read_header_reg='0' or mvb_fifoxm_empty(0)='0') else '0';
         end if;

         if (RESET='1') then
            out_dma_down_reg_vld <= '0';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- TX generation
   -- -------------------------------------------------------------------------

   TX_DMA_DOWN_HDR     <= out_dma_down_hdr_reg;
   TX_DMA_DOWN_DATA    <= out_dma_down_data_reg;
   TX_DMA_DOWN_SOP     <= out_dma_down_sop_reg;
   TX_DMA_DOWN_EOP     <= out_dma_down_eop_reg;
   TX_DMA_DOWN_SRC_RDY <= out_dma_down_reg_vld;

   -- -------------------------------------------------------------------------

end architecture;
