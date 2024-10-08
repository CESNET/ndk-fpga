-- mfb_splitter.vhd: MFB+MVB bus splitter
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                           Entity Declaration
-- ----------------------------------------------------------------------------

-- Splits RX MFB+MVB interface to two intefaces.
-- Switches packets based on one bit SWITCH for each MVB header.
entity MFB_SPLITTER is
   generic (
      -- ======================
      -- TX MVB characteristics
      -- ======================

      -- number of headers
      MVB_ITEMS       : integer := 2;
      -- width of each MVB meta item
      MVB_META_WIDTH  : integer := 2;

      -- ======================
      -- TX MFB characteristics
      -- ======================

      -- number of regions in word
      MFB_REGIONS     : integer := 2;
      -- number of blocks in region
      MFB_REG_SIZE    : integer := 1;
      -- number of items in block
      MFB_BLOCK_SIZE  : integer := 8;
      -- width  of one item (in bits)
      MFB_ITEM_WIDTH  : integer := 32;

      -- ===================
      -- Others
      -- ===================

      -- Width of each MVB item
      -- DMA_DOWNHDR_WIDTH, DMA_UPHDR_WIDTH
      HDR_WIDTH       : integer := DMA_DOWNHDR_WIDTH;

      -- Size of mvb output FIFOXs (in words)
      -- The minimum value is 2
      MVB_OUTPUT_FIFO_SIZE : integer := 8;

      -- Create output register PIPEs
      USE_OUTREG      : boolean := true;

      -- "ULTRASCALE", "7SERIES"
      DEVICE          : string  := "ULTRASCALE"
   );
   port(
      -- ======================
      -- Common interface
      -- ======================

      CLK             : in  std_logic;
      RESET           : in  std_logic;

      -- ======================
      -- RX interface
      -- ======================

      RX_MVB_HDR      : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH     -1 downto 0);
      RX_MVB_META     : in  std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0) := (others => '0');
      -- output select for each header
      RX_MVB_SWITCH   : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
      -- header contains payload in MFB
      RX_MVB_PAYLOAD  : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
      RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
      RX_MVB_SRC_RDY  : in  std_logic;
      RX_MVB_DST_RDY  : out std_logic;

      RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
      RX_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      RX_MFB_SRC_RDY  : in  std_logic;
      RX_MFB_DST_RDY  : out std_logic;

      -- ======================
      -- TX interface 0
      -- ======================

      TX0_MVB_HDR     : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
      TX0_MVB_META    : out std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
      TX0_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
      TX0_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
      TX0_MVB_SRC_RDY : out std_logic;
      TX0_MVB_DST_RDY : in  std_logic;

      TX0_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX0_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX0_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX0_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
      TX0_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX0_MFB_SRC_RDY : out std_logic;
      TX0_MFB_DST_RDY : in  std_logic;

      -- ======================
      -- TX interface 1
      -- ======================

      TX1_MVB_HDR     : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
      TX1_MVB_META    : out std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
      TX1_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
      TX1_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
      TX1_MVB_SRC_RDY : out std_logic;
      TX1_MVB_DST_RDY : in  std_logic;

      TX1_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX1_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX1_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX1_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
      TX1_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX1_MFB_SRC_RDY : out std_logic;
      TX1_MFB_DST_RDY : in  std_logic

   );
end entity MFB_SPLITTER;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of MFB_SPLITTER is

   ---------------------------------------------------------------------------
   -- Constants
   ---------------------------------------------------------------------------

   constant MFB_REG_DATA_WIDTH : integer := RX_MFB_DATA'length+RX_MFB_SOF'length+RX_MFB_EOF'length+RX_MFB_SOF_POS'length+RX_MFB_EOF_POS'length;

   ---------------------------------------------------------------------------

   ---------------------------------------------------------------------------
   -- Signals
   ---------------------------------------------------------------------------

   -- Valid for input MVB separated by its switch
   signal RX0_MVB_VLD : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal RX1_MVB_VLD : std_logic_vector(MVB_ITEMS-1 downto 0);

   -- switch fifoxm interface
   signal switch_fifoxm_di    : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal switch_fifoxm_wr    : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal switch_fifoxm_full  : std_logic;
   signal switch_fifoxm_do    : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal switch_fifoxm_rd    : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal switch_fifoxm_empty : std_logic_vector(MVB_ITEMS-1 downto 0);

   signal switch_fifoxm_empty_sh : std_logic_vector(MVB_ITEMS+1-1 downto 0);

   signal RX_MFB_SOF_cnt        : u_array_t(MFB_REGIONS+1-1 downto 0)(log2(MFB_REGIONS+1)-1 downto 0);
   signal switch_fifoxm_do_dist : std_logic_vector(MVB_ITEMS-1 downto 0);

   signal mfb_spl_rx_src_rdy : std_logic;
   signal mfb_spl_rx_dst_rdy : std_logic;

   -- MFB sending decision signals
   signal can_send_whole     : std_logic;                                -- '1' <-> ready to send the whole RX MFB word

   -- MFB output reg signals
   signal tx_mfb_reg_in_data     : slv_array_t(2-1 downto 0)(MFB_REG_DATA_WIDTH-1 downto 0);
   signal tx_mfb_reg_in_src_rdy  : std_logic_vector(2-1 downto 0);
   signal tx_mfb_reg_in_dst_rdy  : std_logic_vector(2-1 downto 0);
   signal tx_mfb_reg_out_data    : slv_array_t(2-1 downto 0)(MFB_REG_DATA_WIDTH-1 downto 0);
   signal tx_mfb_reg_out_src_rdy : std_logic_vector(2-1 downto 0);
   signal tx_mfb_reg_out_dst_rdy : std_logic_vector(2-1 downto 0);

   -- MVB output fifox signals
   signal mvb_out_fifox_di    : slv_array_t(1 downto 0)(MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2)-1 downto 0);
   signal mvb_out_fifox_wr    : std_logic_vector(1 downto 0);
   signal mvb_out_fifox_full  : std_logic_vector(1 downto 0);
   signal mvb_out_fifox_do    : slv_array_t(1 downto 0)(MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2)-1 downto 0);
   signal mvb_out_fifox_rd    : std_logic_vector(1 downto 0);
   signal mvb_out_fifox_empty : std_logic_vector(1 downto 0);

   ---------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- Switching information fifo
   -- -------------------------------------------------------------------------

   switch_fifoxm_input_gen : for i in 0 to MVB_ITEMS-1 generate
      switch_fifoxm_di(i) <= RX_MVB_SWITCH(i);
      switch_fifoxm_wr(i) <= '1' when RX_MVB_VLD(i)='1' and RX_MVB_SRC_RDY='1' and RX_MVB_PAYLOAD(i)='1' and mvb_out_fifox_full="00" else '0';
   end generate;

   switch_fifoxm_i : entity work.FIFOX_MULTI(SHAKEDOWN)
   generic map(
      DATA_WIDTH     => 1        ,
      ITEMS          => MVB_ITEMS*2*MVB_OUTPUT_FIFO_SIZE,
      WRITE_PORTS    => MVB_ITEMS,
      READ_PORTS     => MVB_ITEMS,
      RAM_TYPE       => "AUTO"   ,
      SAFE_READ_MODE => true     ,
      DEVICE         => DEVICE
   )
   port map(
      CLK    => CLK  ,
      RESET  => RESET,

      DI     => switch_fifoxm_di   ,
      WR     => switch_fifoxm_wr   ,
      FULL   => switch_fifoxm_full ,
      DO     => switch_fifoxm_do   ,
      RD     => switch_fifoxm_rd   ,
      EMPTY  => switch_fifoxm_empty
   );

   switch_fifoxm_rd_gen : for i in 0 to MFB_REGIONS-1 generate
      switch_fifoxm_rd(i) <= '1' when can_send_whole='1' and i<RX_MFB_SOF_cnt(MFB_REGIONS) and RX_MFB_SRC_RDY='1' and mfb_spl_rx_dst_rdy='1' else '0';
   end generate;

   -- shift empty signal
   switch_fifoxm_empty_sh <= switch_fifoxm_empty & '0';

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- MFB sending
   -- -------------------------------------------------------------------------

   -- Distribute switch info according to current RX_MFB_SOF positions
   switch_dist_pr : process (switch_fifoxm_do,RX_MFB_SOF,RX_MFB_SOF_cnt)
      variable cnt : integer;
   begin
      -- count number of SOFs before each region
      for i in 0 to MFB_REGIONS+1-1 loop
         cnt := 0;
         for e in 0 to i-1 loop
            if (RX_MFB_SOF(e)='1') then
               cnt := cnt+1;
            end if;
         end loop;
         RX_MFB_SOF_cnt(i) <= to_unsigned(cnt,log2(MFB_REGIONS+1));
      end loop;

      -- distribute
      switch_fifoxm_do_dist <= (others => switch_fifoxm_do(0));
      for i in 0 to MFB_REGIONS-1 loop
         switch_fifoxm_do_dist(i) <= switch_fifoxm_do(to_integer(RX_MFB_SOF_cnt(i)));
      end loop;
   end process;

   -- RX MFB can be passed when there is at least as much switch info on switch fifoxm output as there is SOFs in the RX MFB
   can_send_whole <= '1' when switch_fifoxm_empty_sh(to_integer(RX_MFB_SOF_cnt(MFB_REGIONS)))='0' else '0';

   mfb_spl_rx_src_rdy <= '1' when can_send_whole='1' and RX_MFB_SRC_RDY='1' else '0';

   RX_MFB_DST_RDY <= '1' when can_send_whole='1' and mfb_spl_rx_dst_rdy='1' else '0';

   mfb_splitter_i : entity work.MFB_SPLITTER_SIMPLE
   generic map(
      REGIONS     => MFB_REGIONS   ,
      REGION_SIZE => MFB_REG_SIZE  ,
      BLOCK_SIZE  => MFB_BLOCK_SIZE,
      ITEM_WIDTH  => MFB_ITEM_WIDTH,
      META_WIDTH  => 0
   )
   port map(
      CLK => CLK  ,
      RST => RESET,

      RX_MFB_META     => (others => '0'),
      RX_MFB_SEL      => switch_fifoxm_do_dist,
      RX_MFB_DATA     => RX_MFB_DATA   ,
      RX_MFB_SOF      => RX_MFB_SOF    ,
      RX_MFB_EOF      => RX_MFB_EOF    ,
      RX_MFB_SOF_POS  => RX_MFB_SOF_POS,
      RX_MFB_EOF_POS  => RX_MFB_EOF_POS,
      RX_MFB_SRC_RDY  => mfb_spl_rx_src_rdy,
      RX_MFB_DST_RDY  => mfb_spl_rx_dst_rdy,

      TX0_MFB_META    => open           ,
      TX0_MFB_DATA    => TX0_MFB_DATA   ,
      TX0_MFB_SOF     => TX0_MFB_SOF    ,
      TX0_MFB_EOF     => TX0_MFB_EOF    ,
      TX0_MFB_SOF_POS => TX0_MFB_SOF_POS,
      TX0_MFB_EOF_POS => TX0_MFB_EOF_POS,
      TX0_MFB_SRC_RDY => TX0_MFB_SRC_RDY,
      TX0_MFB_DST_RDY => TX0_MFB_DST_RDY,

      TX1_MFB_META    => open           ,
      TX1_MFB_DATA    => TX1_MFB_DATA   ,
      TX1_MFB_SOF     => TX1_MFB_SOF    ,
      TX1_MFB_EOF     => TX1_MFB_EOF    ,
      TX1_MFB_SOF_POS => TX1_MFB_SOF_POS,
      TX1_MFB_EOF_POS => TX1_MFB_EOF_POS,
      TX1_MFB_SRC_RDY => TX1_MFB_SRC_RDY,
      TX1_MFB_DST_RDY => TX1_MFB_DST_RDY
   );

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- MVB Output FIFOXs
   -- -------------------------------------------------------------------------

   -- RX MVB VLD generation for each output
   rx_mvb_vld_gen : for i in 0 to MVB_ITEMS-1 generate
      RX0_MVB_VLD(i) <= '1' when RX_MVB_SWITCH(i)='0' and RX_MVB_VLD(i)='1' and RX_MVB_SRC_RDY='1' else '0';
      RX1_MVB_VLD(i) <= '1' when RX_MVB_SWITCH(i)='1' and RX_MVB_VLD(i)='1' and RX_MVB_SRC_RDY='1' else '0';
   end generate;

   -- RX MVB DST RDY
   RX_MVB_DST_RDY <= '1' when switch_fifoxm_full='0' and mvb_out_fifox_full="00" else '0';

   -- MVB out fifox input
   mvb_out_fifox_wr(0) <= '1' when mvb_out_fifox_full(1)='0' and RX_MVB_SRC_RDY='1' and (or RX0_MVB_VLD)='1' and switch_fifoxm_full='0' else '0';
   mvb_out_fifox_wr(1) <= '1' when mvb_out_fifox_full(0)='0' and RX_MVB_SRC_RDY='1' and (or RX1_MVB_VLD)='1' and switch_fifoxm_full='0' else '0';

   mvb_out_fifox_di(0)(MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2)-1 downto MVB_ITEMS*(MVB_META_WIDTH+2)) <= RX_MVB_HDR;
   mvb_out_fifox_di(0)(MVB_ITEMS*(MVB_META_WIDTH+2)-1 downto MVB_ITEMS*2) <= RX_MVB_META;
   mvb_out_fifox_di(0)(MVB_ITEMS*2-1 downto MVB_ITEMS) <= RX_MVB_PAYLOAD;
   mvb_out_fifox_di(0)(MVB_ITEMS-1 downto 0) <= RX0_MVB_VLD;
   mvb_out_fifox_di(1)(MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2)-1 downto MVB_ITEMS*(MVB_META_WIDTH+2)) <= RX_MVB_HDR;
   mvb_out_fifox_di(1)(MVB_ITEMS*(MVB_META_WIDTH+2)-1 downto MVB_ITEMS*2) <= RX_MVB_META;
   mvb_out_fifox_di(1)(MVB_ITEMS*2-1 downto MVB_ITEMS) <= RX_MVB_PAYLOAD;
   mvb_out_fifox_di(1)(MVB_ITEMS-1 downto 0) <= RX1_MVB_VLD;

   mvb_out_fifox_ge : for i in 0 to 1 generate
      mvb_out_fifox_i : entity work.FIFOX
      generic map (
         DATA_WIDTH => MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2),
         ITEMS      => MVB_OUTPUT_FIFO_SIZE,
         RAM_TYPE   => "AUTO",
         DEVICE     => DEVICE
      )
      port map (
         CLK   => CLK  ,
         RESET => RESET,

         DI    => mvb_out_fifox_di(i)   ,
         WR    => mvb_out_fifox_wr(i)   ,
         FULL  => mvb_out_fifox_full(i) ,

         DO    => mvb_out_fifox_do(i)   ,
         RD    => mvb_out_fifox_rd(i)   ,
         EMPTY => mvb_out_fifox_empty(i)
      );
   end generate;

   -- TX MVB
   TX0_MVB_HDR         <= mvb_out_fifox_do(0)(MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2)-1 downto MVB_ITEMS*(MVB_META_WIDTH+2));
   TX0_MVB_META        <= mvb_out_fifox_do(0)(MVB_ITEMS*(MVB_META_WIDTH+2)-1 downto MVB_ITEMS*2);
   TX0_MVB_PAYLOAD     <= mvb_out_fifox_do(0)(MVB_ITEMS*2-1 downto MVB_ITEMS);
   TX0_MVB_VLD         <= mvb_out_fifox_do(0)(MVB_ITEMS-1 downto 0);
   TX0_MVB_SRC_RDY     <= not mvb_out_fifox_empty(0);
   mvb_out_fifox_rd(0) <= TX0_MVB_DST_RDY;

   TX1_MVB_HDR         <= mvb_out_fifox_do(1)(MVB_ITEMS*(HDR_WIDTH+MVB_META_WIDTH+2)-1 downto MVB_ITEMS*(MVB_META_WIDTH+2));
   TX1_MVB_META        <= mvb_out_fifox_do(1)(MVB_ITEMS*(MVB_META_WIDTH+2)-1 downto MVB_ITEMS*2);
   TX1_MVB_PAYLOAD     <= mvb_out_fifox_do(1)(MVB_ITEMS*2-1 downto MVB_ITEMS);
   TX1_MVB_VLD         <= mvb_out_fifox_do(1)(MVB_ITEMS-1 downto 0);
   TX1_MVB_SRC_RDY     <= not mvb_out_fifox_empty(1);
   mvb_out_fifox_rd(1) <= TX1_MVB_DST_RDY;

   -- -------------------------------------------------------------------------

end architecture;
