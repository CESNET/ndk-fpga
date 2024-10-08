-- ptc_storage_fifo.vhd: MVB+MFB completitions storage FIFO
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
--                             Entity
-- ----------------------------------------------------------------------------

entity PTC_STORAGE_FIFO is
   generic (
      -- ===================
      -- MVB characteristics
      -- ===================

      -- number of MVB items
      MVB_ITEMS       : integer := 4;
      -- number of MVB items
      MVB_ITEM_WIDTH  : integer := 3*4*8;

      -- ===================
      -- MFB characteristics
      -- ===================

      -- number of regions in word
      MFB_REGIONS     : integer := 4;
      -- number of blocks in region
      MFB_REG_SIZE    : integer := 1;
      -- number of items in block
      MFB_BLOCK_SIZE  : integer := 4;
      -- width  of one item (in bits)
      MFB_ITEM_WIDTH  : integer := 32;

      -- ===================
      -- Others
      -- ===================

      -- Number of MVB/MFB words space in main MVB/MFB storage FIFOX
      MAIN_FIFO_ITEMS        : integer := 512;

      -- Number of MFB words space in input MFB shakedown FIFOX Multi
      INPUT_MFB_FIFOXM_ITEMS : integer := 8;

      -- Target device
      -- "VIRTEX6", "7SERIES", "ULTRASCALE"
      DEVICE            : string  := "ULTRASCALE"
   );
   port(
      ---------------------------------------------------------------------------
      -- Common interface
      ---------------------------------------------------------------------------

      CLK              : in  std_logic;
      RESET            : in  std_logic;

      ---------------------------------------------------------------------------
      -- RX PCIe MVB interface
      ---------------------------------------------------------------------------

      RX_MVB_DATA      : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
      RX_MVB_VLD       : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
      RX_MVB_SRC_RDY   : in  std_logic;
      RX_MVB_DST_RDY   : out std_logic; -- always '1'

      ---------------------------------------------------------------------------
      -- RX MFB interface
      ---------------------------------------------------------------------------

      RX_MFB_DATA      : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_MFB_SOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_EOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_SOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
      RX_MFB_EOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      RX_MFB_SRC_RDY   : in  std_logic;
      RX_MFB_DST_RDY   : out std_logic; -- always '1'

      ---------------------------------------------------------------------------
      -- TX PCIe MVB interface
      ---------------------------------------------------------------------------

      TX_MVB_DATA      : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
      TX_MVB_VLD       : out std_logic_vector(MVB_ITEMS               -1 downto 0);
      TX_MVB_SRC_RDY   : out std_logic;
      TX_MVB_DST_RDY   : in  std_logic;

      ---------------------------------------------------------------------------
      -- TX MFB interface
      ---------------------------------------------------------------------------

      TX_MFB_DATA      : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX_MFB_SOF       : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_EOF       : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_SOF_POS   : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
      TX_MFB_EOF_POS   : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX_MFB_SRC_RDY   : out std_logic;
      TX_MFB_DST_RDY   : in  std_logic

   );
end entity PTC_STORAGE_FIFO;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PTC_STORAGE_FIFO is

   ---------------------------------------------------------------------------
   -- Constants
   ---------------------------------------------------------------------------

   constant MFB_REG_WIDTH     : integer := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

   constant SOF_POS_WIDTH     : integer := max(1,log2(MFB_REG_SIZE));
   constant EOF_POS_WIDTH     : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));

   constant MFB_FIFOXM_ITEM_WIDTH : integer := MFB_REG_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+1+1;

   ---------------------------------------------------------------------------

   ---------------------------------------------------------------------------
   -- Signals
   ---------------------------------------------------------------------------

   -- Extended RX MFB signals
   signal RX_MFB_DATA_ext    : std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
   signal RX_MFB_SOF_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal RX_MFB_EOF_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal RX_MFB_SOF_POS_ext : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
   signal RX_MFB_EOF_POS_ext : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
   signal RX_MFB_VLD_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal RX_MFB_SRC_RDY_ext : std_logic;
   signal RX_MFB_DST_RDY_ext : std_logic;

   -- Input MFB FIFOXM
   signal in_mfb_fifoxm_di    : std_logic_vector(MFB_REGIONS*MFB_FIFOXM_ITEM_WIDTH-1 downto 0);
   signal in_mfb_fifoxm_wr    : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal in_mfb_fifoxm_full  : std_logic; -- always '0'
   signal in_mfb_fifoxm_do    : std_logic_vector(MFB_REGIONS*MFB_FIFOXM_ITEM_WIDTH-1 downto 0);
   signal in_mfb_fifoxm_rd    : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal in_mfb_fifoxm_empty : std_logic_vector(MFB_REGIONS-1 downto 0);

   -- Number of MVB items to safely read from storage
   signal mvb_fifo_full       : std_logic;
   signal mvb_fifo_rd         : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal mvb_fifo_empty      : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal safe_mvb_items_reg  : unsigned(log2(MAIN_FIFO_ITEMS*MFB_REGIONS+1)-1 downto 0);
   signal mvb_items_vld_cnt   : unsigned(log2(MVB_ITEMS+1)-1 downto 0);

   -- Main MFB FIFO input
   signal main_mfb_fifo_in_data    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
   signal main_mfb_fifo_in_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal main_mfb_fifo_in_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal main_mfb_fifo_in_sof_act : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal main_mfb_fifo_in_eof_act : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal main_mfb_fifo_in_sof_pos : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
   signal main_mfb_fifo_in_eof_pos : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
   signal main_mfb_fifo_in_src_rdy : std_logic;
   signal main_mfb_fifo_in_dst_rdy : std_logic;

   ---------------------------------------------------------------------------

   signal rx_mfb_ext_err_reg       : std_logic; -- for simulation debug purposes
   signal mvb_main_fifo_err_reg    : std_logic; -- for simulation debug purposes

begin

   -- -------------------------------------------------------------------------
   -- RX MFB extention unit
   -- -------------------------------------------------------------------------

   rx_mfb_ext_i : entity work.MFB_AUXILIARY_SIGNALS
   generic map(
      REGIONS     => MFB_REGIONS   ,
      REGION_SIZE => MFB_REG_SIZE  ,
      BLOCK_SIZE  => MFB_BLOCK_SIZE,
      ITEM_WIDTH  => MFB_ITEM_WIDTH,

      REGION_AUX_EN => True        ,
      BLOCK_AUX_EN  => False       ,
      ITEM_AUX_EN   => False
   )
   port map(
      CLK   => CLK  ,
      RESET => RESET,

      RX_DATA       => RX_MFB_DATA       ,
      RX_SOF_POS    => RX_MFB_SOF_POS    ,
      RX_EOF_POS    => RX_MFB_EOF_POS    ,
      RX_SOF        => RX_MFB_SOF        ,
      RX_EOF        => RX_MFB_EOF        ,
      RX_SRC_RDY    => RX_MFB_SRC_RDY    ,
      RX_DST_RDY    => RX_MFB_DST_RDY    ,

      TX_DATA       => RX_MFB_DATA_ext   ,
      TX_SOF_POS    => RX_MFB_SOF_POS_ext,
      TX_EOF_POS    => RX_MFB_EOF_POS_ext,
      TX_SOF        => RX_MFB_SOF_ext    ,
      TX_EOF        => RX_MFB_EOF_ext    ,
      TX_REGION_VLD => RX_MFB_VLD_ext    ,
      TX_SRC_RDY    => RX_MFB_SRC_RDY_ext,
      TX_DST_RDY    => RX_MFB_DST_RDY_ext
   );

   RX_MFB_DST_RDY_ext <= not in_mfb_fifoxm_full;

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (in_mfb_fifoxm_full = '1') then
            rx_mfb_ext_err_reg <= '1';
         end if;
         if (RESET = '1') then
            rx_mfb_ext_err_reg <= '0';
         end if;
      end if;
   end process;

   assert (rx_mfb_ext_err_reg /= '1')
      report "PTC: Storage input shakedown FIFO dst_rdy fall error!"
      severity failure;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- Input MFB shakedown FIFOX Multi
   -- -------------------------------------------------------------------------

   input_mfb_fifoxm_input_gen : for i in 0 to MFB_REGIONS-1 generate
      in_mfb_fifoxm_di(MFB_FIFOXM_ITEM_WIDTH*(i+1)-1 downto MFB_FIFOXM_ITEM_WIDTH*i)
         <= RX_MFB_DATA_ext   (MFB_REG_WIDTH*(i+1)-1 downto MFB_REG_WIDTH*i)
          & RX_MFB_SOF_POS_ext(SOF_POS_WIDTH*(i+1)-1 downto SOF_POS_WIDTH*i)
          & RX_MFB_EOF_POS_ext(EOF_POS_WIDTH*(i+1)-1 downto EOF_POS_WIDTH*i)
          & RX_MFB_SOF_ext(i)
          & RX_MFB_EOF_ext(i);

       in_mfb_fifoxm_wr(i) <= RX_MFB_VLD_ext(i) and RX_MFB_SRC_RDY_ext;
   end generate;

   input_mfb_shake_fifoxm_i : entity work.FIFOX_MULTI
   generic map (
      DATA_WIDTH          => MFB_FIFOXM_ITEM_WIDTH,
      ITEMS               => MAIN_FIFO_ITEMS*MFB_REGIONS,

      WRITE_PORTS         => MFB_REGIONS,
      READ_PORTS          => MFB_REGIONS,
      RAM_TYPE            => "AUTO",
      DEVICE              => DEVICE,
      SAFE_READ_MODE      => false,
      ALMOST_FULL_OFFSET  => 0,
      ALMOST_EMPTY_OFFSET => 0
   )
   port map (
       CLK    => CLK  ,
       RESET  => RESET,

       DI     => in_mfb_fifoxm_di   ,
       WR     => in_mfb_fifoxm_wr   ,
       FULL   => in_mfb_fifoxm_full ,
       AFULL  => open               ,

       DO     => in_mfb_fifoxm_do   ,
       RD     => in_mfb_fifoxm_rd   ,
       EMPTY  => in_mfb_fifoxm_empty,
       AEMPTY => open
   );

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- MFB storing
   -- -------------------------------------------------------------------------

   mfb_store_gen : for i in 0 to MFB_REGIONS-1 generate
      main_mfb_fifo_in_data(MFB_REG_WIDTH*(i+1)-1 downto MFB_REG_WIDTH*i)
         <= in_mfb_fifoxm_do(MFB_FIFOXM_ITEM_WIDTH*(i+1)-1 downto MFB_FIFOXM_ITEM_WIDTH*(i+1)-MFB_REG_WIDTH);

      main_mfb_fifo_in_sof_pos(SOF_POS_WIDTH*(i+1)-1 downto SOF_POS_WIDTH*i)
         <= in_mfb_fifoxm_do(MFB_FIFOXM_ITEM_WIDTH*i+SOF_POS_WIDTH+EOF_POS_WIDTH+1+1-1 downto MFB_FIFOXM_ITEM_WIDTH*i+EOF_POS_WIDTH+1+1);

      main_mfb_fifo_in_eof_pos(EOF_POS_WIDTH*(i+1)-1 downto EOF_POS_WIDTH*i)
         <= in_mfb_fifoxm_do(MFB_FIFOXM_ITEM_WIDTH*i              +EOF_POS_WIDTH+1+1-1 downto MFB_FIFOXM_ITEM_WIDTH*i              +1+1);

      main_mfb_fifo_in_sof(i)
         <= in_mfb_fifoxm_do(MFB_FIFOXM_ITEM_WIDTH*i+1);

      main_mfb_fifo_in_eof(i)
         <= in_mfb_fifoxm_do(MFB_FIFOXM_ITEM_WIDTH*i);
   end generate;

   -- decide FIFOXM reading
   fifoxm_read_pr : process (all)
      variable last_sof     : integer;
      variable last_sof_vld : std_logic;
   begin
      -- default values
      in_mfb_fifoxm_rd <= (others => '0');

      last_sof     := 0;
      last_sof_vld := '1';

      -- find last valid SOF index
      for i in 0 to MFB_REGIONS-1 loop
         if (in_mfb_fifoxm_empty(i)='0') then
            if (main_mfb_fifo_in_sof(i)='1') then
               last_sof := i;
               last_sof_vld := '1';
            end if;
            if (main_mfb_fifo_in_eof(i)='1') then
               last_sof_vld := '0'; -- there is a EOF after the previous SOF
            end if;

            in_mfb_fifoxm_rd(i) <= main_mfb_fifo_in_dst_rdy; -- only read from valid regions
         end if;
      end loop;

       --((        word not full of data         ) and (the last packet was not ended)
      if ((in_mfb_fifoxm_empty(MFB_REGIONS-1)='1') and (     last_sof_vld='1'        )) then
         in_mfb_fifoxm_rd(MFB_REGIONS-1 downto last_sof) <= (others => '0'); -- don't read unfinished transaction
      end if;
   end process;

   main_mfb_fifo_in_src_rdy <= (or in_mfb_fifoxm_rd);

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- Safe MVB items register
   -- -------------------------------------------------------------------------

   -- Number of MVB items to safely read from storage
   safe_mvb_items_reg_pr : process (CLK)
      variable increment : unsigned(log2(MFB_REGIONS+1)-1 downto 0);
      variable decrement : unsigned(log2(MVB_ITEMS  +1)-1 downto 0);
   begin
      if (CLK'event and CLK='1') then
         -- add 1 for every transaction EOF read from main MFB FIFO
         increment := (others => '0');
         for i in 0 to MFB_REGIONS-1 loop
            if (TX_MFB_SRC_RDY='1' and TX_MFB_DST_RDY='1' and TX_MFB_EOF(i)='1') then
               increment := increment+1;
            end if;
         end loop;

         -- substract 1 for every MVB item read from main MVB FIFO
         decrement := (others => '0');
         if (TX_MVB_SRC_RDY='1' and TX_MVB_DST_RDY='1') then
            decrement := mvb_items_vld_cnt;
         end if;

         -- set new register value
         safe_mvb_items_reg <= safe_mvb_items_reg + resize(increment,safe_mvb_items_reg'length) - resize(decrement,safe_mvb_items_reg'length);

         if (RESET='1') then
            safe_mvb_items_reg <= (others => '0');
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- OUTPUT MFB REGISTER
   -- -------------------------------------------------------------------------

   -- mask SOF and EOF by FIFO read (valid)
   main_mfb_fifo_in_sof_act <= main_mfb_fifo_in_sof and in_mfb_fifoxm_rd;
   main_mfb_fifo_in_eof_act <= main_mfb_fifo_in_eof and in_mfb_fifoxm_rd;

   main_mfb_fifo_in_dst_rdy <= TX_MFB_DST_RDY;

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1') then
            TX_MFB_DATA    <= main_mfb_fifo_in_data;
            TX_MFB_SOF_POS <= main_mfb_fifo_in_sof_pos;
            TX_MFB_EOF_POS <= main_mfb_fifo_in_eof_pos;
            TX_MFB_SOF     <= main_mfb_fifo_in_sof_act;
            TX_MFB_EOF     <= main_mfb_fifo_in_eof_act;
            TX_MFB_SRC_RDY <= main_mfb_fifo_in_src_rdy;
         end if;
         if (RESET = '1') then
            TX_MFB_SRC_RDY <= '0';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- Main MVB FIFOX
   -- -------------------------------------------------------------------------

   RX_MVB_DST_RDY <= not mvb_fifo_full;

   mvb_main_fifo_i : entity work.FIFOX_MULTI
   generic map (
      DATA_WIDTH          => MVB_ITEM_WIDTH           ,
      ITEMS               => MVB_ITEMS*MAIN_FIFO_ITEMS,
      WRITE_PORTS         => MVB_ITEMS                ,
      READ_PORTS          => MVB_ITEMS                ,
      RAM_TYPE            => "AUTO"                   ,
      DEVICE              => DEVICE                   ,
      ALMOST_FULL_OFFSET  => 1                        ,
      ALMOST_EMPTY_OFFSET => 1                        ,
      SAFE_READ_MODE      => true
   )
   port map (
      CLK         => CLK  ,
      RESET       => RESET,

      DI          => RX_MVB_DATA   ,
      WR          => RX_MVB_SRC_RDY and RX_MVB_VLD,
      FULL        => mvb_fifo_full ,
      AFULL       => open,

      DO          => TX_MVB_DATA   ,
      RD          => mvb_fifo_rd   ,
      EMPTY       => mvb_fifo_empty,
      AEMPTY      => open
   );

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RX_MVB_DST_RDY = '0') then
            mvb_main_fifo_err_reg <= '1';
         end if;
         if (RESET = '1') then
            mvb_main_fifo_err_reg <= '0';
         end if;
      end if;
   end process;

   assert (mvb_main_fifo_err_reg /= '1')
      report "PTC: Storage main MVB FIFO dst_rdy fall error!"
      severity failure;

   -- safe MVB items checking
   safe_mvb_items_check_pr : process (safe_mvb_items_reg,TX_MVB_DST_RDY,mvb_fifo_empty)
      variable items : unsigned(log2(MVB_ITEMS+1)-1 downto 0);
   begin
      -- read from FIFO, send TX MVB, count number of sent items
      mvb_fifo_rd <= (others => '0');
      TX_MVB_VLD  <= (others => '0');
      items := (others => '0');
      for i in 0 to MVB_ITEMS-1 loop
         if (i<safe_mvb_items_reg) then
            mvb_fifo_rd(i) <= TX_MVB_DST_RDY;
            TX_MVB_VLD (i) <= not mvb_fifo_empty(i);
            items := items+1;
         end if;
      end loop;

      mvb_items_vld_cnt <= items;
   end process;

   TX_MVB_SRC_RDY <= (or TX_MVB_VLD);

   -- -------------------------------------------------------------------------

end architecture;
