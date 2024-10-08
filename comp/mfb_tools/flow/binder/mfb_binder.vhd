-- mfb_binder.vhd: Binder for multi MFB merging (top level)
-- Copyright (C) 2018 CESNET
-- Author(s): Michal Suchanek <xsucha12@stud.feec.vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- MFB Binder is able merge N input MFB(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)
-- streams to one output MFB(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) stream.

entity MFB_BINDER is
   generic(
      -- Number of inputs MFB streams.
      INPUTS            : integer := 4;
      -- Number of regions of output MFB bus, for input buses is REGIONS = 1.
      REGIONS           : integer := 4;
      -- MFB parameters common for input and output buses.
      REGION_SIZE       : integer := 8;
      BLOCK_SIZE        : integer := 8;
      ITEM_WIDTH        : integer := 8;
      META_WIDTH        : integer := 8;
      -- Others parameters
      FIFO_RAM_TYPE     : string  := "BRAM";
      FIFO_DEPTH        : integer := 512;
      FIFO_AFULL_OFFSET : integer := 1;
      DEVICE            : string  := "ULTRASCALE"
   );
   port(
      -- CLOCK AND RESET
      CLK           : in  std_logic;
      RST           : in  std_logic;
      -- RX MULTI MFB INTERFACE
      -- INPUTS*MFB(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)
      RX_DATA       : in  std_logic_vector(INPUTS*1*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META       : in  std_logic_vector(INPUTS*1*META_WIDTH-1 downto 0);
      RX_SOF_POS    : in  std_logic_vector(INPUTS*1*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS    : in  std_logic_vector(INPUTS*1*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF        : in  std_logic_vector(INPUTS*1-1 downto 0);
      RX_EOF        : in  std_logic_vector(INPUTS*1-1 downto 0);
      RX_SRC_RDY    : in  std_logic_vector(INPUTS*1-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUTS*1-1 downto 0);
      RX_FIFO_AFULL : out std_logic_vector(INPUTS*1-1 downto 0);
      -- TX MFB INTERFACE
      -- MFB(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)
      TX_DATA       : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META       : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF        : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF        : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in  std_logic
   );
end MFB_BINDER;

architecture behavioral of MFB_BINDER is

   constant RX_REGION_WIDTH  : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant RX_SOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE));
   constant RX_EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant WORD_CNT_MAX     : natural := FIFO_DEPTH;
   constant WORD_CNT_WIDTH   : natural := log2(WORD_CNT_MAX);

   -- RX signals
   signal s_rx_data_arr              : slv_array_t(INPUTS-1 downto 0)(RX_REGION_WIDTH-1 downto 0);
   signal s_rx_meta_arr              : slv_array_t(INPUTS-1 downto 0)(META_WIDTH-1 downto 0);
   signal s_rx_sof_pos_arr           : slv_array_t(INPUTS-1 downto 0)(RX_SOF_POS_WIDTH-1 downto 0);
   signal s_rx_eof_pos_arr           : slv_array_t(INPUTS-1 downto 0)(RX_EOF_POS_WIDTH-1 downto 0);

   -- FIFO
   signal s_fifo_data_arr            : slv_array_t(INPUTS-1 downto 0)(REGIONS*RX_REGION_WIDTH-1 downto 0);
   signal s_fifo_meta_arr            : slv_array_t(INPUTS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
   signal s_fifo_sof_pos_arr         : slv_array_t(INPUTS-1 downto 0)(REGIONS*RX_SOF_POS_WIDTH-1 downto 0);
   signal s_fifo_eof_pos_arr         : slv_array_t(INPUTS-1 downto 0)(REGIONS*RX_EOF_POS_WIDTH-1 downto 0);
   signal s_fifo_sof_arr             : slv_array_t(INPUTS-1 downto 0)(REGIONS-1 downto 0);
   signal s_fifo_eof_arr             : slv_array_t(INPUTS-1 downto 0)(REGIONS-1 downto 0);
   signal s_fifo_src_rdy             : std_logic_vector(INPUTS-1 downto 0);
   signal s_fifo_dst_rdy_demuxed     : std_logic_vector(INPUTS-1 downto 0);
   signal s_fifo_ongoing_frame       : std_logic_vector(INPUTS-1 downto 0);
   signal s_fifo_unfinished_frame    : std_logic_vector(INPUTS-1 downto 0);

   -- MFB COUNTER
   signal s_mfb_select               : unsigned(log2(INPUTS)-1 downto 0);
   signal s_mfb_select_next          : std_logic;

   -- WORD COUNTER
   signal s_word_cnt                 : unsigned(WORD_CNT_WIDTH-1 downto 0);
   signal s_word_cnt_en              : std_logic;
   signal s_word_cnt_max             : std_logic;

   signal s_fifo_dst_rdy             : std_logic;
   signal s_fifo_eof_vld             : std_logic_vector(INPUTS-1 downto 0);

   -- SOF AND EOF MASKING
   signal s_mask_enable              : std_logic;
   signal s_sof_masked_arr           : slv_array_t(INPUTS-1 downto 0)(REGIONS-1 downto 0);
   signal s_eof_masked_arr           : slv_array_t(INPUTS-1 downto 0)(REGIONS-1 downto 0);
   signal s_need_mask_first_word     : std_logic_vector(INPUTS-1 downto 0);
   signal s_need_mask_last_word      : std_logic_vector(INPUTS-1 downto 0);

   signal s_fifo_eof_vld_muxed       : std_logic;
   signal s_need_mask_fword_muxed    : std_logic;
   signal s_need_mask_lword_muxed    : std_logic;
   signal s_fifo_ongoing_frame_muxed : std_logic;
   signal s_mask_enable_demuxed      : std_logic_vector(INPUTS-1 downto 0);

   signal s_tx_data                  : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   signal s_tx_meta                  : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
   signal s_tx_sof_pos               : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   signal s_tx_eof_pos               : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   signal s_tx_sof                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_tx_eof                   : std_logic_vector(REGIONS-1 downto 0);
   signal s_tx_src_rdy               : std_logic;

   type state_type is (check, reading);
   signal s_present_state            : state_type;
   signal s_next_state               : state_type;

begin

   s_rx_data_arr    <= slv_array_downto_deser(RX_DATA,INPUTS,RX_REGION_WIDTH);
   s_rx_meta_arr    <= slv_array_downto_deser(RX_META,INPUTS,META_WIDTH);
   s_rx_sof_pos_arr <= slv_array_downto_deser(RX_SOF_POS,INPUTS,RX_SOF_POS_WIDTH);
   s_rx_eof_pos_arr <= slv_array_downto_deser(RX_EOF_POS,INPUTS,RX_EOF_POS_WIDTH);

   -- Input component mapping
   mfb_binder_input_g : for i in 0 to INPUTS-1 generate
      mfb_binder_input_i : entity work.MFB_BINDER_INPUT
      generic map(
         REGIONS           => REGIONS,
         REGION_SIZE       => REGION_SIZE,
         BLOCK_SIZE        => BLOCK_SIZE,
         ITEM_WIDTH        => ITEM_WIDTH,
         META_WIDTH        => META_WIDTH,
         FIFO_RAM_TYPE     => FIFO_RAM_TYPE,
         FIFO_DEPTH        => FIFO_DEPTH,
         FIFO_AFULL_OFFSET => FIFO_AFULL_OFFSET,
         DEVICE            => DEVICE
      )
      port map(
         -- CLOCK AND RESET
         CLK                 => CLK,
         RST                 => RST,
         -- RX MULTI MFB INTERFACE
         RX_DATA             => s_rx_data_arr(i),
         RX_META             => s_rx_meta_arr(i),
         RX_SOF_POS          => s_rx_sof_pos_arr(i),
         RX_EOF_POS          => s_rx_eof_pos_arr(i),
         RX_SOF              => RX_SOF(i),
         RX_EOF              => RX_EOF(i),
         RX_SRC_RDY          => RX_SRC_RDY(i),
         RX_DST_RDY          => RX_DST_RDY(i),
         RX_FIFO_AFULL       => RX_FIFO_AFULL(i),
         -- TX MFB INTERFACE
         TX_DATA             => s_fifo_data_arr(i),
         TX_META             => s_fifo_meta_arr(i),
         TX_SOF_POS          => s_fifo_sof_pos_arr(i),
         TX_EOF_POS          => s_fifo_eof_pos_arr(i),
         TX_SOF              => s_fifo_sof_arr(i),
         TX_EOF              => s_fifo_eof_arr(i),
         TX_SRC_RDY          => s_fifo_src_rdy(i),
         TX_DST_RDY          => s_fifo_dst_rdy_demuxed(i),
         -- FRAME STATE
         -- In this word continues the previously unfinished frame.
         TX_ONGOING_FRAME    => s_fifo_ongoing_frame(i),
         -- Last frame in this word is unfinished.
         TX_UNFINISHED_FRAME => s_fifo_unfinished_frame(i)
      );

      s_fifo_eof_vld(i) <= (or s_fifo_eof_arr(i)) and s_fifo_src_rdy(i);
   end generate;

   -- --------------------------------------------------------------------------
   -- EOF SOF MASKING
   -- --------------------------------------------------------------------------
   -- Used in forced MFB input switch. Masked signal is sent to output with s_mask_enable.
   -- Masking first SOF from top (REGIONS-1 donwto 0) if it's part of incomplete frame.
   -- If masking was done before on given input, the rest (SOF, EOF) is masked, except for previously masked SOF.

   mfb_binder_mask_g : for i in 0 to INPUTS-1 generate
      mfb_binder_mask_i : entity work.MFB_BINDER_MASK
      generic map(
         REGIONS => REGIONS
      )
      port map(
         -- CLOCK AND RESET
         CLK                 => CLK,
         RST                 => RST,
         -- INPUT
         IN_MASK_ENABLE      => s_mask_enable_demuxed(i),
         IN_UNFINISHED_FRAME => s_fifo_unfinished_frame(i),
         IN_SOF              => s_fifo_sof_arr(i),
         IN_EOF              => s_fifo_eof_arr(i),
         -- OUTPUT
         OUT_NEED_MASK_FWORD => s_need_mask_first_word(i),
         OUT_NEED_MASK_LWORD => s_need_mask_last_word(i),
         OUT_SOF_MASKED      => s_sof_masked_arr(i),
         OUT_EOF_MASKED      => s_eof_masked_arr(i)
      );
   end generate;

   -- --------------------------------------------------------------------------
   -- MFB COUNTER
   -- --------------------------------------------------------------------------
   -- switches between MFB inputs.

   process(CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1') then
            s_mfb_select <= (others => '0');
         elsif (s_mfb_select_next = '1') then
            s_mfb_select <= s_mfb_select + 1;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   -- WORD COUNTER
   -- --------------------------------------------------------------------------
   -- After reaching defined counter_max -> forced EOF and SOF masking,
   -- and switching to the next MFB input.

   process(CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1') then
            s_word_cnt <= (others => '0');
         elsif (s_word_cnt_en = '1') then
            if (TX_DST_RDY = '1' and s_word_cnt_max = '0') then
               s_word_cnt <= s_word_cnt + 1;
            end if;
         else
            s_word_cnt <= (others => '0');
         end if;
      end if;
   end process;

   s_word_cnt_max <= '1' when (s_word_cnt >= WORD_CNT_MAX-1) else '0';

   -- --------------------------------------------------------------------------
   -- (DE)MULTIPLEXORS OF CONTROL SIGNALS
   -- --------------------------------------------------------------------------

   s_fifo_eof_vld_muxed       <= s_fifo_eof_vld(to_integer(s_mfb_select));
   s_need_mask_fword_muxed    <= s_need_mask_first_word(to_integer(s_mfb_select));
   s_need_mask_lword_muxed    <= s_need_mask_last_word(to_integer(s_mfb_select));
   s_fifo_ongoing_frame_muxed <= s_fifo_ongoing_frame(to_integer(s_mfb_select));

   demultiplexor_g : for i in 0 to INPUTS-1 generate
      s_mask_enable_demuxed(i)  <= s_mask_enable when (i = to_integer(s_mfb_select)) else '0';
      s_fifo_dst_rdy_demuxed(i) <= s_fifo_dst_rdy when (i = to_integer(s_mfb_select)) else '0';
   end generate;

   -- --------------------------------------------------------------------------
   -- FSM
   -- --------------------------------------------------------------------------

   process(CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1') then
            s_present_state <= check;
         else
            s_present_state <= s_next_state;
         end if;
      end if;
   end process;

   process(all)
   begin
      case s_present_state is
         when check =>
            s_next_state      <= check;
            s_mfb_select_next <= '1';
            s_word_cnt_en     <= '0';
            s_fifo_dst_rdy    <= '0';
            s_mask_enable     <= '0';

            if (s_tx_src_rdy = '1') then
               s_next_state      <= reading;
               s_mfb_select_next <= '0';
               s_fifo_dst_rdy    <= TX_DST_RDY;
               s_mask_enable     <= s_need_mask_fword_muxed and TX_DST_RDY;
            end if;

         when reading =>
            s_next_state      <= reading;
            s_mfb_select_next <= '0';
            s_word_cnt_en     <= '1';
            s_fifo_dst_rdy    <= TX_DST_RDY;
            s_mask_enable     <= s_need_mask_fword_muxed and TX_DST_RDY;

            if (s_word_cnt_max = '1') then
               if (s_fifo_eof_vld_muxed = '1' AND TX_DST_RDY = '1') then
                  s_next_state      <= check;
                  s_mfb_select_next <= '1';
                  s_mask_enable     <= '1';
                  s_fifo_dst_rdy    <= not s_need_mask_lword_muxed;
               end if;
            end if;

            if (s_tx_src_rdy = '0' AND s_fifo_ongoing_frame_muxed = '0') then
               s_next_state      <= check;
               s_mfb_select_next <= '1';
               s_mask_enable     <= '0';
            end if;

         when others =>
            s_next_state      <= check;
            s_mfb_select_next <= '1';
            s_word_cnt_en     <= '0';
            s_fifo_dst_rdy    <= '0';
            s_mask_enable     <= '0';
      end case;
   end process;

   -- --------------------------------------------------------------------------
   -- OUTPUT MULTIPLEXORS
   -- --------------------------------------------------------------------------

   s_tx_data    <= s_fifo_data_arr(to_integer(s_mfb_select));
   s_tx_meta    <= s_fifo_meta_arr(to_integer(s_mfb_select));
   s_tx_sof_pos <= s_fifo_sof_pos_arr(to_integer(s_mfb_select));
   s_tx_eof_pos <= s_fifo_eof_pos_arr(to_integer(s_mfb_select));
   s_tx_sof     <= s_sof_masked_arr(to_integer(s_mfb_select));
   s_tx_eof     <= s_eof_masked_arr(to_integer(s_mfb_select));
   s_tx_src_rdy <= s_fifo_src_rdy(to_integer(s_mfb_select));

   -- --------------------------------------------------------------------------
   -- OUTPUT REGISTERS
   -- --------------------------------------------------------------------------

   process (CLK)
   begin
      if rising_edge(CLK) then
         if (TX_DST_RDY = '1') then
            TX_DATA    <= s_tx_data;
            TX_META    <= s_tx_meta;
            TX_SOF_POS <= s_tx_sof_pos;
            TX_EOF_POS <= s_tx_eof_pos;
            TX_SOF     <= s_tx_sof;
            TX_EOF     <= s_tx_eof;
         end if;
      end if;
   end process;

   process (CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1') then
            TX_SRC_RDY <= '0';
         elsif (TX_DST_RDY = '1') then
            TX_SRC_RDY <= s_tx_src_rdy;
         end if;
      end if;
   end process;

end architecture;
