-- pd_asfifo_full.vhd: Asynchronous packet buffer
--
--
-- Copyright (C) 2018 CESNET z. s. p. o.
-- SPDX-License-Identifier: BSD-3-Clause
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of MFB_PD_ASFIFO is

   -- ----------------------------------------------------------------------------
   -- Constants
   -- ----------------------------------------------------------------------------

   constant SOF_POS_WIDTH      : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH      : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant SOF_POS_TRUE_WIDTH : natural := log2(REGION_SIZE);
   constant EOF_POS_TRUE_WIDTH : natural := log2(REGION_SIZE*BLOCK_SIZE);
   constant SOF_POS_WW         : natural := REGIONS*SOF_POS_WIDTH;
   constant EOF_POS_WW         : natural := REGIONS*EOF_POS_WIDTH;

   constant INTERNAL_FIFO_WIDTH : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH
                                            +REGIONS*SOF_POS_WIDTH
                                            +REGIONS*EOF_POS_WIDTH
                                            +REGIONS
                                            +REGIONS;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- Signals
   -- ----------------------------------------------------------------------------

   signal rx_src_rdy_true    : std_logic;

   signal rx_sof_pos_arr     : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
   signal rx_eof_pos_arr     : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal rx_eof_pos_top_arr : slv_array_t(REGIONS-1 downto 0)(SOF_POS_TRUE_WIDTH-1 downto 0);

   signal rx_pos_cmp : std_logic_vector(REGIONS-1 downto 0); -- '1' for region where EOF_POS<SOF_POS
   signal tx_pos_cmp : std_logic_vector(REGIONS-1 downto 0); -- '1' for region where EOF_POS<SOF_POS

   -- RX SOF and EOF masking
   signal rx_open_sof     : std_logic;
   signal rx_sof_masked : std_logic_vector(REGIONS-1 downto 0);
   signal rx_eof_masked : std_logic_vector(REGIONS-1 downto 0);

   -- Discard logic
   signal discard             : std_logic;
   signal delayed_mark        : std_logic;
   signal delayed_mark_reg    : std_logic;
   signal shared_inserted_reg : std_logic;

   -- mark asfifo signals
   signal masfifo_wr      : std_logic;
   signal masfifo_di      : std_logic_vector(INTERNAL_FIFO_WIDTH-1 downto 0);
   signal masfifo_full    : std_logic;
   signal masfifo_mark    : std_logic;
   signal masfifo_discard : std_logic;
   signal masfifo_rd      : std_logic;
   signal masfifo_do      : std_logic_vector(INTERNAL_FIFO_WIDTH-1 downto 0);
   signal masfifo_empty   : std_logic;
   signal masfifo_nxempty : std_logic;

   -- Shared continue word masking FIFO
   signal masking_asfifo_di    : std_logic_vector(1-1 downto 0);
   signal masking_asfifo_wr    : std_logic;
   signal masking_asfifo_do    : std_logic_vector(1-1 downto 0);
   signal masking_asfifo_rd    : std_logic;
   signal masking_asfifo_full  : std_logic;
   signal masking_asfifo_empty : std_logic;

   -- TX SOF and EOF masking
   signal tx_mask_sof     : std_logic;
   signal tx_open_sof     : std_logic;
   signal tx_demand_mask  : std_logic;
   signal tx_sof_unmasked : std_logic_vector(REGIONS-1 downto 0);
   signal tx_eof_unmasked : std_logic_vector(REGIONS-1 downto 0);

   signal need_cut_word    : std_logic;
   signal cutted_word_reg  : std_logic;
   signal cutted_word_rdy  : std_logic;
   signal tx_rm_last_sof   : std_logic;
   signal tx_only_last_sof : std_logic;

   signal tx_sof_masked : std_logic_vector(REGIONS-1 downto 0);
   signal tx_eof_masked : std_logic_vector(REGIONS-1 downto 0);

   signal fifos_rd   : std_logic;
   signal tx_rm_word : std_logic;
   signal tx_valid   : std_logic;

   -- ----------------------------------------------------------------------------

begin

   rx_arr_gen : for i in 0 to REGIONS-1 generate
      rx_sof_pos_arr(i)     <= RX_SOF_POS(SOF_POS_WIDTH*(i+1)-1 downto SOF_POS_WIDTH*i);
      rx_eof_pos_arr(i)     <= RX_EOF_POS(EOF_POS_WIDTH*(i+1)-1 downto EOF_POS_WIDTH*i);

      rx_eof_pos_top_arr(i) <= rx_eof_pos_arr(i)(EOF_POS_WIDTH-1 downto EOF_POS_WIDTH-SOF_POS_TRUE_WIDTH);

      rx_pos_cmp(i)         <= '1' when unsigned(rx_eof_pos_top_arr(i))<unsigned(rx_sof_pos_arr(i)(SOF_POS_TRUE_WIDTH-1 downto 0)) else '0';

      tx_pos_cmp(i)         <= '1' when unsigned(TX_EOF_POS((i+1)*EOF_POS_WIDTH-1 downto (i+1)*EOF_POS_WIDTH-SOF_POS_TRUE_WIDTH))<unsigned(TX_SOF_POS(i*SOF_POS_WIDTH+SOF_POS_TRUE_WIDTH-1 downto i*SOF_POS_WIDTH)) else '0';
   end generate;

   -- ----------------------------------------------------------------------------
   -- RX SRC RDY and DST RDY medling
   -- ----------------------------------------------------------------------------

   rx_src_rdy_true <= RX_SRC_RDY and (not RX_FORCE_DISCARD);

   RX_DST_RDY <= '1' when masfifo_full='0' and masking_asfifo_full='0' else '0';

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- RX SOF and EOF masking
   -- ----------------------------------------------------------------------------

   -- this process deletes the EOFs of all discarded packets and the SOFs of discarded packets which are inside one RX word
   rx_sof_eof_masked_pr : process (all)
      variable flag : std_logic;
   begin
      rx_sof_masked <= RX_SOF;
      rx_eof_masked <= RX_EOF;

      flag := '0';

      for i in REGIONS-1 downto 0 loop -- a DOWNTO loop!
         if (flag='0') then -- look for EOF
            if (RX_EOF(i)='1' and RX_DISCARD(i)='1') then -- new packet for discard
               rx_eof_masked(i) <= '0';

               if (RX_SOF(i)='1' and rx_pos_cmp(i)='0') then -- packet inside one region
                  rx_sof_masked(i) <= '0';
               else -- packet starts in some previous region
                  flag := '1';
               end if;
            end if;
         else -- expect SOF of discarded packet
            if (RX_SOF(i)='1') then -- expected start of discarded packet
               rx_sof_masked(i) <= '0';
               flag := '0';
            end if;

            if (RX_EOF(i)='1' and RX_DISCARD(i)='1') then -- region shared by two discarded packets
               rx_eof_masked(i) <= '0';
               flag := '1';
            end if;
         end if;
      end loop;
   end process;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- Discard logic
   -- ----------------------------------------------------------------------------

   -- discard=='1' indicates that the first EOF in valid RX word has DISCARD
   discard_pr : process (all)
   begin
      discard <= RX_FORCE_DISCARD;

      if (rx_src_rdy_true='1' and masfifo_full='0') then
         -- set discard
         for i in 0 to REGIONS-1 loop
            if (RX_EOF(i)='1' and RX_DISCARD(i)='1') then
               discard <= '1';
            end if;
            exit when (RX_EOF(i)='1');
         end loop;
      end if;
   end process;

   delayed_mark <= (or rx_eof_masked); -- insert mark after every EOF

   -- delay the mark insertion by one CLK (only when SRC_RDY and DST_RDY)
   delayed_mark_reg_pr : process (RX_CLK)
   begin
      if (RX_CLK'event and RX_CLK='1') then
         if (rx_src_rdy_true='1' and RX_DST_RDY='1') then
            if (delayed_mark_reg='1') then
               delayed_mark_reg <= '0';
            end if;

            if (delayed_mark='1') then
               delayed_mark_reg <= '1';
            end if;
         end if;

         if (RX_RESET='1') then
            delayed_mark_reg <= '0';
         end if;
      end if;
   end process;

   masfifo_mark    <= delayed_mark_reg; -- insert mark request
   masfifo_discard <= discard and (not masfifo_mark); -- discard request (go back to last mark in data ASFIFO)

   -- rx_open_sof=='1' indicated that the RX word contains a SOF with no EOF after it
   rx_open_sof_det_pr : process (all)
   begin
      rx_open_sof <= '0';

      -- detect open SOF
      for i in REGIONS-1 downto 0 loop
         if (rx_sof_masked(i)='1' and (rx_eof_masked(i)='0' or rx_pos_cmp(i)='1')) then
            rx_open_sof <= '1';
         end if;
         exit when (rx_sof_masked(i)='1' or rx_eof_masked(i)='1');
      end loop;
   end process;

   -- shared_inserted_reg='1' indicates that ian item will have to be inserted in the masking ASFIFO with the next EOF
   shared_inserted_reg_pr : process (RX_CLK)
   begin
      if (RX_CLK'event and RX_CLK='1') then
         if (rx_src_rdy_true='1' and RX_DST_RDY='1') then
            -- unset
            if ((or RX_EOF)='1') then
               shared_inserted_reg <= '0';
            end if;

            -- set
            if (rx_open_sof='1' and (or rx_eof_masked)='1') then
               shared_inserted_reg <= '1';
            end if;
         end if;

         -- force unset
         if (RX_FORCE_DISCARD='1') then
            shared_inserted_reg <= '0';
         end if;

         if (RX_RESET='1') then
            shared_inserted_reg <= '0';
         end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- Main ASFIFO
   -- ----------------------------------------------------------------------------

   mark_asfifo_i : entity work.MARK_ASFIFO
   generic map(
      ITEMS              => ITEMS,
      DATA_WIDTH         => INTERNAL_FIFO_WIDTH,
      WR_PTR_ADD_LATENCY => WR_PTR_ADD_LATENCY
   )
   port map(
      CLK_WR     => RX_CLK  ,
      RESET_WR   => RX_RESET,

      WR         => masfifo_wr  ,
      DI         => masfifo_di  ,
      FULL       => masfifo_full,
      STATUS     => STATUS      ,

      MARK       => masfifo_mark   ,
      DISCARD    => masfifo_discard,

      CLK_RD     => TX_CLK  ,
      RESET_RD   => TX_RESET,

      RD         => masfifo_rd   ,
      DO         => masfifo_do   ,
      EMPTY      => masfifo_empty,
      NEXT_EMPTY => masfifo_nxempty
   );

   masfifo_wr <= '1' when rx_src_rdy_true='1'        -- data ready
                      and masking_asfifo_full='0'    -- some space in masking fifo
                      and (   discard='0'            -- not inserting word with masked EOF
                           or (or rx_sof_masked)='1' -- inserting word with valid SOF
                          )
                     else '0';

   -- data serialization
   masfifo_di <= RX_DATA & RX_SOF_POS & RX_EOF_POS & rx_sof_masked & rx_eof_masked;

   -- data deserialization
   tx_eof_unmasked <= masfifo_do(REGIONS-1 downto 0);
   tx_sof_unmasked <= masfifo_do(2*REGIONS-1 downto REGIONS);
   TX_EOF_POS      <= masfifo_do(2*REGIONS+EOF_POS_WW-1 downto 2*REGIONS);
   TX_SOF_POS      <= masfifo_do(2*REGIONS+EOF_POS_WW+SOF_POS_WW-1 downto 2*REGIONS+EOF_POS_WW);
   TX_DATA         <= masfifo_do(INTERNAL_FIFO_WIDTH-1 downto 2*REGIONS+EOF_POS_WW+SOF_POS_WW);

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- Shared continue word masking ASFIFO
   -- ----------------------------------------------------------------------------
   -- To this FIFO an item is inserted for each shared MFB word, which contains a SOF with no EOF after it
   -- The items value determines, whether the last SOF should be masked out when reading the word ('1' for masking)

   masking_asfifo_i : entity work.ASFIFOX
   generic map(
      DATA_WIDTH => 1,
      ITEMS      => ITEMS,
      RAM_TYPE   => "BRAM",
      FWFT_MODE  => True,
      OUTPUT_REG => True,
      DEVICE     => DEVICE
   )
   port map(
      WR_CLK    => RX_CLK,
      WR_RST    => RX_RESET,
      WR_DATA   => masking_asfifo_di,
      WR_EN     => masking_asfifo_wr,
      WR_FULL   => masking_asfifo_full,
      WR_AFULL  => open,
      WR_STATUS => open,

      RD_CLK    => TX_CLK,
      RD_RST    => TX_RESET,
      RD_DATA   => masking_asfifo_do,
      RD_EN     => masking_asfifo_rd,
      RD_EMPTY  => masking_asfifo_empty,
      RD_AEMPTY => open,
      RD_STATUS => open
   );

   -- masking will be done if the multiple-word packet is meant to be discarded
   masking_asfifo_di(0) <= discard;

   tx_mask_sof <= masking_asfifo_do(0);

   masking_asfifo_wr <= '1' when shared_inserted_reg='1'       -- masking information will be required on TX
                             and (    (    rx_src_rdy_true='1' -- RX data is valid
                                       and masfifo_full='0'    -- RX data is being accepted
                                       and (or RX_EOF)='1'     -- there is an EOF
                                      )
                                  or  RX_FORCE_DISCARD='1'     -- force discarding
                                 )
                            else '0';

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- TX continue detection
   -- ----------------------------------------------------------------------------

   -- tx_open_sof=='1' indicates that the TX word contains a SOF with no EOF after it
   tx_demand_mask_det_pr : process (tx_sof_unmasked,tx_eof_unmasked,tx_pos_cmp)
   begin
      tx_open_sof <= '0';
      -- detect open SOF
      for i in REGIONS-1 downto 0 loop
         if (tx_sof_unmasked(i)='1' and (tx_eof_unmasked(i)='0' or tx_pos_cmp(i)='1')) then
            tx_open_sof <= '1';
         end if;
         exit when (tx_sof_unmasked(i)='1' or tx_eof_unmasked(i)='1');
      end loop;
   end process;

   -- masking information is required for shared word with open SOF
   tx_demand_mask <= tx_open_sof and (or tx_eof_unmasked);
   -- is need cut word due to shared word with open SOF
   -- masking_asfifo_empty == 1 -> We have SOF, but we don't know whether to remove it or not yet.
   --                              Stop until the information arrives.
   --      masfifo_nxempty == 1 -> We have SOF, but it belongs to packet which has not been confirmed as whole by the Mark ASFIFO.
   --                              Stop until the FIFO confirms it to avoid potential word gaps inside frame.
   need_cut_word <= tx_demand_mask and (masking_asfifo_empty or masfifo_nxempty);
   -- second part of cutted word is ready to transmit
   cutted_word_rdy <= cutted_word_reg and not masking_asfifo_empty and not masfifo_nxempty;

   cutted_word_reg_p : process (TX_CLK)
   begin
      if (TX_CLK'event and TX_CLK='1') then
         if (masfifo_empty='0' and TX_DST_RDY='1') then
            if (need_cut_word='1') then
               cutted_word_reg <= '1';
            end if;

            if (cutted_word_rdy='1') then
               cutted_word_reg <= '0';
            end if;
         end if;

         if (TX_RESET='1') then
            cutted_word_reg <= '0';
         end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------

   tx_rm_last_sof <= need_cut_word or (tx_demand_mask and tx_mask_sof);
   tx_only_last_sof <= cutted_word_rdy and tx_demand_mask and not tx_mask_sof;

   tx_sof_eof_masked_p : process (tx_sof_unmasked, tx_eof_unmasked, tx_only_last_sof, tx_rm_last_sof)
   begin
      tx_sof_masked <= tx_sof_unmasked;
      tx_eof_masked <= tx_eof_unmasked;

      if (tx_only_last_sof = '1') then
         tx_sof_masked <= (others => '0');
         tx_eof_masked <= (others => '0');
      end if;

      for i in REGIONS-1 downto 0 loop
         if (tx_sof_unmasked(i) = '1') then
            if (tx_rm_last_sof = '1') then
               tx_sof_masked(i) <= '0';
            else
               tx_sof_masked(i) <= tx_sof_unmasked(i);
            end if;
            exit;
         end if;
      end loop;
   end process;

   tx_rm_word <= cutted_word_rdy and tx_demand_mask and tx_mask_sof;
   tx_valid <= not masfifo_empty and not tx_rm_word and (not cutted_word_reg or cutted_word_rdy);
   fifos_rd <= TX_DST_RDY and not need_cut_word and (not cutted_word_reg or cutted_word_rdy);

   masfifo_rd <= fifos_rd;
   masking_asfifo_rd <= fifos_rd and tx_demand_mask and not masfifo_empty;

   TX_SOF <= tx_sof_masked;
   TX_EOF <= tx_eof_masked;
   TX_SRC_RDY <= tx_valid;

end architecture;
