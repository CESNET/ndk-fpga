-- trimming_unit_flu.vhd: Trimming unit for FLU architecture
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id: trimming_unit.vhd 14575 2010-07-21 14:21:17Z dedekt1 $
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Architecture: TRIMMING_UNIT_FLU
-- ----------------------------------------------------------------------------
architecture TRIMMING_UNIT_ARCH of TRIMMING_UNIT_FLU is
   -- number of REM bits
   constant EOP_POS_WIDTH      : integer := log2(DATA_WIDTH/8);
   constant BLOCKS             : integer := 2**SOP_POS_WIDTH;
   constant BLOCK_SIZE         : integer := DATA_WIDTH/BLOCKS;
   type block_array_t is array (integer range <>) of std_logic_vector(BLOCK_SIZE-1 downto 0);

   signal length_zeros         : std_logic;
   signal length_ones          : std_logic;
   signal length_zeros_reg     : std_logic;
   signal length_ones_reg      : std_logic;
   signal length_actual        : std_logic_vector(LENGTH_WIDTH downto 0);

   signal header_detect        : std_logic;
   signal rx_valid             : std_logic;
   signal block_flu            : std_logic;
   signal discard_sop          : std_logic;
   signal discard_eop          : std_logic;
   signal discard_word         : std_logic;
   signal sop_pos_aug          : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal sop_after_eop        : std_logic;
   signal in_packet_tx         : std_logic;

   signal sig_rx_dst_rdy       : std_logic;
   signal sig_tx_sop_pos       : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal sig_tx_sop_pos_aug   : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal sig_tx_src_rdy       : std_logic;

   signal shift                : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal shift_reg            : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal shift_reg_aug        : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal odd_shift            : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal even_shift           : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal shift_need           : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal eop_shift_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal eop_shift_data_array : block_array_t(0 to BLOCKS-1);
   signal sop_shift_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sop_shift_data_array : block_array_t(0 to BLOCKS-1);
   signal odd_shift_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal even_shift_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_mx              : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_mx_array        : block_array_t(0 to BLOCKS-1);
   signal sop_pos_cmp          : std_logic_vector(BLOCKS-1 downto 0);
   signal data_mx_array_sel    : std_logic_vector(BLOCKS-1 downto 0);
   signal odd_packet           : std_logic;

   signal expect_eop_pos       : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal expect_eop_pos_reg   : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal expect_eop_pos_mx    : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal eop_pos_mx           : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal expect_end           : std_logic_vector(LENGTH_WIDTH downto 0);
   signal expect_words         : std_logic_vector(LENGTH_WIDTH-EOP_POS_WIDTH downto 0);
   signal words_cnt            : std_logic_vector(LENGTH_WIDTH-EOP_POS_WIDTH downto 0);
   signal words_cnt_zeros      : std_logic;
   signal eop_mx               : std_logic;
   signal expect_eop           : std_logic;



begin
   sop_pos_aug(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH)        <= RX_SOP_POS;
   shift_reg_aug(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH)      <= shift_reg;
   sig_tx_sop_pos_aug(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH) <= sig_tx_sop_pos;
   sop_pos_zero_fill_gen : if(EOP_POS_WIDTH>SOP_POS_WIDTH) generate
      sop_pos_aug(EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0) <= (others => '0');
      shift_reg_aug(EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0) <= (others => '0');
      sig_tx_sop_pos_aug(EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0) <= (others => '0');
   end generate;

   rx_valid       <= RX_SRC_RDY and sig_rx_dst_rdy;
   sop_after_eop  <= '1' when sop_pos_aug > RX_EOP_POS else '0';
   block_flu      <= header_detect and not LENGTH_READY;
   discard_word   <= (RX_SOP and RX_EOP and length_ones and (not sop_after_eop or (sop_after_eop and (length_ones_reg or (words_cnt_zeros and not length_zeros_reg))))) OR  -- SOP+EOP => new and possibly actual => result depends on relative positions of SOP and EOP
                     (RX_SOP and not RX_EOP and length_ones) OR -- SOP only => new packet => new discard
                     (not RX_SOP and length_ones_reg) OR -- not SOP => actual packet => registered discard
                     (words_cnt_zeros and not length_zeros_reg and not RX_SOP); -- not RDY after trimmed data
   discard_sop    <= length_ones;
   --                ( discarding act  && EOP    &&    EOP is for actual packet  )  ||(discarding new && EOP for new packet && new starting));
   discard_eop    <= (length_ones_reg and RX_EOP and (sop_after_eop or not RX_SOP)) or (length_ones and not sop_after_eop and header_detect);

   header_detect    <= RX_SOP and RX_SRC_RDY;
   length_zeros     <= '1' when LENGTH=(LENGTH_WIDTH-1 downto 0 => '0') else '0';
   length_ones      <= '1' when LENGTH=(LENGTH_WIDTH-1 downto 0 => '1') else '0';
   length_actual    <= ('0'&LENGTH)+conv_std_logic_vector((BLOCK_SIZE/8)-1,LENGTH_WIDTH+1);

   length_flag_regs : process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            length_ones_reg  <= '0';
            length_zeros_reg <= '0';
         elsif (header_detect='1' and rx_valid='1') then
            length_ones_reg  <= length_ones;
            length_zeros_reg <= length_zeros;
         end if;
      end if;
   end process;

   in_packet_tx_reg : process (CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            in_packet_tx <= '0';
         elsif TX_DST_RDY='1' and sig_tx_src_rdy='1' then
            in_packet_tx <= in_packet_tx xor (RX_SOP and not discard_sop) xor (eop_mx and not discard_eop);
         end if;
      end if;
   end process;

   TX_DATA    <= data_mx;
   TX_SOP_POS <= sig_tx_sop_pos;
   TX_EOP_POS <= eop_pos_mx;
   TX_SOP     <= RX_SOP and not discard_sop;
   TX_EOP     <= eop_mx and not discard_eop;
   TX_SRC_RDY <= sig_tx_src_rdy;
   RX_DST_RDY <= sig_rx_dst_rdy;
   sig_rx_dst_rdy <= (TX_DST_RDY or discard_word) and not block_flu;
   sig_tx_sop_pos <= RX_SOP_POS+shift;
   sig_tx_src_rdy <= (RX_SRC_RDY and not discard_word) and not block_flu;

   LENGTH_NEXT <= RX_SOP and rx_valid;


   -- DATA SHIFTING -------------------------------------------------
   -- odd packets
   odd_shifter : entity work.DATA_SHIFTER
   generic map(
      DATA_WIDTH      => DATA_WIDTH,
      SOP_POS_WIDTH   => SOP_POS_WIDTH
   ) port map (
      CLK             => CLK,
      RESET           => RESET,

      DATA_IN         => RX_DATA,
      DATA_IN_VLD     => rx_valid,
      DATA_OUT        => odd_shift_data,
      DATA_OUT_VLD    => open,
      SEL             => odd_shift
   );
   -- even packets
   even_shifter : entity work.DATA_SHIFTER
   generic map(
      DATA_WIDTH      => DATA_WIDTH,
      SOP_POS_WIDTH   => SOP_POS_WIDTH
   ) port map (
      CLK             => CLK,
      RESET           => RESET,

      DATA_IN         => RX_DATA,
      DATA_IN_VLD     => rx_valid,
      DATA_OUT        => even_shift_data,
      DATA_OUT_VLD    => open,
      SEL             => even_shift
   );
   -- packet marker (odd or even packets)
   odd_packet_i : process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            odd_packet <= '0';
         elsif (header_detect='1' and rx_valid='1') then
            odd_packet <= not odd_packet;
         end if;
      end if;
   end process;
   -- EOP and SOP based on packet mark
   eop_shift_data <= odd_shift_data  when odd_packet='1' else even_shift_data;
   sop_shift_data <= even_shift_data when odd_packet='1' else odd_shift_data;
   odd_shift      <= shift_reg       when odd_packet='1' else shift;
   even_shift     <= shift           when odd_packet='1' else shift_reg;
   -- shifters data integration
   --    SOP_POS is change point:
   --       below SOP_POS there may be old packet   =>  eop_shifter is used
   --       from SOP_POS there is always new packet =>  sop_shifter is used
   data_mx_gen : for i in 0 to BLOCKS-1 generate
      data_mx((i+1)*BLOCK_SIZE-1 downto BLOCK_SIZE*i) <= data_mx_array(i);
      eop_shift_data_array(i)                         <= eop_shift_data((i+1)*BLOCK_SIZE-1 downto BLOCK_SIZE*i);
      sop_shift_data_array(i)                         <= sop_shift_data((i+1)*BLOCK_SIZE-1 downto BLOCK_SIZE*i);
      sop_pos_cmp(i) <= '1' when conv_std_logic_vector(i,SOP_POS_WIDTH)<RX_SOP_POS else '0';
      data_mx_array_sel(i) <= sop_pos_cmp(i) or not header_detect;
      data_mx_array(i) <= eop_shift_data_array(i) when data_mx_array_sel(i) = '1' else sop_shift_data_array(i);
   end generate;
   -- shift register (remembers shift from SOP for the rest of the packet)
   shift_reg_i : process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            shift_reg <= (others => '0');
         elsif (header_detect='1' and rx_valid='1') then
            shift_reg <= shift;
         end if;
      end if;
   end process;
   -- shift computation
   shift_need <= (not length_actual(log2(BLOCK_SIZE/8)+SOP_POS_WIDTH-1 downto log2(BLOCK_SIZE/8)))+1;
   shift <= shift_need-RX_SOP_POS when
               (shift_need>RX_SOP_POS) and
               length_actual(LENGTH_WIDTH downto EOP_POS_WIDTH) = (LENGTH_WIDTH downto EOP_POS_WIDTH => '0') and
               (RX_EOP='1' and sop_after_eop='1') and
               length_zeros = '0'
            else (others => '0');
   -- DATA SHIFTING -(end)-------------------------------------------


   -- EOP and EOP_POS COMPUTING -------------------------------------
   -- remember expected eop_pos based on trim length
   expect_eop_pos_reg_i : process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            expect_eop_pos_reg <= (others => '0');
         elsif (header_detect='1' and rx_valid='1') then
            expect_eop_pos_reg <= expect_eop_pos;
         end if;
      end if;
   end process;
   -- compute necessary EOP_POS signals
   expect_end        <= ((LENGTH_WIDTH downto EOP_POS_WIDTH =>'0')&sig_tx_sop_pos_aug)+length_actual;
   expect_eop_pos    <= expect_end(EOP_POS_WIDTH-1 downto 0);
   expect_words      <= expect_end(LENGTH_WIDTH downto EOP_POS_WIDTH);
   expect_eop_pos_mx <= expect_eop_pos when in_packet_tx='0' else expect_eop_pos_reg;
   eop_pos_mx        <= RX_EOP_POS when
                           (length_zeros='1'     and in_packet_tx='0') or
                           (length_zeros_reg='1' and in_packet_tx='1') or
                           (expect_eop='0') or
                           ((('0'&RX_EOP_POS)+('0'&shift_reg_aug))<('0'&expect_eop_pos_mx) and RX_EOP='1')
                        else expect_eop_pos_mx;
   -- counter of packet words
   words_cnt_i : process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            words_cnt <= (others => '0');
         elsif (rx_valid='1') then
            if header_detect='1' then
               words_cnt <= expect_words;
            elsif words_cnt_zeros='0' then
               words_cnt <= words_cnt-1;
            end if;
         end if;
      end if;
   end process;
   words_cnt_zeros <= '1' when words_cnt=(LENGTH_WIDTH-EOP_POS_WIDTH downto 0 => '0') else '0';
   expect_eop  <= '1' when
                     ((words_cnt<=conv_std_logic_vector(1,LENGTH_WIDTH-EOP_POS_WIDTH-1)) and (header_detect='0' or (sop_after_eop='1' and RX_EOP='1')) and length_zeros_reg='0') or
                     (header_detect='1' and expect_words=(LENGTH_WIDTH-EOP_POS_WIDTH downto 0 => '0') and length_zeros='0')
                  else '0';
   eop_mx      <= RX_EOP when
                     expect_eop='0'
                  else words_cnt(0) when
                     (header_detect='0' or (header_detect='1' and sop_after_eop='1' and RX_EOP='1')) and
                     (words_cnt<=conv_std_logic_vector(1,LENGTH_WIDTH-EOP_POS_WIDTH-1))
                  else '1' when
                     expect_words=(LENGTH_WIDTH-EOP_POS_WIDTH downto 0 => '0')
                  else '0';
   -- EOP and EOP_POS COMPUTING -(end)-------------------------------

end architecture TRIMMING_UNIT_ARCH;
