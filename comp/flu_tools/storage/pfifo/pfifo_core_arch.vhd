-- pfifo_core_arch.vhd: Frame Link Unaligned protocol generic Packet Store-And-Forward FIFO core
-- Copyright (C) 2012 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 and min functions
use work.math_pack.all;

architecture full of FLU_PFIFO_CORE is
   --Constant declaration ---------------------------------
   --! Hight index of EOP_BLOCK
   constant EOP_BLOCK_HINDEX  : integer := log2(DATA_WIDTH/8) - 1;
   --! Low index of EOP_BLOCK
   constant EOP_BLOCK_LINDEX  : integer := log2(DATA_WIDTH/8) - SOP_POS_WIDTH;

   --Data FIFO --------------------------------------------
   --! Output data bus
   signal sig_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   --! RX_DST_RDY signal
   signal sig_rx_dst_rdy   : std_logic;
   --! SOP output
   signal sig_sop       : std_logic;
   --! EOP output
   signal sig_eop       : std_logic;
   --! SRC_RDY output
   signal sig_tx_src_rdy   : std_logic;
   --! Output masked SOP signal
   signal sig_sop_masked   : std_logic;
   --! Output masked EOP signal
   signal sig_eop_masked   : std_logic;
   --! Output masked SRC_RDY
   signal sig_tx_src_rdy_masked  : std_logic;
   --! Output masked DST_RDY
   signal sig_tx_dst_rdy_masked  : std_logic;
   --! Output SOP_POS
   signal sig_sop_pos            : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! Output EOP_POS
   signal sig_eop_pos            : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   --! Repaired SOP_POS
   signal sig_eop_pos_block      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! Signal SRC_RDY
   signal sig_rx_src_rdy         : std_logic;
   --------------------------------------------------------
   --! Packet counter in ASFIFO
   signal packet_cnt          : std_logic_vector(log2(DFIFO_ITEMS+1)-1 downto 0);
   --! RX domain increment
   signal packet_inc_rx : std_logic;
   --! TX domain decrement
   signal packet_dec_tx : std_logic;
   --------------------------------------------------------
   --! Need to mask SOP
   signal need_sop_mask       : std_logic;
   --! Need to mask SOP register
   signal reg_need_sop_mask   : std_logic;
   --! Unmask SOP signal - data ready
   signal sop_unmask          : std_logic;

begin

   --! Data FIFO
   DFIFO_I:entity work.FLU_FIFO
   generic map(
      --! Data width
      --! \brief Should be power of 2 and higher than 16
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      USE_BRAMS      => true,
      --! number of items in the FIFO
      ITEMS          => DFIFO_ITEMS,
      --! Size of block (for LSTBLK signal)
      BLOCK_SIZE     => BLOCK_SIZE,
      --! Width of STATUS signal available
      STATUS_WIDTH   => STATUS_WIDTH,
      --! Ouptut register (important to set in a case that USE_BRAMS = true)
      --False -  data will be available one clock earlier
      OUTPUT_REG => false
   )
   port map(
      -----------------------------------------------------
      --! \name Clocking & Reset interface
      -----------------------------------------------------
      CLK            => CLK,
      RESET          => RESET,

      -----------------------------------------------------
      --! \name Frame Link Unaligned input interface
      -----------------------------------------------------
      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => sig_rx_src_rdy,
      RX_DST_RDY    => sig_rx_dst_rdy,

      -----------------------------------------------------
      --! \name Frame Link Unaligned output interface
      -----------------------------------------------------
      TX_DATA       => sig_data,
      TX_SOP_POS    => sig_sop_pos,
      TX_EOP_POS    => sig_eop_pos,
      TX_SOP        => sig_sop,
      TX_EOP        => sig_eop,
      TX_SRC_RDY    => sig_tx_src_rdy,
      TX_DST_RDY    => sig_tx_dst_rdy_masked,

      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => RX_STATUS,
      FRAME_RDY      => open
   );

   --! Source ready signal (RX side)
   sig_rx_src_rdy <= RX_SRC_RDY;

   --! RX_DST_RDY output map
   RX_DST_RDY <= sig_rx_dst_rdy;

   --! TX DATA map
   TX_DATA  <= sig_data;

   --! TX_SRC_RDY output map
   TX_SRC_RDY <= sig_tx_src_rdy_masked;

   --! TX_SOP output map
   TX_SOP <= sig_sop_masked;

   --! TX_EOP output map
   TX_EOP <= sig_eop_masked;

   --! TX_SOP_POS output map
   TX_SOP_POS <= sig_sop_pos;

   --! TX_EOP_POS output map
   TX_EOP_POS <= sig_eop_pos;

   --! Output packet count information
   PACKET_COUNT <= packet_cnt;

   --------------------------------------------------------
   -- Packet inc. logic
   --------------------------------------------------------

   --! RX incrementation (increment if whole packet is going to be stored)
   packet_inc_rx <= '1' when(RX_SRC_RDY = '1' and sig_rx_dst_rdy = '1' and RX_EOP = '1') else
                    '0';

   --! Decrement signal on TX side
   packet_dec_tx <= '1' when (TX_DST_RDY = '1' and sig_tx_src_rdy_masked = '1' and sig_eop_masked = '1') else
                    '0';

   --! \brief Packet counter of stored packets in ASFIFO (synchronized in TX domain)
   packet_cntp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            packet_cnt <= (others=>'0');
         else
            if(packet_inc_rx = '1' and packet_dec_tx = '0')then
               packet_cnt <= packet_cnt + 1;
            elsif(packet_inc_rx = '0' and packet_dec_tx = '1')then
               packet_cnt <= packet_cnt - 1;
            else
               packet_cnt <= packet_cnt;
            end if;
         end if;
      end if;
   end process;

   --------------------------------------------------------
   --Masking control logic
   --------------------------------------------------------
   --! #_RDY masking control
   rdy_mask_contp:process(sig_tx_src_rdy,TX_DST_RDY,need_sop_mask,reg_need_sop_mask,packet_cnt)
   begin
      --Default behaviour -> copy signals -------
      sig_tx_src_rdy_masked <= sig_tx_src_rdy;
      sig_tx_dst_rdy_masked <= TX_DST_RDY;

      if(packet_cnt > 0)then
         if(need_sop_mask = '1' and reg_need_sop_mask = '0') then
            --We need to halt data from ASFIFO
            --sig_tx_src_rdy_masked <= sig_tx_src_rdy; -> copy
            sig_tx_dst_rdy_masked <= '0';
         end if;
      else
         --Data are not available / data are buffered
         sig_tx_src_rdy_masked <= '0';
         sig_tx_dst_rdy_masked <= '0';
      end if;
   end process;

   --! EOP_POS block extraction
   sig_eop_pos_block <= sig_eop_pos(EOP_BLOCK_HINDEX downto EOP_BLOCK_LINDEX);

   --! Need SOP mask generator -> Word is shared and actual packet count is 1
   need_sop_mask <= '1' when(packet_cnt = 1 and sig_eop = '1' and sig_sop = '1' and
                             sig_tx_src_rdy = '1' and TX_DST_RDY = '1' and sig_sop_pos > sig_eop_pos_block) else
                    '0';

   --! SOP unmask generator -> data are ready for new masked packet
   sop_unmask <= '1' when(packet_cnt > 0 and sig_tx_src_rdy = '1' and TX_DST_RDY = '1' and
                          reg_need_sop_mask = '1') else
                 '0';

   --! \brief Remember SOP masking in next transfer.
   --! \details SET when EOP, RESET when SOP  & DATA available
   need_sop_mask_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if((RESET = '1') OR sop_unmask = '1')then
            --Default value during reset OR masked detected for SOP & actual word is still
            --on output of ASFIFO (we detect the same condition again).
            reg_need_sop_mask <= '0';
         else
            if(need_sop_mask = '1')then
               --Remeber this information for later use
               reg_need_sop_mask <= '1';
            end if;
         end if;
      end if;
   end process;

   --! Masking control generator
   sop_eop_mask_genp:process(sig_eop,sig_sop,need_sop_mask,reg_need_sop_mask,sop_unmask)
   begin
      --Default behaviour -> copy signals -------
      sig_eop_masked <= sig_eop;
      sig_sop_masked <= sig_sop;

      --Masking process -------------------------
      if(need_sop_mask = '1' and reg_need_sop_mask = '0')then
         --sig_eop_masked <= sig_eop; -> copy this value
         sig_sop_masked <= '0'; --> mask signal
      elsif(sop_unmask = '1')then
         --We need to mask EOP
         sig_eop_masked <= '0';
         --sig_sop_masked <= sig_sop; --> copy signal
      end if;
   end process;

end architecture full;
