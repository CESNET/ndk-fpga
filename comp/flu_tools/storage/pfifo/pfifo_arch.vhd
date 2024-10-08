-- pfifo_arch.vhd: Frame Link Unaligned protocol generic Packet Store-And-Forward FIFO
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

architecture full of FLU_PFIFO is
   --Constant declaration ---------------------------------
   --! Hight index of EOP_BLOCK
   constant EOP_BLOCK_HINDEX  : integer := log2(DATA_WIDTH/8) - 1;
   --! Low index of EOP_BLOCK
   constant EOP_BLOCK_LINDEX  : integer := log2(DATA_WIDTH/8) - SOP_POS_WIDTH;

   -----------------------------------------------
   -- Store-and-forward fifo output
   -----------------------------------------------
   --! DATA signal
   signal sig_pfifo_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   --! SOP_POS signal
   signal sig_pfifo_sop_pos   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! EOP_POS signal
   signal sig_pfifo_eop_pos   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   --! SOP signal
   signal sig_pfifo_sop       : std_logic;
   --! EOP signal
   signal sig_pfifo_eop       : std_logic;
   --! SRC_RDY signal
   signal sig_pfifo_src_rdy   : std_logic;
   --! DST_RDY signal
   signal sig_pfifo_dst_rdy   : std_logic;

   -----------------------------------------------
   -- Asynchronous FIFO signals
   -----------------------------------------------
   --! DATA signal
   signal sig_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   --! SOP_POS signal
   signal sig_tx_sop_pos   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! EOP_POS signal
   signal sig_tx_eop_pos   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   --! SOP signal
   signal sig_tx_sop       : std_logic;
   --! EOP signal
   signal sig_tx_eop       : std_logic;
   --! SRC_RDY signal
   signal sig_tx_src_rdy   : std_logic;
   --! DST_RDY signal
   signal sig_tx_dst_rdy   : std_logic;
   --! Packet count
   signal sig_tx_packet_count : std_logic_vector(log2(DFIFO_ITEMS+1)-1 downto 0);

   --------------------------------------------------------
   -- Output pipeline signals
   --------------------------------------------------------
   --! DATA signal
   signal sig_pipe_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   --! SOP_POS signal
   signal sig_pipe_sop_pos   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! EOP_POS signal
   signal sig_pipe_eop_pos   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   --! SOP signal
   signal sig_pipe_sop       : std_logic;
   --! EOP signal
   signal sig_pipe_eop       : std_logic;
   --! SRC_RDY signal
   signal sig_pipe_src_rdy   : std_logic;
   --! DST_RDY signal
   signal sig_pipe_dst_rdy   : std_logic;

   --------------------------------------------------------
   --! SOP detector for asertion
   signal assert_trans_on     : std_logic;
   --! EOP block detector
   signal assert_eop_block    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! SOP block detector
   signal assert_sop_block    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);

begin

   --Assertions -------------------------------------------
   --! SOP block detection
   assert_sop_block <= sig_tx_sop_pos;
   --! EOP bloc detection
   assert_eop_block <= sig_tx_eop_pos(EOP_BLOCK_HINDEX downto EOP_BLOCK_LINDEX);

   --! \brief This register helps to detect assertion during transfer
   trans_detp:process(TX_CLK)
   begin
      if(TX_CLK = '1' and TX_CLK'event)then
         if(TX_RESET = '1')then
            assert_trans_on <= '0';
         else
            if(TX_DST_RDY = '1' and sig_tx_src_rdy = '1' and sig_tx_sop = '1' and assert_eop_block < assert_sop_block)then
               assert_trans_on <= '1';
            elsif(TX_DST_RDY = '1' and sig_tx_src_rdy = '1'and sig_tx_eop = '1')then
               assert_trans_on <= '0';
            end if;
         end if;
      end if;
   end process;

   --! Assertion for Store-and-forward
   assertTX_SF:process(TX_CLK)
   begin
      if(TX_CLK = '1' and TX_CLK'event)then
         if(assert_trans_on = '1')then
            --If the transaction is enabled, control that ...
            assert (sig_tx_src_rdy = '1')
                   report "Store-and-forward condition broken. There was detected SRC_RDY=0 during packet transfer"
                   severity error;
         end if;
      end if;
   end process;

   --------------------------------------------------------
   --! Asynchronous FIFO for clock domain cross (ASFIFO from base library)
   ASFIFO_NO_BRAM_STAGE_ON:if DISABLE_ASFIFO = false and BRAM_ASFIFO = false generate
      FLU_ASFIFO_I:entity work.FLU_ASFIFO
      generic map(
         --! \brief Data width of input and output FrameLinkUnaligned data.
         --! \details Must be greater than 8.
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,
         ITEMS          => HFIFO_ITEMS,
         AUTO_PIPELINE  => true
      )
      port map(
         --! \name Resets and clocks

         --! Input FLU clock
         RX_CLK         => RX_CLK,
         --! Input FLU reset
         RX_RESET       => RX_RESET,
         --! Output FLU clock
         TX_CLK         => TX_CLK,
         --! Output FLU reset
         TX_RESET       => TX_RESET,

         --! \name Write interface

         --! Write side data
         RX_DATA        => RX_DATA,
         --! Write side position of packet start inside word
         RX_SOP_POS     => RX_SOP_POS,
         --! Write side position of packet end inside word
         RX_EOP_POS     => RX_EOP_POS,
         --! Write side start of packet
         RX_SOP         => RX_SOP,
         --! Write side end of packet
         RX_EOP         => RX_EOP,
         --! Write side source ready
         RX_SRC_RDY     => RX_SRC_RDY,
         --! Write side destination ready
         RX_DST_RDY     => RX_DST_RDY,
         --! Write side status
         RX_STATUS      => open,

         --! \name Read interface

         --! Read side data
         TX_DATA        => sig_pfifo_data,
         --! Read side position of packet start inside word
         TX_SOP_POS     => sig_pfifo_sop_pos,
         --! Read side position of packet end inside word
         TX_EOP_POS     => sig_pfifo_eop_pos,
         --! Read side start of packet
         TX_SOP         => sig_pfifo_sop,
         --! Read side end of packet
         TX_EOP         => sig_pfifo_eop,
         --! Read side source ready
         TX_SRC_RDY     => sig_pfifo_src_rdy,
         --! Read side destination ready
         TX_DST_RDY     => sig_pfifo_dst_rdy
      );
   end generate;

   --! Asynchronous FIFO for clock domain cross (BRAM oriented)
   ASFIFO_BRAM_STAGE_ON:if DISABLE_ASFIFO = false and BRAM_ASFIFO = true generate
      FLU_ASFIFO_I:entity work.FLU_ASFIFO_BRAM_XILINX
        generic map(
          --! \brief Data width of input and output FrameLinkUnaligned data.
          --! \details Must be greater than 8.
          DATA_WIDTH       => DATA_WIDTH,
          --! \brief Width of SOP_POS signal.
          --! \description Determines size of data allocation block.
          SOP_POS_WIDTH    => SOP_POS_WIDTH,
          --! \brief Number of items in the FIFO
          --! \description Only powers of 512 supported.
          ITEMS            => HFIFO_ITEMS,
          --! \brief Target FPGA type.
          --! \description Supported values are "VIRTEX5", "VIRTEX6" or "7SERIES".
          DEVICE           => BRAM_DEVICE
        )
        port map(
          --! \name Write interface

          --! Input FLU clock
          RX_CLK           => RX_CLK,
          RX_RESET         => RX_RESET,
          --! Write side data
          RX_DATA          => RX_DATA,
          --! Write side position of packet start inside word
          RX_SOP_POS       => RX_SOP_POS,
          --! Write side position of packet end inside word
          RX_EOP_POS       => RX_EOP_POS,
          --! Write side start of packet
          RX_SOP           => RX_SOP,
          --! Write side end of packet
          RX_EOP           => RX_EOP,
          --! Write side source ready
          RX_SRC_RDY       => RX_SRC_RDY,
          --! Write side destination ready
          RX_DST_RDY       => RX_DST_RDY,

          --! \name Read interface

          --! Output FLU clock
          TX_CLK           => TX_CLK,
          TX_RESET         => TX_RESET,
          --! Read side data
          TX_DATA          => sig_pfifo_data,
          --! Read side position of packet start inside word
          TX_SOP_POS       => sig_pfifo_sop_pos,
          --! Read side position of packet end inside word
          TX_EOP_POS       => sig_pfifo_eop_pos,
          --! Read side start of packet
          TX_SOP           => sig_pfifo_sop,
          --! Read side end of packet
          TX_EOP           => sig_pfifo_eop,
          --! Read side source ready
          TX_SRC_RDY       => sig_pfifo_src_rdy,
          --! Read side destination ready
          TX_DST_RDY       => sig_pfifo_dst_rdy
          );
   end generate;

   ASFIFO_STAGE_OFF:if DISABLE_ASFIFO = true generate
      sig_pfifo_data       <= RX_DATA;
      sig_pfifo_sop_pos    <= RX_SOP_POS;
      sig_pfifo_eop_pos    <= RX_EOP_POS;
      sig_pfifo_sop        <= RX_SOP;
      sig_pfifo_eop        <= RX_EOP;
      sig_pfifo_src_rdy    <= RX_SRC_RDY;
      RX_DST_RDY           <= sig_pfifo_dst_rdy;
   end generate;

   --! Packet fifo without output register
   PFIFO_CORE:entity work.FLU_PFIFO_CORE
   generic map(
      --! Data width
      --! \brief Should be power of 2 and higher than 16
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      --! number of items in the FIFO
      DFIFO_ITEMS    => DFIFO_ITEMS,
      --! Size of block (for LSTBLK signal)
      BLOCK_SIZE     => BLOCK_SIZE,
      --! Width of STATUS signal available
      STATUS_WIDTH   => STATUS_WIDTH
   )
   port map(
      -----------------------------------------------------
      --! \name Clocking & Reset interface
      -----------------------------------------------------
      CLK            => TX_CLK,
      RESET          => TX_RESET,

      -----------------------------------------------------
      --! \name Frame Link Unaligned input interface
      -----------------------------------------------------
      RX_DATA       => sig_pfifo_data,
      RX_SOP_POS    => sig_pfifo_sop_pos,
      RX_EOP_POS    => sig_pfifo_eop_pos,
      RX_SOP        => sig_pfifo_sop,
      RX_EOP        => sig_pfifo_eop,
      RX_SRC_RDY    => sig_pfifo_src_rdy,
      RX_DST_RDY    => sig_pfifo_dst_rdy,
      RX_STATUS     => RX_STATUS,

      -----------------------------------------------------
      --! \name Frame Link Unaligned output interface
      -----------------------------------------------------
      TX_DATA       => sig_pipe_data,
      TX_SOP_POS    => sig_pipe_sop_pos,
      TX_EOP_POS    => sig_pipe_eop_pos,
      TX_SOP        => sig_pipe_sop,
      TX_EOP        => sig_pipe_eop,
      TX_SRC_RDY    => sig_pipe_src_rdy,
      TX_DST_RDY    => sig_pipe_dst_rdy,

      -----------------------------------------------------
      --! \name Output statistical interface
      -----------------------------------------------------
      PACKET_COUNT   => sig_tx_packet_count
   );


   --------------------------------------------------------
   --Output pipeline (based ond generic)
   --------------------------------------------------------
   FLU_OUTPUT_PIPE_GEN: if(USE_OUT_PIPELINE = true) generate
      OUT_PIPE_I:entity work.FLU_PIPE
      generic map(
         -- FrameLinkUnaligned Data Width
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,
         USE_OUTREG     => false
      )
      port map(
         -- Common interface
         CLK            => TX_CLK,
         RESET          => TX_RESET,

         -- Input interface
         RX_DATA       => sig_pipe_data,
         RX_SOP_POS    => sig_pipe_sop_pos,
         RX_EOP_POS    => sig_pipe_eop_pos,
         RX_SOP        => sig_pipe_sop,
         RX_EOP        => sig_pipe_eop,
         RX_SRC_RDY    => sig_pipe_src_rdy,
         RX_DST_RDY    => sig_pipe_dst_rdy,

         -- Output interface
         TX_DATA       => sig_tx_data,
         TX_SOP_POS    => sig_tx_sop_pos,
         TX_EOP_POS    => sig_tx_eop_pos,
         TX_SOP        => sig_tx_sop,
         TX_EOP        => sig_tx_eop,
         TX_SRC_RDY    => sig_tx_src_rdy,
         TX_DST_RDY    => sig_tx_dst_rdy
      );
   end generate;

   NO_FLU_OUTPUT_PIPE_GEN: if(USE_OUT_PIPELINE = false) generate
      --No Pipeline, connect FLU signals
      sig_tx_data       <= sig_pipe_data;
      sig_tx_sop_pos    <= sig_pipe_sop_pos;
      sig_tx_eop_pos    <= sig_pipe_eop_pos;
      sig_tx_sop        <= sig_pipe_sop;
      sig_tx_eop        <= sig_pipe_eop;
      sig_tx_src_rdy    <= sig_pipe_src_rdy;
      sig_pipe_dst_rdy  <= sig_tx_dst_rdy;
   end generate;

   --------------------------------------------------------
   --Output signal map
   --------------------------------------------------------

   --! DATA output map
   TX_DATA     <= sig_tx_data;
   --! SOP_POS output map
   TX_SOP_POS  <= sig_tx_sop_pos;
   --! EOP_POS output map
   TX_EOP_POS  <= sig_tx_eop_pos;
   --! SOP output map
   TX_SOP      <= sig_tx_sop;
   --! EOP output map
   TX_EOP      <= sig_tx_eop;
   --! SRC_RDY output map
   TX_SRC_RDY  <= sig_tx_src_rdy;

   --! Packetou count output map
   PACKET_COUNT <= sig_tx_packet_count;

   --! PFIFO DST_RDY signal map
   sig_tx_dst_rdy <= TX_DST_RDY;

end architecture full;
