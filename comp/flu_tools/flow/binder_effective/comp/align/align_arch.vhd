--
-- align_arch.vhd: FLU align component architecture
-- Copyright (C) 2014 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLU_ALIGN is
   -- Constants and ranges declarations ---------------------------------------
   --! EOP_POS bus length
   constant EOP_POS_BUS_WIDTH    : integer := log2(DATA_WIDTH/8);
   --! EOP block range declaration
   subtype EOP_BLK is natural range EOP_POS_BUS_WIDTH-1 downto EOP_POS_BUS_WIDTH-SOP_POS_WIDTH;
   --! Number of blocks in word
   constant BLK_COUNT   : integer := 2**SOP_POS_WIDTH;
   --! Width of one block
   constant BLK_WIDTH   : integer := DATA_WIDTH/BLK_COUNT;

   --! FLU input signals
   signal in_rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_rx_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_rx_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_rx_sop        : std_logic;
   signal in_rx_eop        : std_logic;
   signal in_rx_src_rdy    : std_logic;
   signal in_rx_dst_rdy    : std_logic;

   signal flu2fl_tx_sop_n        : std_logic;
   signal flu2fl_tx_eop_n        : std_logic;
   signal flu2fl_tx_src_rdy_n    : std_logic;
   signal flu2fl_tx_dst_rdy_n    : std_logic;
   signal flu2fl_tx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flu2fl_tx_drem         : std_logic_vector(abs(log2(DATA_WIDTH/8)-1) downto 0);

begin

   -- -------------------------------------------------------------------------
   -- Input port map
   -- -------------------------------------------------------------------------
   -- Deal with map of the input RX flow
   in_rx_data        <= RX_DATA;
   in_rx_sop_pos     <= RX_SOP_POS;
   in_rx_eop_pos     <= RX_EOP_POS;
   in_rx_sop         <= RX_SOP;
   in_rx_eop         <= RX_EOP;
   in_rx_src_rdy     <= RX_SRC_RDY;
   RX_DST_RDY        <= in_rx_dst_rdy;

   -- -------------------------------------------------------------------------
   -- Align logic
   -- -------------------------------------------------------------------------
   ALIGN_GEN:if(ALIGN = true)generate
      FLU2FL : entity work.flu2fl
         generic map(
            -- data width of input FLU and output FL interfaces
            DATA_WIDTH        => DATA_WIDTH,
            -- sop_pos width of input FLU
            SOP_POS_WIDTH     => SOP_POS_WIDTH,
            -- use input pipe
            IN_PIPE_EN        => IN_PIPE_EN,
            -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
            --    "SHREG" - pipe implemented as shift register
            --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
            --              on wide buses and on Intel/Altera devices
            IN_PIPE_TYPE      => IN_PIPE_TYPE,
            -- use output register of input pipe
            IN_PIPE_OUTREG    => IN_PIPE_OUTREG,
            -- use output pipe
            OUT_PIPE_EN       => OUT_PIPE_EN,
            -- same as IN_PIPE_TYPE
            OUT_PIPE_TYPE      => OUT_PIPE_TYPE,
            -- use output register of input pipe
            OUT_PIPE_OUTREG   => OUT_PIPE_OUTREG
         )
         port map(
            -- common interface
            CLK            => CLK,
            RESET          => RESET,

            -- input interface (FLU)
            RX_DATA        => in_rx_data,
            RX_SOP_POS     => in_rx_sop_pos,
            RX_EOP_POS     => in_rx_eop_pos,
            RX_SOP         => in_rx_sop,
            RX_EOP         => in_rx_eop,
            RX_SRC_RDY     => in_rx_src_rdy,
            RX_DST_RDY     => in_rx_dst_rdy,

            -- output interface (FL)
            TX_SOF_N       => open,
            TX_EOP_N       => flu2fl_tx_eop_n,
            TX_SOP_N       => flu2fl_tx_sop_n,
            TX_EOF_N       => open,
            TX_SRC_RDY_N   => flu2fl_tx_src_rdy_n,
            TX_DST_RDY_N   => flu2fl_tx_dst_rdy_n,
            TX_DATA        => flu2fl_tx_data,
            TX_DREM        => flu2fl_tx_drem
           );
      end generate;

      NO_ALIGN_GEN:if(ALIGN = false)generate
         flu2fl_tx_data <= in_rx_data;
         flu2fl_tx_drem <= in_rx_eop_pos;
         flu2fl_tx_src_rdy_n <= not(in_rx_src_rdy);
         in_rx_dst_rdy <= not(flu2fl_tx_dst_rdy_n);
         flu2fl_tx_sop_n <= not(in_rx_sop);
         flu2fl_tx_eop_n <= not(in_rx_eop);
      end generate;

   -- -------------------------------------------------------------------------
   -- Output port map
   -- -------------------------------------------------------------------------
   --! FrameLink Unaligned output lane 0
   TX_DATA              <= flu2fl_tx_data;
   TX_SOP_POS           <= (others=>'0');
   TX_EOP_POS           <= flu2fl_tx_drem;
   TX_SOP               <= not(flu2fl_tx_sop_n);
   TX_EOP               <= not(flu2fl_tx_eop_n);
   TX_SRC_RDY           <= not(flu2fl_tx_src_rdy_n);
   flu2fl_tx_dst_rdy_n  <= not(TX_DST_RDY);


end architecture FULL;
