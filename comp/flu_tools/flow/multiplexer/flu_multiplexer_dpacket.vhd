-- flu_multiplexer_dpacket.vhd
--!
--! \file
--! \brief Packet oriented FLU multiplexer, with optional packet discarding
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \author Jan Kučera <xkucer73@stud.fit.vutbr.cz>
--! \date 2012, 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function.
use work.math_pack.all;

--! \brief Entity of FLU multiplexer, with optional packet discarding.
entity FLU_MULTIPLEXER_DPACKET is
   generic (
      DATA_WIDTH     : integer := 512;
      SOP_POS_WIDTH  : integer := 3;
      INPUT_PORTS    : integer := 2
   );
   port (
      --! \name Common interface
      RESET         : in  std_logic;
      CLK           : in  std_logic;

      --! \name Control interface
      --! \details Port blocking settings:
      --!   when 1:  specific port is blocked
      --!   when 0:  specific port discard packets at the same rate as selected
      --!            one forwarding (something like exclusive packet selection),
      --!            selected port could not be blocked
      CTRL_SEL      : in std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
      CTRL_BLOCK    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      CTRL_READY    : in std_logic;
      CTRL_NEXT     : out std_logic;

      --! \name Frame Link Unaligned input interfaces
      RX_DATA       : in std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_EOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);

      --! \name Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity;

--! \brief Implementation of FLU multiplexer, with optional packet discarding.
architecture FULL of FLU_MULTIPLEXER_DPACKET is

   -- ----------------------------- Constants ---------------------------------

   constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);


   -- ------------------------------ Signals ----------------------------------

   signal ctrl_sel_in    : std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
   signal ctrl_block_in  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal ctrl_ready_in  : std_logic;
   signal ctrl_next_out  : std_logic;

   signal rx_data_in     : std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
   signal rx_sop_pos_in  : std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
   signal rx_eop_pos_in  : std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
   signal rx_sop_in      : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rx_eop_in      : std_logic_vector(INPUT_PORTS-1 downto 0);

   signal rx_src_rdy_in  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rx_dst_rdy_out : std_logic_vector(INPUT_PORTS-1 downto 0);

   signal mx_rx_dst_rdy  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal mx_rx_src_rdy  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rx_sop_detect  : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal rx_sop_detect_all : std_logic;

   signal mux_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mux_sop_pos    : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   signal mux_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal mux_sop        : std_logic;
   signal mux_eop        : std_logic;
   signal mux_src_rdy    : std_logic;
   signal mux_dst_rdy    : std_logic;

   signal mux_eop_sop    : std_logic;
   signal mux_sop_out    : std_logic;
   signal mux_eop_out    : std_logic;

   signal tx_src_rdy_out : std_logic;
   signal tx_dst_rdy_in  : std_logic;

   signal rx_sel         : std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
   signal sel_reg        : std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
   signal rx_block       : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal block_reg      : std_logic_vector(INPUT_PORTS-1 downto 0);

   signal block_mask     : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal ctrl_change    : std_logic;
   signal ctrl_nochange  : std_logic;

   signal reg_frame_sent  : std_logic;
   signal reg_frame_start : std_logic;

begin

   --! Expand SOP_POS with zeros due to comparison
   mux_sop_pos_augment : if EOP_POS_WIDTH > SOP_POS_WIDTH generate
      mux_sop_pos(EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0) <= (others => '0');
   end generate;

   --! Control input signal
   ctrl_sel_in    <= CTRL_SEL;
   ctrl_block_in  <= CTRL_BLOCK;
   ctrl_ready_in  <= CTRL_READY;
   CTRL_NEXT <= ctrl_next_out;

   --! FLU input signals
   rx_data_in     <= RX_DATA;
   rx_sop_pos_in  <= RX_SOP_POS;
   rx_eop_pos_in  <= RX_EOP_POS;
   rx_sop_in      <= RX_SOP;
   rx_eop_in      <= RX_EOP;
   rx_src_rdy_in  <= RX_SRC_RDY;
   RX_DST_RDY     <= rx_dst_rdy_out;

   block_mask_gen : for i in 0 to INPUT_PORTS-1 generate
      block_mask(i) <= '0' when conv_integer(ctrl_sel_in) = i else ctrl_block_in(i);
   end generate;

   rx_sel        <= ctrl_sel_in when reg_frame_sent='1' and ctrl_ready_in = '1' else sel_reg;
   rx_block      <= block_mask when reg_frame_sent='1' and ctrl_ready_in = '1' else block_reg;
   ctrl_nochange <= '1' when ctrl_sel_in=sel_reg and ctrl_ready_in='1' else '0';
   ctrl_change   <= '0' when ctrl_sel_in=sel_reg and ctrl_ready_in='1' else '1';

   process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            sel_reg <= (others => '0');
            block_reg <= (others => '0');
         elsif (ctrl_ready_in = '1' and ctrl_next_out = '1') then
            sel_reg <= ctrl_sel_in;
            block_reg <= block_mask;
         end if;
      end if;
   end process;

   rx_dst_rdy_gen : for i in 0 to INPUT_PORTS-1 generate
      rx_dst_rdy_out(i) <= mx_rx_dst_rdy(i) and not(mux_sop_out and not (rx_sop_detect_all and mux_dst_rdy))
          when conv_integer(rx_sel) = i else
          mx_rx_dst_rdy(i) and not(rx_sop_detect(i) and not (rx_sop_detect_all and mux_dst_rdy and not rx_block(i)));

      mx_rx_src_rdy(i) <= rx_src_rdy_in(i) and (not(mux_sop_out and not rx_sop_detect_all))
          when conv_integer(rx_sel) = i else
          rx_src_rdy_in(i) and not rx_block(i) and not(rx_sop_detect(i) and not rx_sop_detect_all);

      rx_sop_detect(i) <= rx_sop_in(i) and rx_src_rdy_in(i);
   end generate;

   rx_sop_detect_all_i : process(rx_sop_detect, rx_block)
      variable and_sop : std_logic;
   begin
      and_sop := '1';
      for k in 0 to INPUT_PORTS-1 loop
         and_sop := and_sop and (rx_sop_detect(k) or rx_block(k));
      end loop;
      rx_sop_detect_all <= and_sop;
   end process;

   --! FLU basic multiplexer instantiation
   rx_flu_mux_i : entity work.FLU_MULTIPLEXER
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      INPUT_PORTS    => INPUT_PORTS,
      BLOCKING       => false
   ) port map (
      --! Common signals
      CLK   => CLK,
      RESET => RESET,
      --! Control signal
      SEL => rx_sel,
      --! Input FLUs
      RX_DATA    => rx_data_in,
      RX_SOP_POS => rx_sop_pos_in,
      RX_EOP_POS => rx_eop_pos_in,
      RX_SOP     => rx_sop_in,
      RX_EOP     => rx_eop_in,
      RX_SRC_RDY => mx_rx_src_rdy,
      RX_DST_RDY => mx_rx_dst_rdy,
      --! Output FLU
      TX_DATA    => mux_data,
      TX_SOP_POS => mux_sop_pos(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH),
      TX_EOP_POS => mux_eop_pos,
      TX_SOP     => mux_sop,
      TX_EOP     => mux_eop,
      TX_SRC_RDY => mux_src_rdy,
      TX_DST_RDY => mux_dst_rdy
   );

   --! SOP, EOP output signals masking
   mux_eop_sop <= mux_sop and mux_eop and mux_src_rdy when mux_sop_pos > mux_eop_pos else '0';
   mux_sop_out <= mux_sop and (reg_frame_sent or not ctrl_change);
   mux_eop_out <= mux_eop and (not mux_eop_sop or not reg_frame_sent);

   --! State register
   frame_state_reg: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_frame_sent <= '1';
            reg_frame_start <= '0';
         elsif (tx_src_rdy_out = '1' and tx_dst_rdy_in = '1') then
--            reg_frame_sent <= mux_eop and ((not mux_eop_sop or ctrl_change) and not mux_sop_out);
--            reg_frame_sent <= mux_eop and ((not mux_eop_sop and not mux_sop_out) or ctrl_change);
--            reg_frame_sent <= mux_eop and ((not mux_eop_sop and not mux_sop_out) or (not ctrl_change and not mux_eop_sop and mux_sop_out) or (ctrl_change and not mux_sop_out));
            reg_frame_sent <= mux_eop and ((not mux_eop_sop and not mux_sop_out) or (not ctrl_change and not mux_eop_sop and mux_sop_out) or (ctrl_change and not mux_sop_out) or (ctrl_change and not mux_eop_sop));
            reg_frame_start <= mux_eop and mux_eop_sop and ctrl_change;
         end if;
      end if;
   end process;

   --! MUX, TX & CTRL ready signals
   mux_dst_rdy <= tx_dst_rdy_in and (ctrl_ready_in or not mux_sop_out) and (reg_frame_sent or not ctrl_change or not mux_sop or not mux_eop_sop);
   tx_src_rdy_out <= mux_src_rdy and (ctrl_ready_in or not mux_sop_out) and not (reg_frame_sent and not reg_frame_start and not mux_sop_out);
   ctrl_next_out <= mux_sop_out and tx_src_rdy_out and tx_dst_rdy_in;

   --! FLU output signals
   TX_DATA       <= mux_data;
   TX_SOP_POS    <= mux_sop_pos(EOP_POS_WIDTH-1 downto EOP_POS_WIDTH-SOP_POS_WIDTH);
   TX_EOP_POS    <= mux_eop_pos;
   TX_SOP        <= mux_sop_out;
   TX_EOP        <= mux_eop_out;
   TX_SRC_RDY    <= tx_src_rdy_out and (not reg_frame_sent or reg_frame_start or mux_sop_out);
   tx_dst_rdy_in <= TX_DST_RDY;

end architecture;
