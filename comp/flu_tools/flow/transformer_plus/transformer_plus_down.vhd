-- transformer_plus_down.vhd: Implementation of DOWN architecture of FrameLinkUnaligned Transformer component.
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--            Roman Striz  <striz@netcope.com> channel support added
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- library containing log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FLU_TRANSFORMER_PLUS_DOWN is
  generic(
    HEADER_WIDTH     : integer := 8;
    CHANNEL_WIDTH    : integer := 2;
    RX_DATA_WIDTH    : integer := 512;
    RX_SOP_POS_WIDTH : integer := 3;
    TX_DATA_WIDTH    : integer := 256;
    TX_SOP_POS_WIDTH : integer := 2
  );
  port(
    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- Frame Link Unaligned input interface
    RX_HEADER     : in std_logic_vector(HEADER_WIDTH-1 downto 0);
    RX_CHANNEL    : in std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    RX_DATA       : in std_logic_vector(RX_DATA_WIDTH-1 downto 0);
    RX_SOP_POS    : in std_logic_vector(max(1,RX_SOP_POS_WIDTH)-1 downto 0);
    RX_EOP_POS    : in std_logic_vector(max(1,log2(RX_DATA_WIDTH/8))-1 downto 0);
    RX_SOP        : in std_logic;
    RX_EOP        : in std_logic;
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    -- Frame Link Unaligned output interface
    TX_HEADER     : out std_logic_vector(HEADER_WIDTH-1 downto 0);
    TX_CHANNEL    : out std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    TX_DATA       : out std_logic_vector(TX_DATA_WIDTH-1 downto 0);
    TX_SOP_POS    : out std_logic_vector(max(1,TX_SOP_POS_WIDTH)-1 downto 0);
    TX_EOP_POS    : out std_logic_vector(max(1,log2(TX_DATA_WIDTH/8))-1 downto 0);
    TX_SOP        : out std_logic;
    TX_EOP        : out std_logic;
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic
  );
end entity;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of FLU_TRANSFORMER_PLUS_DOWN is
  constant RX_BLOCKS            : integer := RX_DATA_WIDTH/TX_DATA_WIDTH;

  signal rx_sop_array           : std_logic_vector(RX_BLOCKS-1 downto 0);
  signal rx_eop_array           : std_logic_vector(RX_BLOCKS-1 downto 0);
  signal tx_sop_sig             : std_logic_vector(0 downto 0);
  signal tx_eop_sig             : std_logic_vector(0 downto 0);

  signal in_packet_reg_new      : std_logic;
  signal in_packet_reg          : std_logic;
  signal in_packet_border_reg   : std_logic;
  signal rx_sop_pos_augment     : std_logic_vector(TX_SOP_POS_WIDTH+log2(RX_BLOCKS) downto 0);
  signal rx_sop_block_pos       : std_logic_vector(log2(RX_BLOCKS)-1 downto 0);
  signal rx_eop_block_pos       : std_logic_vector(log2(RX_BLOCKS)-1 downto 0);
  signal word_cleared           : std_logic;

  signal sel                    : std_logic_vector(log2(RX_BLOCKS)-1 downto 0);
  signal cnt                    : std_logic_vector(log2(RX_BLOCKS)-1 downto 0);
  signal cnt_will_overflow      : std_logic;

begin
  -- preprocessing of RX SOP and EOP possitions for easier manipulation wtih them
  rx_sop_pos_augment <= RX_SOP_POS & (TX_SOP_POS_WIDTH-RX_SOP_POS_WIDTH+log2(RX_BLOCKS) downto 0 => '0');
  rx_sop_block_pos   <= rx_sop_pos_augment(TX_SOP_POS_WIDTH+log2(RX_BLOCKS) downto TX_SOP_POS_WIDTH+1);
  rx_eop_block_pos   <= RX_EOP_POS(log2(RX_DATA_WIDTH/8)-1 downto log2(RX_DATA_WIDTH/8)-log2(RX_BLOCKS));

  -- mask of SOP and EOP position for RX data blocks
  sop_mask_of_blocks : entity work.dec1fn_enable
   generic map (RX_BLOCKS)
   port map (rx_sop_block_pos,RX_SOP,rx_sop_array);
  eop_mask_of_blocks : entity work.dec1fn_enable
   generic map (RX_BLOCKS)
   port map (rx_eop_block_pos,RX_EOP,rx_eop_array);

  -- data, sop and eop multiplexers
  data_mux : entity work.GEN_MUX
    generic map (TX_DATA_WIDTH,RX_BLOCKS)
    port map (RX_DATA,sel,TX_DATA);
  sop_mux : entity work.GEN_MUX
    generic map (1,RX_BLOCKS)
    port map (rx_sop_array,sel,tx_sop_sig);
  eop_mux : entity work.GEN_MUX
    generic map (1,RX_BLOCKS)
    port map (rx_eop_array,sel,tx_eop_sig);

  -- output FLU signals connections
  TX_SOP        <= tx_sop_sig(0);
  TX_EOP        <= tx_eop_sig(0);
  TX_CHANNEL    <= RX_CHANNEL;     -- no need to use GEN_MUX because CHANNEL is valid only with SOP
  TX_HEADER     <= RX_HEADER;      -- no need to use GEN_MUX because HEADER is valid only with SOP
  real_tx_sop_pos_gen : if TX_SOP_POS_WIDTH>0 generate
    TX_SOP_POS    <= rx_sop_pos_augment(TX_SOP_POS_WIDTH downto 1);
  end generate;
  fake_tx_sop_pos_gen : if TX_SOP_POS_WIDTH=0 generate
    TX_SOP_POS    <= "0";
  end generate;
  TX_EOP_POS    <= RX_EOP_POS(log2(TX_DATA_WIDTH/8)-1 downto 0);
  TX_SRC_RDY    <= RX_SRC_RDY;
  RX_DST_RDY    <= word_cleared;

  -- registers to remember if we are inside or outside of packets
  inside_packet_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        in_packet_reg <= '0';
      elsif RX_SRC_RDY='1' and TX_DST_RDY='1' then
        in_packet_reg <= in_packet_reg_new;
      end if;
    end if;
  end process;
  inside_packet_word_border_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        in_packet_border_reg <= '0';
      elsif RX_SRC_RDY='1' and word_cleared='1' then
        in_packet_border_reg <= in_packet_reg_new;
      end if;
    end if;
  end process;
  in_packet_reg_new <= in_packet_reg xor tx_sop_sig(0) xor tx_eop_sig(0);

  -- position (block) inside RX word counter
  subwords_counter : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RX_SRC_RDY='1' and TX_DST_RDY='1' then
        cnt <= sel+1;
      end if;
    end if;
  end process;
  sel               <= cnt when in_packet_reg='1' else rx_sop_block_pos;
  cnt_will_overflow <= '1' when sel=(sel'length-1 downto 0 => '1') else '0';

  -- actual RX data word sent whole to TX
  word_cleared <= ((tx_eop_sig(0) and (not RX_SOP or not in_packet_border_reg)) or cnt_will_overflow) and TX_DST_RDY;
end architecture;
