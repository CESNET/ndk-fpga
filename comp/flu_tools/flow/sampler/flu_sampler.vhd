-- flu_sampler.vhd: Full architecture of FLU_SAMPLER unit.
-- Copyright (C) 2012 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: FLU SAMPLER
-- ----------------------------------------------------------------------------
entity FLU_SAMPLER is
    generic(
       DATA_WIDTH    :   integer:=256;
       SOP_POS_WIDTH :   integer:=2;
       MAX_RATE      :   integer:=16 -- Maximum Rate 1:N
   );
   port(
      -- common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Sampling RATE 1:N
      RATE           : in std_logic_vector(log2(MAX_RATE)- 1 downto 0);
      -- Discarded packet? (1 = yes, 0 = no)
      PCKT_DISCARD   : out std_logic;

      -- Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Frame Link Unaligned output interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity FLU_SAMPLER;

-- ----------------------------------------------------------------------------
--  Architecture: FLU SAMPLER
-- ----------------------------------------------------------------------------
architecture full of FLU_SAMPLER is

constant EOP_POS_WIDTH     : integer :=log2(DATA_WIDTH/8);
signal cnt_packet          : std_logic_vector(log2(MAX_RATE)-1 downto 0);
signal sig_rx_dst_rdy      : std_logic;
signal rx_sop_detect       : std_logic;
signal rx_eop_detect       : std_logic;
signal rx_sop_detect_weak  : std_logic;
signal rx_eop_detect_weak  : std_logic;
signal rx_sop_pos_augment  : std_logic_vector(EOP_POS_WIDTH-1 downto 0);
signal discard             : std_logic;
signal discard_eop         : std_logic;
signal discard_sop         : std_logic;
signal discard_src         : std_logic;
signal discard_reg         : std_logic;

begin
   rx_sop_detect      <= RX_SOP and RX_SRC_RDY and sig_rx_dst_rdy; -- valid SOP on RX interface
   rx_eop_detect      <= RX_EOP and RX_SRC_RDY and sig_rx_dst_rdy; -- valid EOP on RX interface
   rx_sop_detect_weak <= RX_SOP and RX_SRC_RDY; -- valid SOP on RX interface (weak)
   rx_eop_detect_weak <= RX_EOP and RX_SRC_RDY; -- valid EOP on RX interface (weak)
   discard_sop        <= discard; -- block active SOP signal
   discard_eop        <= discard_reg when (rx_sop_pos_augment > RX_EOP_POS) else discard; -- block active EOP signal
   discard_src        <= discard_reg and discard when (rx_eop_detect_weak='1' and rx_sop_pos_augment > RX_EOP_POS) else discard;
   sig_rx_dst_rdy     <= TX_DST_RDY or discard_src;
   discard            <= '0' when (rx_sop_detect_weak='1') and (cnt_packet=(log2(MAX_RATE)-1 downto 0 => '0'))  else
                         '1' when (rx_sop_detect_weak='1') and (cnt_packet/=(log2(MAX_RATE)-1 downto 0 => '0')) else
                         discard_reg;

   process(CLK,RESET)
   begin
      if CLK'event and CLK='1' then
         if RESET='1' then
            discard_reg <= '0';
         elsif RX_SRC_RDY='1' and sig_rx_dst_rdy='1' then
            discard_reg <= discard;
         end if;
      end if;
   end process;

   rx_sop_pos_augment_gen : if EOP_POS_WIDTH>SOP_POS_WIDTH generate
      rx_sop_pos_augment <= RX_SOP_POS & (EOP_POS_WIDTH-SOP_POS_WIDTH-1 downto 0 => '0');
   end generate;
   rx_sop_pos_augment_fake_gen : if EOP_POS_WIDTH=SOP_POS_WIDTH generate
      rx_sop_pos_augment <= RX_SOP_POS;
   end generate;

   -- Passed packet counter
   cnt_packetp: process(RESET, CLK)
   begin
     if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_packet <= (others => '0');
         elsif (rx_sop_detect='1') then
            if (cnt_packet >= RATE) then
               cnt_packet <= (others => '0');
            else
               cnt_packet <= cnt_packet + 1 ;
            end if;
         end if;
      end if;
   end process;

   -- Maping output ports
   TX_DATA       <= RX_DATA;
   TX_SOP_POS    <= RX_SOP_POS;
   TX_EOP_POS    <= RX_EOP_POS;
   TX_SOP        <= RX_SOP and not discard_sop;
   TX_EOP        <= RX_EOP and not discard_eop;
   TX_SRC_RDY    <= RX_SRC_RDY and not discard_src;
   RX_DST_RDY    <= sig_rx_dst_rdy;

   PCKT_DISCARD  <= rx_eop_detect and discard_eop; -- discarded valid EOP == discarded packet

end architecture full;
