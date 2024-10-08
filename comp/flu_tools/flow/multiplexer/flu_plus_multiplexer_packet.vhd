--
-- flu_plus_multiplexer_packet.vhd: Multiplexer for Frame Link Unaligned Plus (packet oriented!)
-- Copyright (C) 2014 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU_PLUS_MULTIPLEXER_PACKET is
   generic(
       DATA_WIDTH     : integer := 256;
       SOP_POS_WIDTH  : integer := 2;
       INPUT_PORTS    : integer := 2;
       -- is multiplexer blocking or not
         -- when TRUE:  not selected ports are blocked
         -- when FALSE: not selected ports discard packets at the same rate as selected one forwarding
         --             something like exclusive packet selection
       BLOCKING       : boolean := true;
       CHANNEL_WIDTH  : integer:= 3
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      SEL            : in std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
      SEL_READY      : in std_logic;
      SEL_NEXT       : out std_logic;

      -- Frame Link Unaligned input interfaces
      RX_DATA       : in std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
      RX_CHANNEL    : in std_logic_vector(INPUT_PORTS*CHANNEL_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_EOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
      RX_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);

      -- Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_CHANNEL    : out std_logic_vector(CHANNEL_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH of FLU_PLUS_MULTIPLEXER_PACKET is
begin
   -- basic packet MUX connection
   basic_mx_i : entity work.FLU_MULTIPLEXER_PACKET
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      INPUT_PORTS    => INPUT_PORTS,
      BLOCKING       => BLOCKING
   ) port map (
      RESET     => RESET,
      CLK       => CLK,
      SEL       => SEL,
      SEL_READY => SEL_READY,
      SEL_NEXT  => SEL_NEXT,

      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,

      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY
   );

   channel_mx_i : entity work.GEN_MUX
   generic map (
      DATA_WIDTH  => CHANNEL_WIDTH,
      MUX_WIDTH   => INPUT_PORTS
   ) port map (
      DATA_IN     => RX_CHANNEL,
      SEL         => SEL,
      DATA_OUT    => TX_CHANNEL
   );

end architecture;
