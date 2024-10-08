--
-- flu_demultiplexer.vhd: Demultiplexer for Frame Link Unaligned (not packet oriented!)
-- Copyright (C) 2014 CESNET
-- Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
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
entity FLU_DEMULTIPLEXER is
   generic(
       DATA_WIDTH    : integer :=512;
       SOP_POS_WIDTH : integer :=3;
       INPUT_PORTS   : integer :=2
   );
   port(
       -- Common interface
      RST           : in  std_logic;
      CLK           : in  std_logic;

      SEL           : in std_logic_vector(log2(INPUT_PORTS)-1 downto 0);

      -- Frame Link Unaligned input interfaces
      RX_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in  std_logic;
      RX_EOP        : in  std_logic;
      RX_SRC_RDY    : in  std_logic;
      RX_DST_RDY    : out std_logic;

      -- Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic_vector(INPUT_PORTS-1 downto 0);
      TX_EOP        : out std_logic_vector(INPUT_PORTS-1 downto 0);
      TX_SRC_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);
      TX_DST_RDY    : in  std_logic_vector(INPUT_PORTS-1 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH of FLU_DEMULTIPLEXER is
   constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);
begin
   data_mx_i : entity work.GEN_DEMUX
   generic map (
      DATA_WIDTH  => DATA_WIDTH,
      DEMUX_WIDTH => INPUT_PORTS,
      DEF_VALUE   => 'X'
   ) port map (
      DATA_IN     => RX_DATA,
      SEL         => SEL,
      DATA_OUT    => TX_DATA
   );

   sop_pos_mx_i : entity work.GEN_DEMUX
   generic map (
      DATA_WIDTH  => SOP_POS_WIDTH,
      DEMUX_WIDTH => INPUT_PORTS,
      DEF_VALUE   => 'X'
   ) port map (
      DATA_IN     => RX_SOP_POS,
      SEL         => SEL,
      DATA_OUT    => TX_SOP_POS
   );

   eop_pos_mx_i : entity work.GEN_DEMUX
   generic map (
      DATA_WIDTH  => EOP_POS_WIDTH,
      DEMUX_WIDTH => INPUT_PORTS,
      DEF_VALUE   => 'X'
   ) port map (
      DATA_IN     => RX_EOP_POS,
      SEL         => SEL,
      DATA_OUT    => TX_EOP_POS
   );

   sop_mx_i : entity work.GEN_DEMUX
   generic map (
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => INPUT_PORTS,
      DEF_VALUE   => 'X'
   ) port map (
      DATA_IN(0)  => RX_SOP,
      SEL         => SEL,
      DATA_OUT    => TX_SOP
   );

   eop_mx_i : entity work.GEN_DEMUX
   generic map (
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => INPUT_PORTS,
      DEF_VALUE   => 'X'
   ) port map (
      DATA_IN(0)  => RX_EOP,
      SEL         => SEL,
      DATA_OUT    => TX_EOP
   );

   src_rdy_mx_i : entity work.GEN_DEMUX
   generic map (
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => INPUT_PORTS,
      DEF_VALUE   => '0'
   ) port map (
      DATA_IN(0)  => RX_SRC_RDY,
      SEL         => SEL,
      DATA_OUT    => TX_SRC_RDY
   );

   dst_rdy_mx_i : entity work.GEN_MUX
   generic map (
      DATA_WIDTH  => 1,
      MUX_WIDTH   => INPUT_PORTS
   ) port map (
      DATA_IN     => TX_DST_RDY,
      SEL         => SEL,
      DATA_OUT(0) => RX_DST_RDY
   );
end architecture;
