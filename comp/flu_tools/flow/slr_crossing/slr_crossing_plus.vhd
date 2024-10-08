-- slr_crossing_plus.vhd: FrameLinkUnalignedPlus SLR Crossing
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity FLU_SLR_CROSSING_PLUS is
  generic(
    DATA_WIDTH     : integer:= 256;
    SOP_POS_WIDTH  : integer:= 2;
    USE_OUTREG     : boolean:= true;
    FAKE_CROSSING  : boolean:= false;
    CHANNEL_WIDTH  : integer:= 3
  );
  port(
    CLK            : in std_logic;

    RX_RESET      : in  std_logic;
    RX_CHANNEL    : in std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    RX_EOP_POS    : in std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
    RX_SOP        : in std_logic;
    RX_EOP        : in std_logic;
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    TX_RESET      : in  std_logic;
    TX_CHANNEL    : out std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    TX_EOP_POS    : out std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
    TX_SOP        : out std_logic;
    TX_EOP        : out std_logic;
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic
  );
end entity;



architecture arch of FLU_SLR_CROSSING_PLUS is
  constant EOP_POS_WIDTH         : integer := max(1,log2(DATA_WIDTH/8));
  constant CROSSING_WIDTH        : integer := CHANNEL_WIDTH+DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH+2;
  signal crossing_in_data        : std_logic_vector(CROSSING_WIDTH-1 downto 0);
  signal crossing_in_src_rdy     : std_logic;
  signal crossing_in_dst_rdy     : std_logic;
  signal crossing_out_data       : std_logic_vector(CROSSING_WIDTH-1 downto 0);
  signal crossing_out_src_rdy    : std_logic;
  signal crossing_out_dst_rdy    : std_logic;
begin
  crossing_in_data     <= RX_CHANNEL & RX_SOP & RX_EOP & RX_SOP_POS & RX_EOP_POS & RX_DATA;
  crossing_in_src_rdy  <= RX_SRC_RDY;
  RX_DST_RDY           <= crossing_in_dst_rdy;

  TX_CHANNEL           <= crossing_out_data(CROSSING_WIDTH-1 downto DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH+2);
  TX_SOP               <= crossing_out_data(DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH+1);
  TX_EOP               <= crossing_out_data(DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH+0);
  TX_DATA              <= crossing_out_data(DATA_WIDTH-1 downto 0);
  TX_SOP_POS           <= crossing_out_data(DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH-1 downto DATA_WIDTH+EOP_POS_WIDTH);
  TX_EOP_POS           <= crossing_out_data(DATA_WIDTH+EOP_POS_WIDTH-1 downto DATA_WIDTH);
  TX_SRC_RDY           <= crossing_out_src_rdy;
  crossing_out_dst_rdy <= TX_DST_RDY;

  SLR_CROSSING_I : entity work.SLR_CROSSING
  generic map(
    DATA_WIDTH      => CROSSING_WIDTH,
    USE_OUTREG      => USE_OUTREG,
    FAKE_CROSSING   => FAKE_CROSSING
  ) port map(
    CLK         => CLK,
    IN_RESET     => RX_RESET,
    IN_DATA      => crossing_in_data,
    IN_SRC_RDY   => crossing_in_src_rdy,
    IN_DST_RDY   => crossing_in_dst_rdy,
    OUT_RESET    => TX_RESET,
    OUT_DATA     => crossing_out_data,
    OUT_SRC_RDY  => crossing_out_src_rdy,
    OUT_DST_RDY  => crossing_out_dst_rdy
  );
end architecture;

