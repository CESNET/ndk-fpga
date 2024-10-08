-- slr_crossing.vhd: FrameLink SLR Crossing
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

entity FL_SLR_CROSSING is
  generic(
    DATA_WIDTH     : integer:= 64;
    USE_OUTREG     : boolean:= false;
    FAKE_CROSSING  : boolean:= false
  );
  port(
    CLK            : in std_logic;

    RX_RESET       : in  std_logic;
    RX_SOF_N       : in  std_logic;
    RX_SOP_N       : in  std_logic;
    RX_EOP_N       : in  std_logic;
    RX_EOF_N       : in  std_logic;
    RX_SRC_RDY_N   : in  std_logic;
    RX_DST_RDY_N   : out std_logic;
    RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_DREM        : in  std_logic_vector(max(0,log2(DATA_WIDTH/8)-1) downto 0);

    TX_RESET       : in  std_logic;
    TX_SOF_N       : out std_logic;
    TX_EOP_N       : out std_logic;
    TX_SOP_N       : out std_logic;
    TX_EOF_N       : out std_logic;
    TX_SRC_RDY_N   : out std_logic;
    TX_DST_RDY_N   : in  std_logic;
    TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_DREM        : out std_logic_vector(max(0,log2(DATA_WIDTH/8)-1) downto 0)
  );
end entity;



architecture arch of FL_SLR_CROSSING is
  constant DREM_WIDTH        : integer := max(1,log2(DATA_WIDTH/8));
  constant CROSSING_WIDTH    : integer := DATA_WIDTH+DREM_WIDTH+4;
  signal crossing_in_data        : std_logic_vector(CROSSING_WIDTH-1 downto 0);
  signal crossing_in_src_rdy     : std_logic;
  signal crossing_in_dst_rdy     : std_logic;
  signal crossing_out_data       : std_logic_vector(CROSSING_WIDTH-1 downto 0);
  signal crossing_out_src_rdy    : std_logic;
  signal crossing_out_dst_rdy    : std_logic;
begin
  crossing_in_data     <= RX_SOF_N & RX_SOP_N & RX_EOP_N & RX_EOF_N & RX_DREM & RX_DATA;
  crossing_in_src_rdy  <= not RX_SRC_RDY_N;
  RX_DST_RDY_N         <= not crossing_in_dst_rdy;

  TX_SOF_N             <= crossing_out_data(DATA_WIDTH+DREM_WIDTH+3);
  TX_SOP_N             <= crossing_out_data(DATA_WIDTH+DREM_WIDTH+2);
  TX_EOP_N             <= crossing_out_data(DATA_WIDTH+DREM_WIDTH+1);
  TX_EOF_N             <= crossing_out_data(DATA_WIDTH+DREM_WIDTH+0);
  TX_DATA              <= crossing_out_data(DATA_WIDTH-1 downto 0);
  TX_DREM              <= crossing_out_data(DATA_WIDTH+DREM_WIDTH-1 downto DATA_WIDTH);
  TX_SRC_RDY_N         <= not crossing_out_src_rdy;
  crossing_out_dst_rdy <= not TX_DST_RDY_N;

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

