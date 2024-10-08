-- mi_slr_crossing_dst.vhd: Memory interface SLR Crossing - destination part.
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

entity MI_SLR_CROSSING_DST is
  generic(
    DATA_WIDTH     : integer := 32;
    ADDR_WIDTH     : integer := 32;
    META_WIDTH     : integer := 2;
    USE_OUTREG     : boolean := true;
    DEVICE         : string := "7SERIES"
  );
  port(
    CLK              : in std_logic;
    RESET            : in std_logic;
    REQ_CROSSING_DATA    : in  std_logic_vector(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+2-1 downto 0);
    REQ_CROSSING_DST_RDY : out std_logic;
    RESP_CROSSING_DATA   : out std_logic_vector(DATA_WIDTH+1-1 downto 0);
    OUT_DWR     : out std_logic_vector(DATA_WIDTH-1 downto 0);
    OUT_MWR     : out std_logic_vector(META_WIDTH-1 downto 0);
    OUT_ADDR    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    OUT_BE      : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
    OUT_RD      : out std_logic;
    OUT_WR      : out std_logic;
    OUT_ARDY    : in  std_logic;
    OUT_DRD     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    OUT_DRDY    : in  std_logic
  );
end entity;

architecture full of MI_SLR_CROSSING_DST is
  signal out_data    : std_logic_vector(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1-1 downto 0);
  signal out_src_rdy : std_logic;
  signal out_dst_rdy : std_logic;
begin
  OUT_MWR     <= out_data(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1-1 downto DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1);
  OUT_DWR     <= out_data(DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1-1 downto ADDR_WIDTH+DATA_WIDTH/8+1);
  OUT_ADDR    <= out_data(ADDR_WIDTH+DATA_WIDTH/8+1-1 downto DATA_WIDTH/8+1);
  OUT_BE      <= out_data(DATA_WIDTH/8+1-1 downto 1);
  OUT_RD      <= out_data(0)     and out_src_rdy;
  OUT_WR      <= not out_data(0) and out_src_rdy;
  out_dst_rdy <= OUT_ARDY;

  req_destination_endpoint : entity work.SLR_CROSSING_DST
    generic map (
      DATA_WIDTH => META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1,
      USE_OUTREG => USE_OUTREG,
      DEVICE => DEVICE
    ) port map (
      CLK              => CLK,
      RESET            => RESET,
      CROSSING_DATA    => REQ_CROSSING_DATA,
      CROSSING_DST_RDY => REQ_CROSSING_DST_RDY,
      OUT_DATA         => out_data,
      OUT_SRC_RDY      => out_src_rdy,
      OUT_DST_RDY      => out_dst_rdy
    );

  resp_source_endpoint : entity work.SLR_CROSSING_DATA_ONLY_SRC
    generic map (
      DATA_WIDTH  => DATA_WIDTH
    ) port map (
      CLK              => CLK,
      RESET            => RESET,
      IN_DATA          => OUT_DRD,
      IN_SRC_RDY       => OUT_DRDY,
      CROSSING_DATA    => RESP_CROSSING_DATA
    );
end architecture;
