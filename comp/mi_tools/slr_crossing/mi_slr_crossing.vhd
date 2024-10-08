-- mi_slr_crossing.vhd: Memory interface SLR Crossing
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

entity MI_SLR_CROSSING is
  generic(
    DATA_WIDTH     : integer := 32;
    ADDR_WIDTH     : integer := 32;
    META_WIDTH     : integer := 2;
    USE_OUTREG     : boolean:= true;
    FAKE_CROSSING  : boolean:= false;
    DEVICE         : string := "7SERIES"
  );
  port(
    CLK         : in std_logic;

    IN_RESET    : in  std_logic;
    IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    IN_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
    IN_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
    IN_RD       : in  std_logic;
    IN_WR       : in  std_logic;
    IN_ARDY     : out std_logic;
    IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    IN_DRDY     : out std_logic;

    OUT_RESET   : in  std_logic;
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



architecture arch of MI_SLR_CROSSING is
  constant REQ_DATA_WIDTH     : integer := META_WIDTH + DATA_WIDTH + ADDR_WIDTH + DATA_WIDTH/8 + 2;
  constant RESP_DATA_WIDTH    : integer := DATA_WIDTH + 1;
  signal req_crossing_data    : std_logic_vector(REQ_DATA_WIDTH-1 downto 0);
  signal req_crossing_dst_rdy : std_logic;
  signal resp_crossing_data   : std_logic_vector(RESP_DATA_WIDTH-1 downto 0);
begin
  full_architecture_gen : if not FAKE_CROSSING generate
    source_endpoint : entity work.MI_SLR_CROSSING_SRC
      generic map (
        DATA_WIDTH => DATA_WIDTH,
        ADDR_WIDTH => ADDR_WIDTH,
        META_WIDTH => META_WIDTH
      ) port map (
        CLK                  => CLK,
        RESET                => IN_RESET,
        IN_DWR               => IN_DWR,
        IN_MWR               => IN_MWR,
        IN_ADDR              => IN_ADDR,
        IN_BE                => IN_BE,
        IN_RD                => IN_RD,
        IN_WR                => IN_WR,
        IN_ARDY              => IN_ARDY,
        IN_DRD               => IN_DRD,
        IN_DRDY              => IN_DRDY,
        REQ_CROSSING_DATA    => req_crossing_data,
        REQ_CROSSING_DST_RDY => req_crossing_dst_rdy,
        RESP_CROSSING_DATA   => resp_crossing_data
      );

    destination_endpoint : entity work.MI_SLR_CROSSING_DST
      generic map (
        DATA_WIDTH => DATA_WIDTH,
        ADDR_WIDTH => ADDR_WIDTH,
        META_WIDTH => META_WIDTH,
        USE_OUTREG => USE_OUTREG,
        DEVICE     => DEVICE
      ) port map (
        CLK                  => CLK,
        RESET                => OUT_RESET,
        REQ_CROSSING_DATA    => req_crossing_data,
        REQ_CROSSING_DST_RDY => req_crossing_dst_rdy,
        RESP_CROSSING_DATA   => resp_crossing_data,
        OUT_DWR              => OUT_DWR,
        OUT_MWR              => OUT_MWR,
        OUT_ADDR             => OUT_ADDR,
        OUT_BE               => OUT_BE,
        OUT_RD               => OUT_RD,
        OUT_WR               => OUT_WR,
        OUT_ARDY             => OUT_ARDY,
        OUT_DRD              => OUT_DRD,
        OUT_DRDY             => OUT_DRDY
      );
  end generate;

  fake_architecture_gen : if FAKE_CROSSING generate
    OUT_DWR     <= IN_DWR;
    OUT_MWR     <= IN_MWR;
    OUT_ADDR    <= IN_ADDR;
    OUT_BE      <= IN_BE;
    OUT_RD      <= IN_RD;
    OUT_WR      <= IN_WR;
    IN_ARDY     <= OUT_ARDY;
    IN_DRD      <= OUT_DRD;
    IN_DRDY     <= OUT_DRDY;
  end generate;
end architecture;

