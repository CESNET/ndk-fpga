-- mi_slr_crossing_src.vhd: Memory interface SLR Crossing - source part.
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

entity MI_SLR_CROSSING_SRC is
  generic(
    DATA_WIDTH     : integer := 32;
    ADDR_WIDTH     : integer := 32;
    META_WIDTH     : integer := 2
  );
  port(
    CLK              : in std_logic;
    RESET            : in std_logic;
    IN_DWR           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    IN_MWR           : in  std_logic_vector(META_WIDTH-1 downto 0);
    IN_ADDR          : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    IN_BE            : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
    IN_RD            : in  std_logic;
    IN_WR            : in  std_logic;
    IN_ARDY          : out std_logic;
    IN_DRD           : out std_logic_vector(DATA_WIDTH-1 downto 0);
    IN_DRDY          : out std_logic;
    REQ_CROSSING_DATA    : out std_logic_vector(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+2-1 downto 0);
    REQ_CROSSING_DST_RDY : in  std_logic;
    RESP_CROSSING_DATA   : in  std_logic_vector(DATA_WIDTH+1-1 downto 0)
  );
end entity;

architecture full of MI_SLR_CROSSING_SRC is
  signal in_data    : std_logic_vector(META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1-1 downto 0);
  signal in_src_rdy : std_logic;
  signal in_dst_rdy : std_logic;
begin
  in_data    <= IN_MWR & IN_DWR & IN_ADDR & IN_BE & IN_RD;
  in_src_rdy <= IN_RD or IN_WR;
  IN_ARDY    <= in_dst_rdy;

  req_source_endpoint : entity work.SLR_CROSSING_SRC
    generic map (
      DATA_WIDTH  => META_WIDTH+DATA_WIDTH+ADDR_WIDTH+DATA_WIDTH/8+1
    ) port map (
      CLK              => CLK,
      RESET            => RESET,
      IN_DATA          => in_data,
      IN_SRC_RDY       => in_src_rdy,
      IN_DST_RDY       => in_dst_rdy,
      CROSSING_DATA    => REQ_CROSSING_DATA,
      CROSSING_DST_RDY => REQ_CROSSING_DST_RDY
    );

  resp_destination_endpoint : entity work.SLR_CROSSING_DATA_ONLY_DST
    generic map (
      DATA_WIDTH => DATA_WIDTH
    ) port map (
      CLK              => CLK,
      RESET            => RESET,
      CROSSING_DATA    => RESP_CROSSING_DATA,
      OUT_DATA         => IN_DRD,
      OUT_SRC_RDY      => IN_DRDY
    );
end architecture;
