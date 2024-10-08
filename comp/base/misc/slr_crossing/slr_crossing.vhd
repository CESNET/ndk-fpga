-- slr_crossing.vhd: Special pipe component to cross between super logic regions (slow wire).
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity SLR_CROSSING is
  generic(
    DATA_WIDTH      : integer := 64;
    USE_OUTREG      : boolean := true;
    FAKE_CROSSING   : boolean := false;  -- wires only (to disable crossing easily)
    DEVICE          : string := "7SERIES"
  );
  port(
    CLK            : in std_logic;
    IN_RESET       : in std_logic;
    IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    IN_SRC_RDY     : in  std_logic;
    IN_DST_RDY     : out std_logic;
    OUT_RESET      : in  std_logic;
    OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    OUT_SRC_RDY    : out std_logic;
    OUT_DST_RDY    : in  std_logic
  );
end entity;



library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

architecture full of SLR_CROSSING is
  signal crossing_data    : std_logic_vector(DATA_WIDTH downto 0);
  signal crossing_dst_rdy : std_logic;
begin
  full_architecture_gen : if not FAKE_CROSSING generate
    source_endpoint : entity work.SLR_CROSSING_SRC
      generic map (
        DATA_WIDTH  => DATA_WIDTH
      ) port map (
        CLK              => CLK,
        RESET            => IN_RESET,
        IN_DATA          => IN_DATA,
        IN_SRC_RDY       => IN_SRC_RDY,
        IN_DST_RDY       => IN_DST_RDY,
        CROSSING_DATA    => crossing_data,
        CROSSING_DST_RDY => crossing_dst_rdy
      );

    destination_endpoint : entity work.SLR_CROSSING_DST
      generic map (
        DATA_WIDTH => DATA_WIDTH,
        USE_OUTREG => USE_OUTREG,
        DEVICE     => DEVICE
      ) port map (
        CLK              => CLK,
        RESET            => OUT_RESET,
        CROSSING_DATA    => crossing_data,
        CROSSING_DST_RDY => crossing_dst_rdy,
        OUT_DATA         => OUT_DATA,
        OUT_SRC_RDY      => OUT_SRC_RDY,
        OUT_DST_RDY      => OUT_DST_RDY
      );
  end generate;

  fake_architecture_gen : if FAKE_CROSSING generate
    OUT_DATA    <= IN_DATA;
    OUT_SRC_RDY <= IN_SRC_RDY;
    IN_DST_RDY  <= OUT_DST_RDY;
  end generate;
end architecture;
