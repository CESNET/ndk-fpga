-- top_ver.vhd
--!
--! \file
--! \brief Verification wrapper of DUT
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;

entity TOP_VER is
  port(
    CLK            : in  std_logic;
    RESET          : in  std_logic;
    MI_DWR         : in  std_logic_vector(31 downto 0);
    MI_ADDR        : in  std_logic_vector(31 downto 0);
    MI_RD          : in  std_logic;
    MI_WR          : in  std_logic;
    MI_BE          : in  std_logic_vector(3 downto 0);
    MI_DRD         : out std_logic_vector(31 downto 0);
    MI_ARDY        : out std_logic;
    MI_DRDY        : out std_logic
  );
end entity;



library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

architecture full of TOP_VER is

  -- EDIT THIS -----------------------------------------------------------------
  -- Change DATA_WIDTH and add your own signals based on dumped data.
  constant DATA_WIDTH    : integer:= 13;
  signal sop_pos : std_logic_vector(3-1 downto 0);
  signal eop_pos : std_logic_vector(6-1 downto 0);
  signal sop, eop, src_rdy, dst_rdy : std_logic;
  -- ---------------------------------------------------------------------------

  signal replay_data : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal replay_valid : std_logic;
  constant STORAGE_ITEMS : integer:= 65536;

begin
  dut: entity work.busreplay
  generic map (
    DATA_WIDTH    => DATA_WIDTH,
    STORAGE_ITEMS => STORAGE_ITEMS
  ) port map (
    CLK            => CLK,
    RESET          => RESET,
    OUT_DATA       => replay_data,
    OUT_VLD        => replay_valid,
    MI_DWR         => MI_DWR,
    MI_ADDR        => MI_ADDR,
    MI_RD          => MI_RD,
    MI_WR          => MI_WR,
    MI_BE          => MI_BE,
    MI_DRD         => MI_DRD,
    MI_ARDY        => MI_ARDY,
    MI_DRDY        => MI_DRDY
  );

  -- EDIT THIS -----------------------------------------------------------------
  -- Slice and assign replay data to your signals.
  sop_pos <= replay_data(13-1 downto 10);
  eop_pos <= replay_data(10-1 downto 4);
  sop <= replay_data(3);
  eop <= replay_data(2);
  src_rdy <= replay_data(1);
  dst_rdy <= replay_data(0);
  -- ---------------------------------------------------------------------------

end architecture;
