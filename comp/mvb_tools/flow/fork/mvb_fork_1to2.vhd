-- mvb_fork_1to2.vhd: Fork wrapper for two output ports
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;



entity MVB_FORK_1TO2 is
  generic(
    ITEMS          : integer := 4; -- any possitive value
    ITEM_WIDTH     : integer := 8; -- any possitive value
    USE_DST_RDY    : boolean := true;
    VERSION        : string := "logic"
      -- Do not care when USE_DST_RDY is false.
      -- "logic"    - Fork waits with each word for all TX ports to set DST_RDY in the same cycle. Pure logic implementation.
      -- "register" - Fork can send each word independently to each TX port as soon as they are ready. Registers are used to store some flags, but logic functions are simpler for larger forks.
      -- "simple"   - Same behaviour as "logic", but using simpler logic on SRC_RDY and DST_RDY with a potencial of logic loop creation. USE WITH CARE!
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_VLD        : in std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    TX0_DATA      : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX0_VLD       : out std_logic_vector(ITEMS-1 downto 0);
    TX0_SRC_RDY   : out std_logic;
    TX0_DST_RDY   : in std_logic;

    TX1_DATA      : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX1_VLD       : out std_logic_vector(ITEMS-1 downto 0);
    TX1_SRC_RDY   : out std_logic;
    TX1_DST_RDY   : in std_logic
  );
end entity;



architecture arch of MVB_FORK_1TO2 is

  constant OUTPUT_PORTS : integer := 2;
  signal tx_data       : std_logic_vector(OUTPUT_PORTS*ITEMS*ITEM_WIDTH-1 downto 0);
  signal tx_vld        : std_logic_vector(OUTPUT_PORTS*ITEMS-1 downto 0);
  signal tx_src_rdy    : std_logic_vector(OUTPUT_PORTS-1 downto 0);
  signal tx_dst_rdy    : std_logic_vector(OUTPUT_PORTS-1 downto 0);

begin

  core: entity work.MVB_FORK
  generic map (
    OUTPUT_PORTS    => OUTPUT_PORTS,
    ITEMS           => ITEMS,
    ITEM_WIDTH      => ITEM_WIDTH,
    USE_DST_RDY     => USE_DST_RDY,
    VERSION         => VERSION
  ) port map (
    CLK             => CLK,
    RESET           => RESET,
    RX_DATA         => RX_DATA,
    RX_VLD          => RX_VLD,
    RX_SRC_RDY      => RX_SRC_RDY,
    RX_DST_RDY      => RX_DST_RDY,
    TX_DATA         => tx_data,
    TX_VLD          => tx_vld,
    TX_SRC_RDY      => tx_src_rdy,
    TX_DST_RDY      => tx_dst_rdy
  );

  TX0_DATA      <= tx_data(1*ITEMS*ITEM_WIDTH-1 downto 0*ITEMS*ITEM_WIDTH);
  TX0_VLD       <= tx_vld(1*ITEMS-1 downto 0*ITEMS);
  TX0_SRC_RDY   <= tx_src_rdy(0);
  tx_dst_rdy(0) <= TX0_DST_RDY;

  TX1_DATA      <= tx_data(2*ITEMS*ITEM_WIDTH-1 downto 1*ITEMS*ITEM_WIDTH);
  TX1_VLD       <= tx_vld(2*ITEMS-1 downto 1*ITEMS);
  TX1_SRC_RDY   <= tx_src_rdy(1);
  tx_dst_rdy(1) <= TX1_DST_RDY;

end architecture;
