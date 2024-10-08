-- mfb_fork_1to2.vhd: Fork wrapper for two output ports
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;



entity MFB_FORK_1TO2 is
  generic(
    -- =============================
    -- BUS characteristics
    --
    -- Frame size restrictions: none
    -- =============================

    -- any possitive value
    REGIONS        : integer := 4;
    -- any possitive value
    REGION_SIZE    : integer := 8;
    -- any possitive value
    BLOCK_SIZE     : integer := 8;
    -- any possitive value
    ITEM_WIDTH     : integer := 8;
    -- any possitive value
    META_WIDTH     : integer := 0;

    -- =============================
    -- Others
    -- =============================

    USE_DST_RDY    : boolean := true;
    -- Do not care when USE_DST_RDY is false.
    -- "logic"    - Fork waits with each word for all TX ports to set DST_RDY in the same cycle. Pure logic implementation.
    -- "register" - Fork can send each word independently to each TX port as soon as they are ready. Registers are used to store some flags, but logic functions are simpler for larger forks.
    -- "simple"   - Same behaviour as "logic", but using simpler logic on SRC_RDY and DST_RDY with a potencial of logic loop creation. USE WITH CARE!
    VERSION        : string := "logic"
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_META       : in std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
    RX_SOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    RX_EOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_SOF        : in std_logic_vector(REGIONS-1 downto 0);
    RX_EOF        : in std_logic_vector(REGIONS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    TX0_DATA      : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX0_META      : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    TX0_SOF_POS   : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX0_EOF_POS   : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX0_SOF       : out std_logic_vector(REGIONS-1 downto 0);
    TX0_EOF       : out std_logic_vector(REGIONS-1 downto 0);
    TX0_SRC_RDY   : out std_logic;
    TX0_DST_RDY   : in std_logic;

    TX1_DATA      : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX1_META      : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    TX1_SOF_POS   : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX1_EOF_POS   : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX1_SOF       : out std_logic_vector(REGIONS-1 downto 0);
    TX1_EOF       : out std_logic_vector(REGIONS-1 downto 0);
    TX1_SRC_RDY   : out std_logic;
    TX1_DST_RDY   : in std_logic
  );
end entity;



architecture arch of MFB_FORK_1TO2 is

  constant OUTPUT_PORTS : integer := 2;
  signal tx_data       : std_logic_vector(OUTPUT_PORTS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
  signal tx_meta       : std_logic_vector(OUTPUT_PORTS*REGIONS*META_WIDTH-1 downto 0);
  signal tx_sof_pos    : std_logic_vector(OUTPUT_PORTS*REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
  signal tx_eof_pos    : std_logic_vector(OUTPUT_PORTS*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
  signal tx_sof        : std_logic_vector(OUTPUT_PORTS*REGIONS-1 downto 0);
  signal tx_eof        : std_logic_vector(OUTPUT_PORTS*REGIONS-1 downto 0);
  signal tx_src_rdy    : std_logic_vector(OUTPUT_PORTS-1 downto 0);
  signal tx_dst_rdy    : std_logic_vector(OUTPUT_PORTS-1 downto 0);

begin

  core: entity work.MFB_FORK
  generic map (
    OUTPUT_PORTS    => OUTPUT_PORTS,
    REGIONS         => REGIONS,
    REGION_SIZE     => REGION_SIZE,
    BLOCK_SIZE      => BLOCK_SIZE,
    ITEM_WIDTH      => ITEM_WIDTH,
    META_WIDTH      => META_WIDTH,
    USE_DST_RDY     => USE_DST_RDY,
    VERSION         => VERSION
  ) port map (
    CLK             => CLK,
    RESET           => RESET,
    RX_DATA         => RX_DATA,
    RX_META         => RX_META,
    RX_SOF_POS      => RX_SOF_POS,
    RX_EOF_POS      => RX_EOF_POS,
    RX_SOF          => RX_SOF,
    RX_EOF          => RX_EOF,
    RX_SRC_RDY      => RX_SRC_RDY,
    RX_DST_RDY      => RX_DST_RDY,
    TX_DATA         => tx_data,
    TX_META         => tx_meta,
    TX_SOF_POS      => tx_sof_pos,
    TX_EOF_POS      => tx_eof_pos,
    TX_SOF          => tx_sof,
    TX_EOF          => tx_eof,
    TX_SRC_RDY      => tx_src_rdy,
    TX_DST_RDY      => tx_dst_rdy
  );

  TX0_DATA      <= tx_data(1*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH);
  TX0_META      <= tx_meta(1*REGIONS*META_WIDTH-1 downto 0*REGIONS*META_WIDTH);
  TX0_SOF_POS   <= tx_sof_pos(1*REGIONS*max(1,log2(REGION_SIZE))-1 downto 0*REGIONS*max(1,log2(REGION_SIZE)));
  TX0_EOF_POS   <= tx_eof_pos(1*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE)));
  TX0_SOF       <= tx_sof(1*REGIONS-1 downto 0*REGIONS);
  TX0_EOF       <= tx_eof(1*REGIONS-1 downto 0*REGIONS);
  TX0_SRC_RDY   <= tx_src_rdy(0);
  tx_dst_rdy(0) <= TX0_DST_RDY;

  TX1_DATA      <= tx_data(2*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 1*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH);
  TX1_META      <= tx_meta(2*REGIONS*META_WIDTH-1 downto 1*REGIONS*META_WIDTH);
  TX1_SOF_POS   <= tx_sof_pos(2*REGIONS*max(1,log2(REGION_SIZE))-1 downto 1*REGIONS*max(1,log2(REGION_SIZE)));
  TX1_EOF_POS   <= tx_eof_pos(2*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 1*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE)));
  TX1_SOF       <= tx_sof(2*REGIONS-1 downto 1*REGIONS);
  TX1_EOF       <= tx_eof(2*REGIONS-1 downto 1*REGIONS);
  TX1_SRC_RDY   <= tx_src_rdy(1);
  tx_dst_rdy(1) <= TX1_DST_RDY;

end architecture;
