-- fifo_asbram_xilinx.vhd: Multi-Frame Bus wrapper of asynchronous FIFO implemented in Xilinx BRAMs
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;
use work.math_pack.all;

entity MFB_ASFIFO_BRAM_XILINX is
  generic(
    -- =============================
    -- MFB specification
    --
    -- Frame size restrictions: none
    -- =============================

    -- "VIRTEX6", "7SERIES", "ULTRASCALE"
    DEVICE                  : string := "7SERIES";
    -- any possitive value
    REGIONS                 : integer := 4;
    -- any possitive value
    REGION_SIZE             : integer := 8;
    -- any possitive value
    BLOCK_SIZE              : integer := 8;
    -- any possitive value
    ITEM_WIDTH              : integer := 8;
    -- 512, 1024, 2048, 4096, 8192 (less effective)
    ITEMS                   : integer := 512;

    -- ==================
    -- FIFO PARAMETERS
    -- ==================

    -- Almost Full/Empty offsets
    ALMOST_FULL_OFFSET      : integer := 128;
    ALMOST_EMPTY_OFFSET     : integer := 128;
    -- Precision of FULL signal (write interface) assertion.
    --    true = full FIFO's depth can be used, but timing on WR and FULL is worse for high DATA_WIDTH
    --   false = FIFO is 4 items shallower (take this into accont when setting a value of ALMOST_FULL_OFFSET!), but timing on WR and FULL is better
    -- NOTE: disabling makes a difference only when FIRST_WORD_FALL_THROUGH is true, DEVICE is VIRTEX6 or 7SERIES and FIFO size (DATA_WIDTH*ITEMS) is more than 36Kb
    PRECISE_FULL            : boolean := true;
    -- Timing speed of EMPTY signal (read interface) assertion.
    --   false = standard ORing of flags (just a few LUTs), but timing on RD anf EMPTY is worse for high DATA_WIDTH
    --    true = more extra resources (mainly registers), but timing on RD and EMPTY is better
    -- NOTE: enabling makes a difference only when FIRST_WORD_FALL_THROUGH is true, DEVICE is VIRTEX6 or 7SERIES and FIFO size (DATA_WIDTH*ITEMS) is more than 36Kb
    FAST_EMPTY              : boolean := false
  );
  port(
    RX_CLK        : in  std_logic;
    RX_RESET      : in  std_logic;
    RX_DATA       : in std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_SOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    RX_EOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_SOF        : in std_logic_vector(REGIONS-1 downto 0);
    RX_EOF        : in std_logic_vector(REGIONS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    -- NOTE: assertion delay of few cycles after valid TX cycle (UG473) (same as: read from FULL fifo will deassert FULL only after few cycles)
    RX_DST_RDY    : out std_logic;
    AFULL         : out std_logic;

    TX_CLK        : in  std_logic;
    TX_RESET      : in  std_logic;
    TX_DATA       : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_SOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX_EOF_POS    : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_SOF        : out std_logic_vector(REGIONS-1 downto 0);
    TX_EOF        : out std_logic_vector(REGIONS-1 downto 0);
    -- NOTE: assertion delay of few cycles after valid RX cycle (UG473) (same as: write into EMPTY fifo will deassert EMPTY only after few cycles)
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic;
    AEMPTY        : out std_logic
  );
end entity;

architecture full of MFB_ASFIFO_BRAM_XILINX is

  constant WORD_WIDTH        : integer := REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
  constant SOF_POS_WIDTH     : integer := REGIONS * max(1,log2(REGION_SIZE));
  constant EOF_POS_WIDTH     : integer := REGIONS * max(1,log2(REGION_SIZE*BLOCK_SIZE));
  constant DW : integer := WORD_WIDTH + SOF_POS_WIDTH + EOF_POS_WIDTH + REGIONS + REGIONS;

  subtype DW_DATA          is natural range WORD_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS-1 downto SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS;
  subtype DW_SOF_POS       is natural range SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS-1 downto EOF_POS_WIDTH+REGIONS+REGIONS;
  subtype DW_EOF_POS       is natural range EOF_POS_WIDTH+REGIONS+REGIONS-1 downto REGIONS+REGIONS;
  subtype DW_SOF           is natural range REGIONS+REGIONS-1 downto REGIONS;
  subtype DW_EOF           is natural range REGIONS-1 downto 0;

  signal di, do : std_logic_vector(DW-1 downto 0);
  signal full, empty : std_logic;

begin

  fifo_core : entity work.ASFIFO_BRAM_XILINX
  generic map (
    DEVICE                  => DEVICE,
    DATA_WIDTH              => DW,
    ITEMS                   => ITEMS,
    ALMOST_FULL_OFFSET      => ALMOST_FULL_OFFSET,
    ALMOST_EMPTY_OFFSET     => ALMOST_EMPTY_OFFSET,
    DO_REG                  => true,
    FIRST_WORD_FALL_THROUGH => true,
    PRECISE_FULL            => PRECISE_FULL,
    FAST_EMPTY              => FAST_EMPTY
  ) port map (
    RST_WR   => RX_RESET,
    CLK_WR   => RX_CLK,
    DI       => di,
    WR       => RX_SRC_RDY,
    FULL     => full,
    AFULL    => AFULL,
    RST_RD   => TX_RESET,
    CLK_RD   => TX_CLK,
    DO       => do,
    RD       => TX_DST_RDY,
    EMPTY    => empty,
    AEMPTY   => AEMPTY
  );

  di(DW_DATA) <= RX_DATA;
  di(DW_SOF_POS) <= RX_SOF_POS;
  di(DW_EOF_POS) <= RX_EOF_POS;
  di(DW_SOF) <= RX_SOF;
  di(DW_EOF) <= RX_EOF;
  RX_DST_RDY <= not full;

  TX_DATA    <= do(DW_DATA);
  TX_SOF_POS <= do(DW_SOF_POS);
  TX_EOF_POS <= do(DW_EOF_POS);
  TX_SOF     <= do(DW_SOF);
  TX_EOF     <= do(DW_EOF);
  TX_SRC_RDY <= not empty;

end architecture;
