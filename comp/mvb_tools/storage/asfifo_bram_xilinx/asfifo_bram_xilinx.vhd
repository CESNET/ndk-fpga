-- fifo_asbram_xilinx.vhd: Multi-Frame Bus wrapper of asynchronous FIFO implemented in Xilinx BRAMs
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;
use work.math_pack.all;

entity MVB_ASFIFO_BRAM_XILINX is
  generic(
    -- Frame size restrictions: none
    -- "VIRTEX6", "7SERIES", "ULTRASCALE"
    DEVICE                  : string := "7SERIES";
    -- Width of one MVB item
    -- any possitive value
    ITEM_WIDTH              : integer := 8;
    -- Number of ITEMS in one Word
    REGIONS                 : integer := 4;
    -- Number of Words in FIFO
    -- 512, 1024, 2048, 4096, 8192 (less effective)
    FIFO_ITEMS              : integer := 512;
    -- Almost Full/Empty offsets
    ALMOST_FULL_OFFSET      : integer := 128;
    ALMOST_EMPTY_OFFSET     : integer := 128;
    -- Precision of FULL signal (write interface) assertion.
    --   true = full FIFO's depth can be used, but timing on WR and FULL is worse for high DATA_WIDTH
    --   false = FIFO is 4 items shallower (take this into accont when setting a value of ALMOST_FULL_OFFSET!), but timing on WR and FULL is better
    -- NOTE: disabling makes a difference only when FIRST_WORD_FALL_THROUGH is true, DEVICE is VIRTEX6 or 7SERIES and FIFO size (DATA_WIDTH*FIFO_ITEMS) is more than 36Kb
    PRECISE_FULL            : boolean := true;
    -- Timing speed of EMPTY signal (read interface) assertion.
    --   false = standard ORing of flags (just a few LUTs), but timing on RD anf EMPTY is worse for high DATA_WIDTH
    --    true = more extra resources (mainly registers), but timing on RD and EMPTY is better
    -- NOTE: enabling makes a difference only when FIRST_WORD_FALL_THROUGH is true, DEVICE is VIRTEX6 or 7SERIES and FIFO size (DATA_WIDTH*FIFO_ITEMS) is more than 36Kb
    FAST_EMPTY              : boolean := false
  );
  port(
    RX_CLK        : in  std_logic;
    RX_RESET      : in  std_logic;
    RX_DATA       : in  std_logic_vector(REGIONS*ITEM_WIDTH-1 downto 0);
    RX_VLD        : in  std_logic_vector(REGIONS-1 downto 0);
    RX_SRC_RDY    : in  std_logic;
    -- NOTE: assertion delay of few cycles after valid TX cycle (UG473) (same as: read from FULL fifo will deassert FULL only after few cycles)
    RX_DST_RDY    : out std_logic;
    AFULL         : out std_logic;

    TX_CLK        : in  std_logic;
    TX_RESET      : in  std_logic;
    TX_DATA       : out std_logic_vector(REGIONS*ITEM_WIDTH-1 downto 0);
    TX_VLD        : out std_logic_vector(REGIONS-1 downto 0);
    -- NOTE: assertion delay of few cycles after valid RX cycle (UG473) (same as: write into EMPTY fifo will deassert EMPTY only after few cycles)
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in  std_logic;
    AEMPTY        : out std_logic
  );
end entity;



architecture full of MVB_ASFIFO_BRAM_XILINX is

  signal di, do : std_logic_vector(REGIONS*ITEM_WIDTH+REGIONS-1 downto 0);

  signal full, empty : std_logic;

begin

  fifo_core : entity work.ASFIFO_BRAM_XILINX
  generic map (
    DEVICE                  => DEVICE,
    DATA_WIDTH              => REGIONS*ITEM_WIDTH+REGIONS,
    ITEMS                   => FIFO_ITEMS,
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

  di <= RX_DATA & RX_VLD;
  RX_DST_RDY <= not full;

  (TX_DATA, TX_VLD) <= do;
  TX_SRC_RDY <= not empty;

end architecture;
