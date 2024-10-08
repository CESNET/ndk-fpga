-- fifo_bram_xilinx_ent.vhd: FIFO implemented in Xilinx BRAMs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

entity FIFO_BRAM_XILINX is
  generic(
    DEVICE                  : string := "ULTRASCALE"; --! "VIRTEX6", "7SERIES", "ULTRASCALE"
    DATA_WIDTH              : integer := 64; --! any possitive value
    ITEMS                   : integer := 512; --! 512, 1024, 2048, 4096, 8192 (less effective)
    FIRST_WORD_FALL_THROUGH : boolean := true;
    DO_REG                  : boolean := true; -- forced true when FIRST_WORD_FALL_THROUGH is true on VIRTEX6 or 7SERIES devices
    ALMOST_FULL_OFFSET      : integer := 128;
    ALMOST_EMPTY_OFFSET     : integer := 128;
    IS_RD_INVERTED          : boolean := false;
    IS_WR_INVERTED          : boolean := false;
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
    CLK      : in  std_logic;
    RESET    : in  std_logic;

    DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    WR       : in  std_logic;
    AFULL    : out std_logic;
    FULL     : out std_logic;

    DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    RD       : in  std_logic;
    AEMPTY   : out std_logic;
    EMPTY    : out std_logic
  );
end entity;
