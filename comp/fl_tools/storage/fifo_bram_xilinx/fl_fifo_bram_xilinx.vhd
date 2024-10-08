-- fl_fifo_bram_xilinx.vhd: FL wrapper of FIFO implemented in Xilinx BRAMs
-- Copyright (C) 2016 CESNET
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



entity FL_FIFO_BRAM_XILINX is
  generic(
    DEVICE                  : string := "7SERIES"; --! "VIRTEX6", "7SERIES", "ULTRASCALE"
    DATA_WIDTH              : integer := 256;
    ITEMS                   : integer := 512; --! 512, 1024, 2048, 4096, 8192 (less effective)
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

    RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
    RX_SOP_N       : in  std_logic;
    RX_EOP_N       : in  std_logic;
    RX_SOF_N       : in  std_logic;
    RX_EOF_N       : in  std_logic;
    RX_SRC_RDY_N   : in  std_logic;
    RX_DST_RDY_N   : out std_logic; -- NOTE: deassertion delay of few cycles after valid TX cycle (UG473) (same as: read from FULL fifo will deassert FULL only after few cycles)

    TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
    TX_SOP_N       : out std_logic;
    TX_EOP_N       : out std_logic;
    TX_SOF_N       : out std_logic;
    TX_EOF_N       : out std_logic;
    TX_SRC_RDY_N   : out std_logic; -- NOTE: deassertion delay of few cycles after valid RX cycle (UG473) (same as: write into EMPTY fifo will deassert EMPTY only after few cycles)
    TX_DST_RDY_N   : in  std_logic
  );
end entity;



architecture full of FL_FIFO_BRAM_XILINX is

  constant REM_WIDTH : integer := log2(DATA_WIDTH/8);
  constant DW : integer := DATA_WIDTH + REM_WIDTH + 1 + 1 + 1 + 1;

  signal di, do : std_logic_vector(DW-1 downto 0);

begin

  fifo_core : entity work.FIFO_BRAM_XILINX
  generic map (
    DEVICE                  => DEVICE,
    DATA_WIDTH              => DW,
    ITEMS                   => ITEMS,
    DO_REG                  => true,
    FIRST_WORD_FALL_THROUGH => true,
    IS_RD_INVERTED          => true,
    IS_WR_INVERTED          => true,
    PRECISE_FULL            => PRECISE_FULL,
    FAST_EMPTY              => FAST_EMPTY
  ) port map (
    CLK      => CLK,
    RESET    => RESET,
    DI       => di,
    WR       => RX_SRC_RDY_N,
    FULL     => RX_DST_RDY_N,
    DO       => do,
    RD       => TX_DST_RDY_N,
    EMPTY    => TX_SRC_RDY_N
  );

  di <= RX_DATA & RX_REM & RX_SOP_N & RX_EOP_N & RX_SOF_N & RX_EOF_N;

  TX_DATA    <= do(DW-1 downto DW-DATA_WIDTH);
  TX_REM     <= do(DW-DATA_WIDTH-1 downto 4);
  TX_SOP_N   <= do(3);
  TX_EOP_N   <= do(2);
  TX_SOF_N   <= do(1);
  TX_EOF_N   <= do(0);

end architecture;
