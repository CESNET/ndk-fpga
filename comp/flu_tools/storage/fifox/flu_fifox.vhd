-- flu_fifox.vhd: FLU wrapper of FIFOX
-- Copyright (C) 2018 CESNET
-- Author(s): Michal Szabo <xszabo11@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;



entity FLU_FIFOX is
  generic(
      -- Data word width in bits.
      DATA_WIDTH          : natural := 256;
      -- FIFO depth, number of data words
      ITEMS               : natural := 512;
      -- Select memory implementation. Options:
      -- "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32),
      -- "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32),
      -- "URAM"  - effective when ITEMS*DW >= 288000
      --           and DW >= 72 (URAM is only for Xilinx Ultrascale(+)),
      -- "SHIFT" - effective when ITEMS <= 16,
      -- "AUTO"  - effective implementation dependent on ITEMS and DEVICE.
      RAM_TYPE            : string  := "AUTO";
      -- Defines what architecture is FIFO implemented on Options:
      -- "ULTRASCALE" (Xilinx)
      -- "7SERIES"    (Xilinx)
      -- "ARRIA10"    (Intel)
      -- "STRATIX10"  (Intel)
      DEVICE              : string  := "ULTRASCALE";
      -- Determins how many data words left free when almost_full is triggered.
      -- (ITEMS - ALMOST_FULL_OFFSET)
      ALMOST_FULL_OFFSET  : natural := 1;
      -- Determins how many data words present when almost_empty is triggered.
      -- (0 + ALMOST_EMPTY_OFFSET)
      ALMOST_EMPTY_OFFSET : natural := 1;
      SOP_POS_WIDTH       : integer := 2
  );
  port(
    CLK      : in  std_logic;
    RESET    : in  std_logic;

    RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    RX_SOP_POS     : in  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    RX_EOP_POS     : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
    RX_SOP         : in  std_logic;
    RX_EOP         : in  std_logic;
    RX_SRC_RDY     : in  std_logic;
    RX_DST_RDY     : out std_logic; -- NOTE: assertion delay of few cycles after valid TX cycle (UG473) (same as: read from FULL fifo will deassert FULL only after few cycles)

    TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
    TX_SOP         : out std_logic;
    TX_EOP         : out std_logic;
    TX_SRC_RDY     : out std_logic; -- NOTE: assertion delay of few cycles after valid RX cycle (UG473) (same as: write into EMPTY fifo will deassert EMPTY only after few cycles)
    TX_DST_RDY     : in  std_logic;

    STATUS         : out std_logic_vector(log2(ITEMS) downto 0);
    AFULL          : out std_logic;
    AEMPTY         : out std_logic
  );
end entity;



architecture full of FLU_FIFOX is

  constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);
  constant DW : integer := DATA_WIDTH + SOP_POS_WIDTH + EOP_POS_WIDTH + 1 + 1;

  signal di, do : std_logic_vector(DW-1 downto 0);
  signal full, empty : std_logic;

begin

   fifo_core : entity work.FIFOX
   generic map (
      DATA_WIDTH          => DW,
      ITEMS               => ITEMS,
      RAM_TYPE            => RAM_TYPE,
      DEVICE              => DEVICE,
      ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
      ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
  ) port map (
      CLK      => CLK,
      RESET    => RESET,
      DI       => di,
      WR       => RX_SRC_RDY,
      FULL     => full,
      AFULL    => AFULL,
      STATUS   => STATUS,

      DO       => do,
      RD       => TX_DST_RDY,
      EMPTY    => empty,
      AEMPTY   => AEMPTY
  );

  di <= RX_DATA & RX_SOP_POS & RX_EOP_POS & RX_SOP & RX_EOP;
  RX_DST_RDY <= not full;

  TX_DATA    <= do(DW-1 downto DW-DATA_WIDTH);
  TX_SOP_POS <= do(SOP_POS_WIDTH+EOP_POS_WIDTH+1 downto EOP_POS_WIDTH+2);
  TX_EOP_POS <= do(EOP_POS_WIDTH+1 downto 2);
  TX_SOP     <= do(1);
  TX_EOP     <= do(0);
  TX_SRC_RDY <= not empty;

end architecture;
