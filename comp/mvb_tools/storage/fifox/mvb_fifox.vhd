-- fifo_ent.vhd: Multi-Value Bus with implementation on FIFOX
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author: Michal Szabo <xszabo11@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;

entity MVB_FIFOX is
  generic(
      -- Number of MVB items in word
      ITEMS               : natural := 4;
      -- One MVB item width
      ITEM_WIDTH          : natural := 8;
      -- FIFO depth, number of data words
      FIFO_DEPTH          : natural := 512;
      -- Select memory implementation. Options:
      --
      -- * "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32)
      -- * "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32)
      -- * "URAM"  - effective when ITEMS*FIFO_WIDTH >= 288000
      --   and FIFO_WIDTH >= 72 (URAM is only for Xilinx Ultrascale(+))
      -- * "SHIFT" - effective when ITEMS <= 16
      -- * "AUTO"  - effective implementation dependent on ITEMS and DEVICE
      RAM_TYPE            : string  := "AUTO";
      -- Defines what architecture is FIFO implemented on Options:
      --
      -- * "ULTRASCALE" (Xilinx)
      -- * "7SERIES"    (Xilinx)
      -- * "ARRIA10"    (Intel)
      -- * "STRATIX10"  (Intel)
      DEVICE              : string  := "ULTRASCALE";
      -- | Determins how many data words left free when almost_full is triggered.
      -- | (ITEMS - ALMOST_FULL_OFFSET)
      ALMOST_FULL_OFFSET  : natural := 1;
      -- | Determins how many data words present when almost_empty is triggered.
      -- | (0 + ALMOST_EMPTY_OFFSET)
      ALMOST_EMPTY_OFFSET : natural := 1;
      -- Disables the FIFO implementation and replaces it with straight wires.
      FAKE_FIFO           : boolean := false
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA        : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_VLD         : in std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY     : in std_logic;
    RX_DST_RDY     : out std_logic;

    TX_DATA        : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX_VLD         : out std_logic_vector(ITEMS-1 downto 0);
    TX_SRC_RDY     : out std_logic;
    TX_DST_RDY     : in std_logic;

    STATUS         : out std_logic_vector(log2(FIFO_DEPTH) downto 0);
    AFULL          : out std_logic;
    AEMPTY         : out std_logic
  );
end MVB_FIFOX;

architecture behavioral of MVB_FIFOX is

  constant FIFO_WIDTH : integer := ITEMS * ITEM_WIDTH + ITEMS;

  signal rx_data_vec, tx_data_vec : std_logic_vector(FIFO_WIDTH-1 downto 0);
  signal fifo_full : std_logic;
  signal fifo_empty : std_logic;

begin

   fifo_core : entity work.FIFOX
      generic map(
         DATA_WIDTH          => FIFO_WIDTH,
         ITEMS               => FIFO_DEPTH,
         RAM_TYPE            => RAM_TYPE,
         DEVICE              => DEVICE,
         ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
         ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
         FAKE_FIFO           => FAKE_FIFO
      ) port map(
         CLK         => CLK,
         RESET       => RESET,
         DI          => rx_data_vec,
         WR          => RX_SRC_RDY,
         FULL        => fifo_full,
         AFULL       => AFULL,
         STATUS      => STATUS,

         DO          => tx_data_vec,
         RD          => TX_DST_RDY,
         EMPTY       => fifo_empty,
         AEMPTY      => AEMPTY
      );

    -- Connections with entity

    rx_data_vec <= RX_DATA & RX_VLD;
    RX_DST_RDY <= not fifo_full;

    TX_DATA <= tx_data_vec(FIFO_WIDTH-1 downto ITEMS);
    TX_VLD <= tx_data_vec(ITEMS-1 downto 0);
    TX_SRC_RDY <= not fifo_empty;

end behavioral;
