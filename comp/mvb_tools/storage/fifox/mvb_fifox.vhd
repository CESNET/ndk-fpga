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

-- Synchronous (single clock domain) general-purpose FIFO for the MVB bus,
-- implemented as a thin wrapper around the generic ``FIFOX`` component.
-- The MVB item validity (RX_VLD/TX_VLD) is stored together with RX_DATA/TX_DATA
-- in the same memory word. The TX side behaves as First-Word-Fall-Through:
-- valid data is presented on TX_DATA/TX_VLD together with TX_SRC_RDY without
-- needing a prior TX_DST_RDY request; a write takes at least two CLK cycles
-- before the written word can appear on the TX side.
--
-- .. NOTE::
--    When FAKE_FIFO = true, the FIFO memory is not instantiated; RX and TX
--    are connected combinationally (TX_DATA/TX_VLD = RX_DATA/RX_VLD,
--    TX_SRC_RDY = RX_SRC_RDY, RX_DST_RDY = TX_DST_RDY) with zero latency.
--    Unlike some other FIFO wrappers in this repository, this passthrough
--    still correctly propagates TX-side backpressure to RX_DST_RDY, so it is
--    always safe to use, not only when the TX side is always ready.
--
entity MVB_FIFOX is
    generic (
        -- Number of MVB items transferred in one word.
        ITEMS               : natural := 4;
        -- Width of one MVB item in bits.
        ITEM_WIDTH          : natural := 8;
        -- FIFO depth in number of data words.
        FIFO_DEPTH          : natural := 512;
        -- Select memory implementation. Options:
        --
        -- * "LUT"   - effective when FIFO_DEPTH <= 64 (on Intel FPGA <= 32)
        -- * "BRAM"  - effective when FIFO_DEPTH  > 64 (on Intel FPGA  > 32)
        -- * "URAM"  - effective when FIFO_DEPTH * (ITEMS*ITEM_WIDTH+ITEMS) >= 288000
        --   and (ITEMS*ITEM_WIDTH+ITEMS) >= 72 (URAM is only available on
        --   DEVICE = "ULTRASCALE" or "VERSAL")
        -- * "SHIFT" - effective when FIFO_DEPTH <= 16
        -- * "AUTO"  - implementation chosen automatically based on FIFO_DEPTH and DEVICE
        RAM_TYPE            : string  := "AUTO";
        -- Defines what architecture the FIFO is implemented on. Options:
        --
        -- * "ULTRASCALE", "7SERIES", "VERSAL" (Xilinx)
        -- * "ARRIA10", "STRATIX10", "AGILEX"  (Intel)
        DEVICE              : string  := "ULTRASCALE";
        -- Determines how many free data words remain when AFULL is triggered.
        -- (currently_stored >= FIFO_DEPTH - ALMOST_FULL_OFFSET)
        ALMOST_FULL_OFFSET  : natural := 1;
        -- Determines how many stored data words remain when AEMPTY is triggered.
        -- (currently_stored <= ALMOST_EMPTY_OFFSET)
        ALMOST_EMPTY_OFFSET : natural := 1;
        -- Disables the FIFO implementation and replaces it with straight
        -- wires, see the NOTE above.
        FAKE_FIFO           : boolean := false
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- =====================================================================
        -- RX INTERFACE
        -- =====================================================================

        RX_DATA        : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        RX_VLD         : in std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY     : in std_logic;
        RX_DST_RDY     : out std_logic;

        -- =====================================================================
        -- TX INTERFACE
        -- =====================================================================

        TX_DATA        : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD         : out std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY     : out std_logic;
        TX_DST_RDY     : in std_logic;

        -- =====================================================================
        -- STATUS FLAGS
        -- =====================================================================

        -- Number of words currently stored in the FIFO (not the number of
        -- free words). Held at '0' when FAKE_FIFO = true.
        STATUS         : out std_logic_vector(log2(FIFO_DEPTH) downto 0);
        AFULL          : out std_logic;
        AEMPTY         : out std_logic
    );
end entity;

architecture BEHAVIORAL of MVB_FIFOX is

    constant FIFO_WIDTH : integer := ITEMS * ITEM_WIDTH + ITEMS;

    signal rx_data_vec : std_logic_vector(FIFO_WIDTH-1 downto 0);
    signal tx_data_vec : std_logic_vector(FIFO_WIDTH-1 downto 0);
    signal fifo_full   : std_logic;
    signal fifo_empty  : std_logic;

begin

    fifo_core : entity work.FIFOX
    generic map (
        DATA_WIDTH          => FIFO_WIDTH,
        ITEMS               => FIFO_DEPTH,
        RAM_TYPE            => RAM_TYPE,
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
        ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
        FAKE_FIFO           => FAKE_FIFO
    ) port map (
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
    RX_DST_RDY  <= not fifo_full;

    TX_DATA    <= tx_data_vec(FIFO_WIDTH-1 downto ITEMS);
    TX_VLD     <= tx_data_vec(ITEMS-1 downto 0);
    TX_SRC_RDY <= not fifo_empty;

end architecture;
