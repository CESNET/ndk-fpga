-- fifo_ent.vhd: Multi-Value Bus generic FIFO
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;



-- Synchronous (single clock domain) general-purpose FIFO for the MVB bus.
-- Selects between a distributed/LUT-RAM-based core and a BlockRAM-based core
-- (see USE_BRAMS). The TX side always behaves as First-Word-Fall-Through,
-- i.e. valid data is presented on TX_DATA/TX_VLD together with TX_SRC_RDY as
-- soon as it is available, without needing a prior TX_DST_RDY request.
--
-- .. WARNING::
--    When USE_DST_RDY = false, no FIFO memory is instantiated at all: the
--    component becomes a pure combinational pass-through (RX_DATA/RX_VLD/
--    RX_SRC_RDY wired directly to TX_DATA/TX_VLD/TX_SRC_RDY), RX_DST_RDY is
--    tied permanently to '1' and TX_DST_RDY is completely ignored. Use this
--    mode only where the TX-side consumer is guaranteed to always be ready;
--    otherwise data is silently lost.
--
entity MVB_FIFO is
    generic (
        -- Number of MVB items transferred in one word.
        -- Any positive value.
        ITEMS          : integer := 4;
        -- Width of one MVB item in bits.
        -- Any positive value.
        ITEM_WIDTH     : integer := 8;
        -- Enables destination-ready (backpressure) handling and the actual
        -- FIFO storage memory. See the WARNING above for the false case.
        USE_DST_RDY    : boolean := true;
        -- Select memory implementation (only relevant when USE_DST_RDY = true):
        --
        -- * true  - BlockRAM-based core (FIFO_BRAM); preferable for larger FIFO_ITEMS depths.
        -- * false - distributed/LUT-RAM-based core (FIFO, "SelectRAM"); preferable for small FIFO_ITEMS depths, avoids consuming a whole BRAM.
        USE_BRAMS      : boolean := false;
        -- FIFO depth in number of data words.
        -- Any integer value of 2 or more; does not need to be a power of two.
        FIFO_ITEMS     : integer := 64;
        -- Size, in items, of one write "block" used for the LSTBLK flag.
        -- LSTBLK is asserted once the remaining free capacity drops to
        -- BLOCK_SIZE items, signalling a block-oriented producer that only
        -- one more block of this size can still be safely written.
        BLOCK_SIZE     : integer := 1;
        -- Enables the internal free-space counter that drives STATUS (and,
        -- together with BLOCK_SIZE, LSTBLK). The counter is only skipped
        -- (saving a few resources) when STATUS_ENABLED = false *and*
        -- BLOCK_SIZE = 0 at the same time - BLOCK_SIZE defaults to 1, so
        -- STATUS/LSTBLK are valid by default even with STATUS_ENABLED =
        -- false. See the STATUS/LSTBLK port descriptions for what happens
        -- when the counter is skipped.
        STATUS_ENABLED : boolean := true;
        -- Adds an output register stage on the TX_DATA/TX_VLD path for
        -- better timing, at the cost of extra registers and one additional
        -- clock cycle of latency.
        OUTPUT_REG     : boolean := true
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- =====================================================================
        -- RX INTERFACE
        -- =====================================================================

        RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        RX_VLD        : in std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY    : in std_logic;
        RX_DST_RDY    : out std_logic;

        -- =====================================================================
        -- TX INTERFACE
        -- =====================================================================

        TX_DATA       : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD        : out std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY    : out std_logic;
        TX_DST_RDY    : in std_logic;

        -- =====================================================================
        -- STATUS FLAGS
        -- =====================================================================

        -- When the free-space counter is skipped (see STATUS_ENABLED above):
        -- held at '0' if USE_BRAMS = false, but left completely undriven
        -- (undefined in simulation) if USE_BRAMS = true - avoid that
        -- combination if LSTBLK is used.
        LSTBLK         : out std_logic;
        -- Equivalent to "not RX_DST_RDY".
        FULL           : out std_logic;
        -- Equivalent to "not TX_SRC_RDY" when USE_BRAMS = false. When
        -- USE_BRAMS = true, EMPTY deasserts one CLK cycle before TX_SRC_RDY
        -- asserts (two cycles when OUTPUT_REG = true), because of the
        -- BlockRAM output-register read pipeline latency; use TX_SRC_RDY,
        -- not EMPTY, to determine data validity on the TX side.
        EMPTY          : out std_logic;
        -- Number of currently *free* (unoccupied) words in the FIFO - not the
        -- number of stored words. Held at '0' when the free-space counter
        -- is skipped (see STATUS_ENABLED above).
        STATUS         : out std_logic_vector(log2(FIFO_ITEMS) downto 0)
    );
end entity;
