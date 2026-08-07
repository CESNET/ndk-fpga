-- mvb_asfifox.vhd: MVB ASFIFOX
-- Copyright (C) 2019 CESNET z. s. p. o.
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

-- Asynchronous (independent RX/TX clock domain) FIFO for the MVB bus,
-- implemented as a thin wrapper around the generic ``ASFIFOX`` component.
-- The MVB item validity (RX_VLD/TX_VLD) is stored together with RX_DATA/TX_DATA
-- in the same memory word, so both cross the clock-domain boundary atomically.
--
-- .. WARNING::
--    RX_RESET and TX_RESET are combined internally (by the underlying
--    ASFIFOX core) into a single reset of the whole FIFO, synchronized
--    separately into each clock domain. Asserting either one resets
--    **both** the write and the read side; they are not independent
--    per-side resets.
--
entity MVB_ASFIFOX is
    generic (
        -- Number of MVB items transferred in one word.
        MVB_ITEMS                   : integer := 4;
        -- Width of one MVB item in bits.
        -- Any positive value.
        MVB_ITEM_WIDTH              : integer := 8;
        -- FIFO depth in number of data words.
        -- Must be a power of two, minimum value is 2.
        FIFO_ITEMS                  : natural := 512;
        -- Select memory implementation:
        --
        -- * "LUT" - distributed/LUT memory, effective for a shallow FIFO (approx. FIFO_ITEMS <= 64).
        -- * "BRAM" - block RAM, effective for a deep FIFO (approx. FIFO_ITEMS > 64).
        -- * "AUTO" - treated the same as "BRAM" by the underlying core.
        RAM_TYPE                    : string  := "BRAM";
        -- First Word Fall Through mode. If true, valid data is ready at
        -- TX_DATA/TX_VLD (TX_SRC_RDY = '1') without TX_DST_RDY having to be
        -- asserted first.
        --
        -- .. WARNING::
        --    Setting this to false removes the automatic advance into the
        --    output register: the core then only reads a new word in direct
        --    response to TX_DST_RDY, so TX_DST_RDY must already be asserted
        --    one or more cycles **before** TX_SRC_RDY becomes valid for that
        --    word (unlike the default, where TX_SRC_RDY becomes valid on its
        --    own and TX_DST_RDY is only needed to accept/advance past it).
        FWFT_MODE                   : boolean := True;
        -- Adds one more register stage between the internal memory's read
        -- output and TX_DATA/TX_VLD/TX_SRC_RDY. Improves timing at the cost
        -- of a few more flip-flops and one additional TX_CLK cycle of
        -- latency between writing a word (RX side) and it becoming valid
        -- on the TX side.
        OUTPUT_REG                  : boolean := True;
        -- Target FPGA device, passed through to the underlying memory
        -- implementation (affects the "LUT" RAM_TYPE only, where it selects
        -- the correct distributed/MLAB memory primitive).
        -- "7SERIES", "ULTRASCALE", "VERSAL", "STRATIX10", "ARRIA10", "AGILEX"
        DEVICE                      : string  := "ULTRASCALE";
        -- Number of free words (write/RX side) at or below which RX_AFULL is asserted.
        ALMOST_FULL_OFFSET          : natural := FIFO_ITEMS/2;
        -- Number of stored words (read/TX side) at or below which TX_AEMPTY is asserted.
        ALMOST_EMPTY_OFFSET         : natural := FIFO_ITEMS/2
    );
    port (
        -- =====================================================================
        -- RX INTERFACE (write side, RX_CLK domain)
        -- =====================================================================

        RX_CLK        : in  std_logic;
        RX_RESET      : in  std_logic;

        RX_DATA       : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        RX_VLD        : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_SRC_RDY    : in  std_logic;
        RX_DST_RDY    : out std_logic;
        -- Asserted when the number of free words drops to or below ALMOST_FULL_OFFSET.
        RX_AFULL      : out std_logic;
        -- Number of words currently stored in the FIFO (write/RX side view).
        RX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0);

        -- =====================================================================
        -- TX INTERFACE (read side, TX_CLK domain - independent of RX_CLK)
        -- =====================================================================

        TX_CLK        : in  std_logic;
        TX_RESET      : in  std_logic;

        TX_DATA       : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        TX_VLD        : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_SRC_RDY    : out std_logic;
        TX_DST_RDY    : in  std_logic;
        -- Asserted when the number of stored words drops to or below ALMOST_EMPTY_OFFSET.
        TX_AEMPTY     : out std_logic;
        -- Number of words currently stored in the FIFO (read/TX side view);
        -- may be nonzero even before the data appears on TX_DATA/TX_VLD.
        TX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0)
    );
end entity;



architecture FULL of MVB_ASFIFOX is

    signal di : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS-1 downto 0);
    signal do : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS-1 downto 0);

    signal full  : std_logic;
    signal empty : std_logic;

begin

    fifo_core : entity work.ASFIFOX
    generic map (
        DATA_WIDTH          => MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS,
        ITEMS               => FIFO_ITEMS,
        RAM_TYPE            => RAM_TYPE,
        FWFT_MODE           => FWFT_MODE,
        OUTPUT_REG          => OUTPUT_REG,
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
        ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
    ) port map (
        WR_CLK    => RX_CLK,
        WR_RST    => RX_RESET,

        WR_DATA   => di,
        WR_EN     => RX_SRC_RDY,
        WR_FULL   => full,
        WR_AFULL  => RX_AFULL,
        WR_STATUS => RX_STATUS,

        RD_CLK    => TX_CLK,
        RD_RST    => TX_RESET,

        RD_DATA   => do,
        RD_EN     => TX_DST_RDY,
        RD_EMPTY  => empty,
        RD_AEMPTY => TX_AEMPTY,
        RD_STATUS => TX_STATUS
    );

    di         <= RX_DATA & RX_VLD;
    RX_DST_RDY <= not full;

    TX_VLD     <= do(MVB_ITEMS-1 downto 0);
    TX_DATA    <= do(MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS-1 downto MVB_ITEMS);
    TX_SRC_RDY <= not empty;

end architecture;
