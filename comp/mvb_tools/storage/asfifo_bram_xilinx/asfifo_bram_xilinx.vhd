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

-- Asynchronous FIFO for the MVB bus with independent RX (write) and TX (read)
-- clock domains, built directly on Xilinx block-RAM FIFO primitives
-- (FIFO18E1/FIFO36E1 or FIFO18E2/FIFO36E2, selected by the DEVICE generic).
-- The MVB item validity (RX_VLD/TX_VLD) is stored in the same memory as the
-- data, so both cross the clock-domain boundary together atomically.
--
-- The component is always operated in First-Word-Fall-Through mode with a
-- registered output, i.e. the oldest stored word is presented on TX_DATA/TX_VLD
-- together with TX_SRC_RDY as soon as it is stored, without needing a
-- preceding dummy transfer to first shift it into the output register (as a
-- standard, non-FWFT FIFO would require). TX_DST_RDY is only used to accept
-- the current word and advance to the next one, never to make the current
-- word visible in the first place.
--
-- .. WARNING::
--    The FIFO memory is reset only by **RX_RESET**. TX_RESET is accepted by
--    the entity for interface symmetry but is **not connected to the
--    underlying FIFO primitives on any supported device** and has no effect.
--    Do not rely on TX_RESET to clear the FIFO content or the TX-side
--    interface.
--
-- .. WARNING::
--    Because of the underlying BRAM FIFO primitive behavior (see Xilinx
--    UG473), status flags react to the opposite side's activity only after
--    a delay of a few clock cycles: RX_DST_RDY/AFULL are deasserted a few
--    RX_CLK cycles after a word is actually read out on the TX side, and
--    TX_SRC_RDY/AEMPTY are asserted a few TX_CLK cycles after a word is
--    actually written on the RX side.
--
entity MVB_ASFIFO_BRAM_XILINX is
    generic (
        -- Target FPGA device.
        -- "VIRTEX6", "7SERIES", "ULTRASCALE", "VERSAL"
        DEVICE                  : string := "7SERIES";
        -- Width of one MVB item in bits.
        -- Any positive value.
        ITEM_WIDTH              : integer := 8;
        -- Number of MVB items transferred in one word.
        -- Any positive value.
        REGIONS                 : integer := 4;
        -- FIFO depth in number of words. Recommended values are 512, 1024,
        -- 2048, 4096 or 8192 (the last one uses BRAM less efficiently); any
        -- other value is internally rounded up to the nearest one of these,
        -- wasting block RAM capacity, so set this generic directly to one
        -- of the recommended values. Values above 8192 are not supported
        -- and fail at elaboration.
        FIFO_ITEMS              : integer := 512;
        -- Number of free words (write/RX side) at or below which AFULL is asserted.
        ALMOST_FULL_OFFSET      : integer := 128;
        -- Number of stored words (read/TX side) at or below which AEMPTY is asserted.
        ALMOST_EMPTY_OFFSET     : integer := 128;
        -- Precision of the FULL signal (write interface) assertion.
        --
        -- * true = the full FIFO_ITEMS depth is usable, but timing on RX_SRC_RDY/RX_DST_RDY is worse for wide words.
        -- * false = the FIFO is effectively 4 items shallower (account for this when setting ALMOST_FULL_OFFSET), but timing is better.
        --
        -- Only makes a difference when the stored word (REGIONS*ITEM_WIDTH+REGIONS
        -- bits, i.e. data plus the packed validity bits) together with
        -- FIFO_ITEMS requires more than one cascaded Xilinx BRAM (word x depth
        -- product exceeds a single 36 Kb block). Applies on all supported devices.
        PRECISE_FULL            : boolean := true;
        -- Timing speed of the EMPTY signal (read interface) assertion.
        --
        -- * false = standard ORing of internal flags (a few LUTs only), worse timing on TX_DST_RDY/TX_SRC_RDY for wide words.
        -- * true = uses extra resources (mainly registers), but improves timing.
        --
        -- Only makes a difference when more than two Xilinx BRAMs are
        -- cascaded (a stricter condition than PRECISE_FULL above). Applies
        -- on all supported devices. The matching FAST_EMPTY_DEPTH generic of
        -- the underlying ``ASFIFO_BRAM_XILINX`` core is not exposed by this
        -- wrapper (stays at its default of 1), which is only valid when
        -- TX_CLK is at least as fast as RX_CLK.
        FAST_EMPTY              : boolean := false
    );
    port (
        -- =====================================================================
        -- RX INTERFACE (write side, RX_CLK domain)
        -- =====================================================================

        RX_CLK        : in  std_logic;
        -- Resets the whole FIFO (both RX and TX sides), see the WARNING above.
        RX_RESET      : in  std_logic;
        RX_DATA       : in  std_logic_vector(REGIONS*ITEM_WIDTH-1 downto 0);
        RX_VLD        : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY    : in  std_logic;
        RX_DST_RDY    : out std_logic;
        -- Almost-full flag, see ALMOST_FULL_OFFSET and the timing WARNING above.
        AFULL         : out std_logic;

        -- =====================================================================
        -- TX INTERFACE (read side, TX_CLK domain - independent of RX_CLK)
        -- =====================================================================

        TX_CLK        : in  std_logic;
        -- Has no effect, see the WARNING above.
        TX_RESET      : in  std_logic;
        TX_DATA       : out std_logic_vector(REGIONS*ITEM_WIDTH-1 downto 0);
        TX_VLD        : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY    : out std_logic;
        TX_DST_RDY    : in  std_logic;
        -- Almost-empty flag, see ALMOST_EMPTY_OFFSET and the timing WARNING above.
        AEMPTY        : out std_logic
    );
end entity;



architecture FULL of MVB_ASFIFO_BRAM_XILINX is

    signal di : std_logic_vector(REGIONS*ITEM_WIDTH+REGIONS-1 downto 0);
    signal do : std_logic_vector(REGIONS*ITEM_WIDTH+REGIONS-1 downto 0);

    signal full  : std_logic;
    signal empty : std_logic;

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

    di         <= RX_DATA & RX_VLD;
    RX_DST_RDY <= not full;

    (TX_DATA, TX_VLD) <= do;
    TX_SRC_RDY        <= not empty;

end architecture;
