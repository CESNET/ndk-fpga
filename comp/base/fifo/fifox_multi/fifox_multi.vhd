-- fifox_multi_ent.vhd: FIFOX MULTI entity
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;

-- Synchronous FIFO queue, allowing for multiple write and read requests in
-- each cycle. With ``N`` write ports and ``M`` read ports it can perform 0 to
-- ``N`` writes and 0 to ``M`` reads simultaneously. Uses :ref:`FIFOX <fifox>`
-- internally (multiple, when required).
entity FIFOX_MULTI is
    generic (
        -- Width of data word stored in FIFO, in bits.
        DATA_WIDTH          : natural := 512;
        -- Number of data words to fit in the FIFO.
        --
        -- WARNING: The actual maximum amount may be a bit larger due to input
        -- registers
        --
        -- Must be a power of two; will be automatically rounded up to the nearest
        -- power of two if it is not.
        ITEMS               : natural := 512;

        -- Number of write ports
        WRITE_PORTS         : natural := 4;
        -- Number of read ports
        READ_PORTS          : natural := 2;

        -- See :vhdl:type:`FIFOX_RAM_TYPE`
        RAM_TYPE            : string  := "AUTO";
        -- See the documentation of the ``DEVICE`` generic on the :vhdl:entity:`FIFOX` entity instead.
        DEVICE              : string  := "ULTRASCALE";

        -- Determines how few data words must be left free for
        -- :vhdl:portsignal:`AFULL <fifox_multi.afull>` to be triggered.
        --
        -- (``currently_stored`` >= ``(`` :vhdl:genconstant:`ITEMS <fifox_multi.items>` ``- ALMOST_FULL_OFFSET)``
        --
        -- For architecture SHAKEDOWN counts number of cycles spent reading, not ITEMS!
        ALMOST_FULL_OFFSET  : natural := 0;
        -- Determines how few data words must be stored for
        -- :vhdl:portsignal:`AEMPTY <fifox_multi.aempty>` to be triggered.
        --
        -- ( ``currently_stored <= ALMOST_EMPTY_OFFSET`` )
        --
        -- For architecture SHAKEDOWN counts number of cycles spent writing, not ITEMS!
        ALMOST_EMPTY_OFFSET : natural := 0;

        -- Allow instancing of a simple single FIFOX when ``WRITE_PORTS==READ_PORTS==1``
        --
        -- This will lead to the removal of some control logic,
        -- but will also **lower the component's latency**.
        ALLOW_SINGLE_FIFO   : boolean := true;

        -- In safe read mode it is safe to attempt reading (setting ``RD`` to ``'1'``)
        -- from ports, that are currently empty.
        --
        -- This mode leads to worse timing and is often not needed, so it can be disabled here.
        SAFE_READ_MODE      : boolean := true;

        -- ARCHITECTURE SELECTION:
        -- 1. FULL: [Shakedown -> B-Shifter -> Multi-FIFO -> B-Shifter]
        --    + Native gap removal; narrow MUXes (log2 scale).
        --    - High resource usage (multiple FIFOs); async output path.
        -- 2. SHAKEDOWN: [Single FIFO -> MVB Shakedown]
        --    + Low resources; direct register output.
        --    - Throughput ~87%; wide MUXes (2x vs FULL); worse buffering (gaps in FIFO).
        FIFOX_MULTI_ARCH    : string  := "FULL"
    );
    port (
        CLK    : in  std_logic;
        RESET  : in  std_logic;

        -- =======================================================================
        --  WRITE INTERFACE
        -- =======================================================================
        -- Writing does not need to be aligned to port 0.
        -- (i.e. with 4 write ports you can write on port 0 and 2 while not using ports 1 and 3)
        --
        -- FULL behavior:
        -- When FULL is 0 the FIFO can accept any number of writes (0-WRITE_PORTS).
        -- When FULL is 1 the FIFO no writes can be done.
        -- Allows writing of up to "ITEMS_ACT + WRITE_PORTS*3" items (contains 3 levels of input registers).

        DI     : in  std_logic_vector(WRITE_PORTS*DATA_WIDTH-1 downto 0); -- Data input
        WR     : in  std_logic_vector(WRITE_PORTS-1 downto 0);            -- Write enable for each input item
        FULL   : out std_logic;                                           -- Full flag
        AFULL  : out std_logic;                                           -- Almost full flag

        -- =======================================================================
        --  READ INTERFACE
        -- =======================================================================
        -- Reading MUST be aligned to port 0!
        -- (i.e. to read 2 items from 4 read ports you must use ports 0 and 1)
        --
        -- EMPTY behavior:
        -- The EMPTY signal works as "not SRC_RDY" for each port.
        -- Reading from an EMPTY port is not allowed unless the SAFE_READ_MODE generic is enabled.

        DO     : out std_logic_vector(READ_PORTS*DATA_WIDTH-1 downto 0); -- Data output
        RD     : in  std_logic_vector(READ_PORTS-1 downto 0);            -- Read confirm for each item
        EMPTY  : out std_logic_vector(READ_PORTS-1 downto 0);            -- Empty flags ("invalid" for each item)
        AEMPTY : out std_logic                                           -- Almost empty flag
    );
end entity;

architecture FULL of FIFOX_MULTI is

begin

    -- ////////////////////////////////////////////////////////////////////////// --
    --                                                                            --
    --                              FIFOX_MULTI_FULL                              --
    --                                                                            --
    -- ////////////////////////////////////////////////////////////////////////// --
    -- This architecture consists of a SHAKEDOWN, a BARREL SHIFTER, multiple FIFOXs
    -- and another BARREL SHIFTER on output.
    -- PROS:
    --     - MUXes are only as wide as 2**(log2(max(INPUT_PORTS,OUTPUT_PORTS))).
    --     - Native removing of gaps in data words (if reading slower then writing).
    -- CONS:
    --     - More resources used by multiple FIFOXs.
    --     - Output propagated through an asynchronous BARREL SHIFTER.

    fifox_multi_full_g: if FIFOX_MULTI_ARCH = "FULL" generate
        fifox_multi_full_i : entity work.FIFOX_MULTI_GEN(FULL)
        generic map (
            DATA_WIDTH          => DATA_WIDTH,
            ITEMS               => ITEMS,
            WRITE_PORTS         => WRITE_PORTS,
            READ_PORTS          => READ_PORTS,
            RAM_TYPE            => RAM_TYPE,
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
            ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
            ALLOW_SINGLE_FIFO   => ALLOW_SINGLE_FIFO,
            SAFE_READ_MODE      => SAFE_READ_MODE
        )
        port map (
            CLK    => CLK,
            RESET  => RESET,

            DI     => DI,
            WR     => WR,
            FULL   => FULL,
            AFULL  => AFULL,

            DO     => DO,
            RD     => RD,
            EMPTY  => EMPTY,
            AEMPTY => AEMPTY
        );
    end generate;

    -- ////////////////////////////////////////////////////////////////////////// --
    --                                                                            --
    --                           FIFOX_MULTI_SHAKEDOWN                            --
    --                                                                            --
    -- ////////////////////////////////////////////////////////////////////////// --
    -- This architecture consists of a simple FIFOX and a MVB SHAKEDOWN at the end.
    -- PROS:
    --     - Less resources thanks to only one FIFOX being present.
    --     - Output propagated directly from a register.
    -- CONS:
    --     - Output register is connected in a self-loop through a MVB SHAKEDOWN.
    --       This SHAKEDOWN has MUXes twice as wide as would be needed
    --       in architecture FULL.
    --     - Worse buffering capabilities. (The data words FIFOX contain non-valid
    --       items)
    --     - Worse throughput (approximately 87% compared to architecture FULL
    --       according to tests in simulation).

    fifox_multi_shakedown_g: if FIFOX_MULTI_ARCH = "SHAKEDOWN" generate
        fifox_multi_shakedown_i : entity work.FIFOX_MULTI_GEN(SHAKEDOWN)
        generic map (
            DATA_WIDTH          => DATA_WIDTH,
            ITEMS               => ITEMS,
            WRITE_PORTS         => WRITE_PORTS,
            READ_PORTS          => READ_PORTS,
            RAM_TYPE            => RAM_TYPE,
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
            ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
            ALLOW_SINGLE_FIFO   => ALLOW_SINGLE_FIFO,
            SAFE_READ_MODE      => SAFE_READ_MODE
        )
        port map (
            CLK    => CLK,
            RESET  => RESET,

            DI     => DI,
            WR     => WR,
            FULL   => FULL,
            AFULL  => AFULL,

            DO     => DO,
            RD     => RD,
            EMPTY  => EMPTY,
            AEMPTY => AEMPTY
        );
    end generate;

    check_arch_g: if FIFOX_MULTI_ARCH /= "FULL" and FIFOX_MULTI_ARCH /= "SHAKEDOWN" generate
        assert false
            report "CONFIGURATION ERROR: The architecture '" & FIFOX_MULTI_ARCH & "' is not recognized. Please use 'SHAKEDOWN' or 'FULL'."
            severity failure;
    end generate;


end architecture;
