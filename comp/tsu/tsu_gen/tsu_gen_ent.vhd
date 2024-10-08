-- tsu_gen_ent.vhd: Entity of GPS synchronized timestamp unit
-- Copyright (C) 2012 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- The TimeStamp Unit is used to generate accurate 64b timestamps in two different
-- formats (see the description of the :vhdl:portsignal:`TS <tsu_gen.ts>`
-- and :vhdl:portsignal:`TS_NS <tsu_gen.ts_ns>` ports). Conversion to another
-- format, where the whole Timestamp represented as a number of nanoseconds, is
-- available with the :ref:`TSU_FORMAT_TO_NS component <tsu_format_to_ns>`
-- (one directory above).
--
-- The TSU supports a pulse per second (PPS) external signal, for example, from
-- a precision GPS receiver. The TSU must be properly configured and activated
-- to start. Configuration is performed by the software tool via the MI interface.
--
-- **MI address space:**
--
-- .. code-block::
--
--   Registers accessible directly via the MI bus:
--   =============================================
--   0x00 = MI_DATA_REG, low part (32b, RW)
--   0x04 = MI_DATA_REG, middle part (32b, RW)
--   0x08 = MI_DATA_REG, high part (32b RW)
--   0x0C = Control register (CTRL_REG) (3b, WO):
--        - "000" write MI_DATA_REG  to INCR_VAL_REG;
--        - "001" write MI_DATA_REG  to REALTIME_REG;
--        - "100" write INCR_VAL_REG to MI_DATA_REG;
--        - "101" write REALTIME_REG to MI_DATA_REG;
--        - "111" write PPS_REG      to MI_DATA_REG;
--   0x10 = State register detection of clk and pps activity (2b, RO):
--        - bit 0: PPS activity detection
--        - bit 1: clock activity detection
--   0x14 = INTA register (1b, WO):
--        - Valid bit register sets the value of the TS_DV output signal.
--   0x18 = Select PPS source (1-32b, RW):
--        - PPS source with higher number should be more precise.
--   0x1C = Actual TSU clock frequency (32b, RO):
--        - Frequency format: 0=1Hz, 1=2Hz, 2=3Hz...
--   0x20 = TSU clock source multiplexor address (1-32b, RW):
--        - CLK source with higher number should be more precise.
--   0x24 = Number of available CLK and PPS sources (32b, RO):
--        - Lower half (16b) contains the number of available PPS sources.
--        - Higher half (16b) contains the number of available clock sources.
--
--   Registers accessible through CTRL_REG and MI_DATA_REG only:
--   ===========================================================
--   - INCR_VAL_REG = Incremental value register (39b, RW)
--   - REALTIME_REG = Real-time register (96b, RW)
--   - PPS_REG = Register PPS (96b, RO)
--
entity TSU_GEN is
generic (
    -- Selects smarter DSPs arrangement for timestamp format conversion.
    -- Meanings of supported values: true = use multiplication in DSPs composed
    -- of adds and shifts; false = look at TS_MULT_USE_DSP
    TS_MULT_SMART_DSP            : boolean := true;
    -- Selects whether to use DSPs for timestamp format conversion:
    -- Meanings of supported values: true = use multipliers in DSPs;
    -- false = disable DSPs, use logic
    TS_MULT_USE_DSP              : boolean := true;
    -- Width of PPS select signal: Used value must be in range from 1 to 16.
    -- Should be greater or equal to base 2 logarithm from number of available
    -- PPS sources.
    PPS_SEL_WIDTH                : integer := 8;
    -- Width of main CLK select signal: Used value must be in range from 1 to 16.
    -- Should be greater or equal to base 2 logarithm from number of available
    -- CLK sources.
    CLK_SEL_WIDTH                : integer := 8;
    -- Name of selected FPGA device
    DEVICE                       : string  := "ULTRASCALE"
);
port (
    -- =========================================================================
    --  Signals for MI32 interface
    -- =========================================================================

    -- Clock for MI32 interface.
    MI_CLK   	  : in  std_logic;
    -- Synchronious reset with MI_CLK.
    MI_RESET 	  : in  std_logic;
    -- MI bus: data from master to slave (write data)
    MI_DWR        : in  std_logic_vector(31 downto 0);
    -- MI bus: slave address
    MI_ADDR       : in  std_logic_vector(31 downto 0);
    -- MI bus: read request
    MI_RD         : in  std_logic;
    -- MI bus: write request
    MI_WR         : in  std_logic;
    -- MI bus: byte enable, not supported in this component!
    MI_BE         : in  std_logic_vector(3 downto 0);
    -- MI bus: data from slave to master (read data)
    MI_DRD        : out std_logic_vector(31 downto 0);
    -- MI bus: ready of slave module
    MI_ARDY       : out std_logic;
    -- MI bus: valid of MI_DRD data signal
    MI_DRDY       : out std_logic;

    -- =========================================================================
    --  PPS signal interface
    -- =========================================================================

    -- Input PPS_N signal
    PPS_N         : in std_logic;
    -- Number of different PPS sources (on MI_CLK)
    PPS_SRC       : in std_logic_vector(15 downto 0);
    -- Select PPS source (on main CLK)
    PPS_SEL       : out std_logic_vector(max(PPS_SEL_WIDTH-1,0) downto 0);

    -- =========================================================================
    --  Main CLK signal interface
    -- =========================================================================

    -- Input CLK signal (main clock)
    CLK           : in  std_logic;
    -- Synchronious reset with main clock
    RESET         : in  std_logic;

    -- =========================================================================
    --  CLK signal configuration interface
    -- =========================================================================

    -- Frequency of input CLK signal (on MI_CLK)
    CLK_FREQ      : in  std_logic_vector(31 downto 0);
    -- Number of different CLK sources (on MI_CLK)
    CLK_SRC       : in std_logic_vector(15 downto 0);
    -- Select CLK source (on MI_CLK)
    CLK_SEL       : out std_logic_vector(max(CLK_SEL_WIDTH-1,0) downto 0);

    -- =========================================================================
    --  Output timestamp interface (on main CLK)
    -- =========================================================================

    -- Timestamp in fractional (old) format: Fractional part of timestamp
    -- represents number of xanoseconds (one xanosecond is 2^(-32) seconds).
    TS  	 	    : out std_logic_vector(63 downto 0);
    -- Timestamp in nanosecond (new) format: Fractional part of timestamp
    -- represents number of nanoseconds (one nanosecond is 10^(-9) seconds).
    -- Maximum number of nanoseconds is 999 999 999, therefor highest 2 bits of
    -- fractional part are unused.
    TS_NS 	    : out std_logic_vector(63 downto 0);
    -- Timestamp is valid in this cycle
    TS_DV	     : out std_logic
);
end entity;
