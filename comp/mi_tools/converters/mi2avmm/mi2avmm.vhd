-- mi2avmm.vhd : MI to Avalon MM interface converter
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- This component converts MI interface to Avalon Memory-Mapped (Avalon-MM) interface.
-- In the current implementation these are just directly connected wires and one not gate.
entity MI2AVMM is

    generic(
        -- Data word width in bits
        DATA_WIDTH : natural := 32;
        -- Address word width in bits
        ADDR_WIDTH : natural := 32;
        -- Meta word width in bits
        META_WIDTH : natural := 2;
        -- Target device (Intel only) (UNUSED)
        DEVICE     : string  := "AGILEX"
    );

    port(
        -- Clock and Reset

        CLK   : in  std_logic;
        RESET : in  std_logic;

        -- MI interface

        MI_DWR  : in  std_logic_vector(DATA_WIDTH-1 downto 0);     -- Input Data
        MI_MWR  : in  std_logic_vector(META_WIDTH-1 downto 0);     -- Input Metadata (not used yet)
        MI_ADDR : in  std_logic_vector(ADDR_WIDTH-1 downto 0);     -- Address
        MI_RD   : in  std_logic;                                   -- Read Request
        MI_WR   : in  std_logic;                                   -- Write Request
        MI_BE   : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0); -- Byte Enable
        MI_DRD  : out std_logic_vector(DATA_WIDTH-1 downto 0);     -- Output Data
        MI_ARDY : out std_logic;                                   -- Address Ready
        MI_DRDY : out std_logic;                                   -- Data Ready

        -- Avalon MM interface

        AVMM_ADDRESS       : out std_logic_vector(ADDR_WIDTH-1 downto 0);     -- Address
        AVMM_WRITE         : out std_logic;                                   -- Write Request
        AVMM_READ          : out std_logic;                                   -- Read Request
        AVMM_BYTEENABLE    : out std_logic_vector((DATA_WIDTH/8)-1 downto 0); -- Byte Enable
        AVMM_WRITEDATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);     -- Output Data
        AVMM_READDATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);     -- Input Data
        AVMM_READDATAVALID : in  std_logic;                                   -- Input Data Valid
        AVMM_WAITREQUEST   : in  std_logic                                    -- Wait Request
    );

end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of MI2AVMM is

begin

    AVMM_ADDRESS    <= MI_ADDR;
    AVMM_WRITE      <= MI_WR;
    AVMM_READ       <= MI_RD;
    AVMM_BYTEENABLE <= MI_BE;
    AVMM_WRITEDATA  <= MI_DWR;
    MI_DRD          <= AVMM_READDATA;
    MI_DRDY         <= AVMM_READDATAVALID;
    MI_ARDY         <= not AVMM_WAITREQUEST;

end architecture;
