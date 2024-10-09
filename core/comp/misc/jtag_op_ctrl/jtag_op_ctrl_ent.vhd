-- jtag_op_ctrl_ent.vhd: JTAG-Over-Protocol controller entity
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity JTAG_OP_CTRL is
    generic(
        -- MI Address word width in bits.
        MI_ADDR_WIDTH : natural := 32;
        -- MI Data word width in bits.
        MI_DATA_WIDTH : natural := 32;
        -- MI Metadata word width in bits.
        MI_META_WIDTH : natural := 1;
        -- Enables JTAG-over-protocol IP.
        JOP_ENABLE    : boolean := True;
        -- Target device (Intel only).
        DEVICE        : string  := "AGILEX"
    );
    port(
        -- =================
        --  Clock and Reset
        -- =================

        -- 200 MHz
        USER_CLK   : in  std_logic;
        USER_RESET : in  std_logic;

        -- Operating frequency of the JTAG-over-protocol IP must be 100 MHz or lower.
        JOP_CLK    : in  std_logic;
        JOP_RESET  : in  std_logic;

        -- ==============
        --  MI interface
        -- ==============

        -- Address
        MI_ADDR  : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        -- Input Data
        MI_DWR   : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- Input Metadata
        MI_MWR   : in  std_logic_vector(MI_META_WIDTH-1 downto 0) := (others => '0');
        -- Byte Enable
        MI_BE    : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        -- Write Request
        MI_WR    : in  std_logic;
        -- Read Request
        MI_RD    : in  std_logic;
        -- Address Ready
        MI_ARDY  : out std_logic;
        -- Output Data
        MI_DRD   : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- Data Ready
        MI_DRDY  : out std_logic
    );
end entity;
