-- sdm_ctrl_ent.vhd: SDM controller entity
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity SDM_CTRL is
    generic(
        -- Data word width in bits
        DATA_WIDTH   : natural := 32;
        -- Address word width in bits
        ADDR_WIDTH   : natural := 32;
        -- Read CHIP_ID after reset
        READ_CHIP_ID : boolean := true;
        -- Target device (Intel only)
        DEVICE       : string  := "AGILEX"
    );
    port(
        -- Clock and Reset
        CLK   : in  std_logic;
        RESET : in  std_logic;

        -- MI interface
        MI_DWR   : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        MI_ADDR  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        MI_RD    : in  std_logic;
        MI_WR    : in  std_logic;
        MI_BE    : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
        MI_DRD   : out std_logic_vector(DATA_WIDTH-1 downto 0);
        MI_ARDY  : out std_logic;
        MI_DRDY  : out std_logic;

        -- CHIP ID
        CHIP_ID     : out std_logic_vector(64-1 downto 0);
        CHIP_ID_VLD : out std_logic := '0'
    );
end entity;

