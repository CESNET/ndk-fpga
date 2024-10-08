-- altdpram_wrap_ent.vhd: altdpram wrapper
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity ALTDPRAM_WRAP is
    generic(
        DATA_WIDTH      : natural := 8;
        ADDR_WIDTH      : natural := 5;
        RAM_TYPE        : string  := "MLAB";
        RDW_CONSTRAINED : boolean := True;
        OUTPUT_REG      : boolean := False;
        DEVICE          : string  := "STRATIX10"
    );
    port(
        DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        INCLOCK   : in  std_logic;
        RDADDRESS : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        WRADDRESS : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        WREN      : in  std_logic;
        Q         : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;
