-- crc_gen_ent.vhd: CRC generator
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_CRC_GEN is
    generic(
        REGIONS      : natural := 4; -- any positive value
        REGION_SIZE  : natural := 8; -- any positive value
        BLOCK_SIZE   : natural := 8; -- any positive value
        ITEM_WIDTH   : natural := 8; -- must be 8
        CRC_END_IMPL : string  := "TREE";
        DEVICE       : string  := "STRATIX10"
    );
    port(
        -- CLOCK AND RESET
        CLK         : in  std_logic;
        RESET       : in  std_logic;
        -- INPUT MFB DATA INTERFACE
        RX_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY  : in  std_logic;
        -- OUTPUT MVB CRC INTERFACE
        CRC_DATA    : out std_logic_vector(REGIONS*32-1 downto 0);
        CRC_VLD     : out std_logic_vector(REGIONS-1 downto 0);
        CRC_SRC_RDY : out std_logic
    );
end entity;
