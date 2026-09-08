-- mvb_reordering_wrapper.vhd: Wrapper for MVB_REORDERING to enable SystemVerilog UVM verification
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Alena Drlickova <drlickova@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- This wrapper provides a SystemVerilog-compatible interface by ensuring
-- REORDER_KEY port is at least 1 bit wide. For ITEMS=1, the internal
-- REORDER_KEY is null-range (0 bits), but the external wrapper port
-- is 1 bit to satisfy SystemVerilog connection requirements.

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MVB_REORDERING_WRAPPER is
    generic (
        ITEMS         : natural := 5;
        ITEM_WIDTH    : natural := 64;
        OUT_REG_EN    : boolean := True;
        REORDERING_EN : boolean := True
    );
    port (
        CLK         : in  std_logic;
        RESET       : in  std_logic;
        -- MVB RX INTERFACE
        RX_DATA     : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        RX_VLD      : in  std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY  : in  std_logic;
        RX_DST_RDY  : out std_logic;
        -- MVB TX INTERFACE
        TX_DATA     : out  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD      : out  std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY  : out  std_logic;
        TX_DST_RDY  : in  std_logic;
        -- KEYS FOR REORDERING
        REORDER_KEY : in  std_logic_vector(max(1, ITEMS*log2(ITEMS))-1 downto 0)
    );
end entity;

architecture WRAPPER of MVB_REORDERING_WRAPPER is

    signal internal_reorder_key : std_logic_vector(ITEMS*log2(ITEMS)-1 downto 0);

begin

    -- Connect internal signal to DUT
    -- Null-range connection for ITEMS=1
    dut_u : entity work.MVB_REORDERING
    generic map (
        ITEMS         => ITEMS,
        ITEM_WIDTH    => ITEM_WIDTH,
        OUT_REG_EN    => OUT_REG_EN,
        REORDERING_EN => REORDERING_EN
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,
        -- MVB RX INTERFACE
        RX_DATA     => RX_DATA,
        RX_VLD      => RX_VLD,
        RX_SRC_RDY  => RX_SRC_RDY,
        RX_DST_RDY  => RX_DST_RDY,
        -- MVB TX INTERFACE
        TX_DATA     => TX_DATA,
        TX_VLD      => TX_VLD,
        TX_SRC_RDY  => TX_SRC_RDY,
        TX_DST_RDY  => TX_DST_RDY,
        -- KEYS FOR REORDERING
        REORDER_KEY => internal_reorder_key
    );

    gen_connect : if ITEMS > 1 generate
        internal_reorder_key <= REORDER_KEY;
    end generate;

end architecture;
