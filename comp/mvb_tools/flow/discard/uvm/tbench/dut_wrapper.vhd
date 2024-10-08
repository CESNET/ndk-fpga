-- dut_wrapper.vhd
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;

entity DUT_WRAPPER is
    generic(
        -- Number of items
        ITEMS      : natural := 4;
        -- Item width in bits
        ITEM_WIDTH : natural := 32;
        -- Optional output register
        OUTPUT_REG : boolean := True
    );
    port(
        -- Clock input
        CLK         : in  std_logic;
        -- Reset input synchronized with CLK
        RESET       : in  std_logic;

        -- RX MVB: data word with MVB items
        RX_DATA    : in  std_logic_vector(ITEMS*(ITEM_WIDTH+1)-1 downto 0);
        -- RX MVB: valid of each MVB item
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        -- RX MVB: source ready
        RX_SRC_RDY : in  std_logic;
        -- RX MVB: destination ready
        RX_DST_RDY : out std_logic;

        -- TX MVB: Data word with MVB items
        TX_DATA     : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- TX MVB: valid of each MVB item
        TX_VLD      : out std_logic_vector(ITEMS-1 downto 0);
        -- TX MVB: source ready
        TX_SRC_RDY  : out std_logic;
        -- TX MVB: destination ready
        TX_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of DUT_WRAPPER is

    signal rx_data_arr     : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH+1-1 downto 0);
    signal rx_data_raw_arr : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal rx_discard      : std_logic_vector(ITEMS-1 downto 0);

begin

    rx_data_arr <= slv_array_deser(RX_DATA,ITEMS,ITEM_WIDTH+1);

    rx_data_arr_g: for i in 0 to ITEMS-1 generate
        rx_data_raw_arr(i) <= rx_data_arr(i)(ITEM_WIDTH+1-1 downto 1);
        rx_discard(i)      <= rx_data_arr(i)(0);
    end generate;

    dut_i : entity work.MVB_DISCARD
    generic map(
        ITEMS      => ITEMS,
        ITEM_WIDTH => ITEM_WIDTH,
        OUTPUT_REG => OUTPUT_REG
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        RX_DATA     => slv_array_ser(rx_data_raw_arr),
        RX_DISCARD  => rx_discard,
        RX_VLD      => RX_VLD,
        RX_SRC_RDY  => RX_SRC_RDY,
        RX_DST_RDY  => RX_DST_RDY,

        TX_DATA     => TX_DATA,
        TX_VLD      => TX_VLD,
        TX_SRC_RDY  => TX_SRC_RDY,
        TX_DST_RDY  => TX_DST_RDY
    );

end architecture;
