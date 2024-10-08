-- mvb_slr_crossing.vhd: MVB SLR Crossing
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity MVB_SLR_CROSSING is
generic(
    MVB_ITEMS       : integer := 2;
    MVB_ITEM_WIDTH  : integer := 128;

    USE_OUTREG      : boolean:= true;
    FAKE_CROSSING   : boolean:= false;
    DEVICE          : string := "ULTRASCALE"
);
port(
    CLK        : in std_logic;

    RX_RESET   : in  std_logic;
    RX_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    RX_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    TX_RESET   : in  std_logic;
    TX_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    TX_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic
);
end entity;

architecture arch of MVB_SLR_CROSSING is
    constant CROSSING_WIDTH        : integer := MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS;
    signal crossing_in_data        : std_logic_vector(CROSSING_WIDTH-1 downto 0);
    signal crossing_in_src_rdy     : std_logic;
    signal crossing_in_dst_rdy     : std_logic;
    signal crossing_out_data       : std_logic_vector(CROSSING_WIDTH-1 downto 0);
    signal crossing_out_src_rdy    : std_logic;
    signal crossing_out_dst_rdy    : std_logic;
begin
    crossing_in_data     <= RX_DATA & RX_VLD;
    crossing_in_src_rdy  <= RX_SRC_RDY;
    RX_DST_RDY           <= crossing_in_dst_rdy;

    TX_DATA              <= crossing_out_data(MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS-1 downto MVB_ITEMS);
    TX_VLD               <= crossing_out_data(MVB_ITEMS-1 downto 0);
    TX_SRC_RDY           <= crossing_out_src_rdy;
    crossing_out_dst_rdy <= TX_DST_RDY;

    SLR_CROSSING_I : entity work.SLR_CROSSING
    generic map(
        DATA_WIDTH      => CROSSING_WIDTH,
        USE_OUTREG      => USE_OUTREG,
        FAKE_CROSSING   => FAKE_CROSSING,
        DEVICE          => DEVICE
    ) port map(
        CLK         => CLK,
        IN_RESET     => RX_RESET,
        IN_DATA      => crossing_in_data,
        IN_SRC_RDY   => crossing_in_src_rdy,
        IN_DST_RDY   => crossing_in_dst_rdy,
        OUT_RESET    => TX_RESET,
        OUT_DATA     => crossing_out_data,
        OUT_SRC_RDY  => crossing_out_src_rdy,
        OUT_DST_RDY  => crossing_out_dst_rdy
    );
end architecture;
