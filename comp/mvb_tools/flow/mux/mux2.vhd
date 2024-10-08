-- mux2.vhd: Simple MVB MUX
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MVB_MUX2 is
    generic (
        MVB_ITEMS       : natural := 1;
        DATA_WIDTH      : natural := 64;
        FIFO_DEPTH      : natural := 2;
        DEVICE          : string  := "ULTRASCALE"
    );
    port (
        -- Clock signal
        CLK                     : in    std_logic;
        -- Synchronous reset with CLK
        RESET                   : in    std_logic;

        -- RX MVB interface 0
        RX0_DATA        : in std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        RX0_VLD         : in std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX0_SRC_RDY     : in std_logic;
        RX0_DST_RDY     : out std_logic;

        -- RX MVB interface 1
        RX1_DATA        : in std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        RX1_VLD         : in std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX1_SRC_RDY     : in std_logic;
        RX1_DST_RDY     : out std_logic;

        -- TX MVB interface
        TX_DATA        : out std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        TX_VLD         : out std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX_SRC_RDY     : out std_logic;
        TX_DST_RDY     : in std_logic;

        -- SELECT MVB interface
        RX_SEL_DATA             : in std_logic;
        RX_SEL_VLD              : in std_logic;
        RX_SEL_SRC_RDY          : in std_logic;
        RX_SEL_DST_RDY          : out std_logic
    );
end entity;

architecture behavioral of MVB_MUX2 is
    signal rx_dst_rdies : std_logic_vector(2 - 1 downto 0);
begin

    gen_mux_i : entity work.GEN_MVB_MUX
    generic map (
        MVB_ITEMS   => MVB_ITEMS,
        DATA_WIDTH  => DATA_WIDTH,
        MUX_WIDTH   => 2,

        FIFO_DEPTH  => FIFO_DEPTH,
        DEVICE      => DEVICE
    ) port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => RX1_DATA & RX0_DATA,
        RX_VLD      => RX1_VLD & RX0_VLD,
        RX_SRC_RDY  => RX1_SRC_RDY & RX0_SRC_RDY,
        RX_DST_RDY  => rx_dst_rdies,

        TX_DATA     => TX_DATA,
        TX_VLD      => TX_VLD,
        TX_SRC_RDY  => TX_SRC_RDY,
        TX_DST_RDY  => TX_DST_RDY,

        RX_SEL_DATA     => "" & RX_SEL_DATA,
        RX_SEL_VLD      => "" & RX_SEL_VLD,
        RX_SEL_SRC_RDY  => RX_SEL_SRC_RDY,
        RX_SEL_DST_RDY  => RX_SEL_DST_RDY
    );

    RX0_DST_RDY <= rx_dst_rdies(0);
    RX1_DST_RDY <= rx_dst_rdies(1);
end architecture;
