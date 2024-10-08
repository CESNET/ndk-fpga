-- demux.vhd: General width MVB DEMUX
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

entity MVB_DEMUX2 is
    generic (
        MVB_ITEMS       : natural := 1;
        DATA_WIDTH      : natural := 64;
        VERSION         : string := "register";

        OUTPUT_REG      : boolean := False
    );
    port (
        -- Clock signal
        CLK             : in    std_logic;
        -- Synchronous reset with CLK
        RESET           : in    std_logic;

        -- Input MVB interface with select signal for each item
        RX_DATA         : in    std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        RX_SEL          : in    std_logic_vector(MVB_ITEMS * max(1, log2(2)) - 1 downto 0);
        RX_VLD          : in    std_logic_vector(MVB_ITEMS - 1 downto 0);
        RX_SRC_RDY      : in    std_logic;
        RX_DST_RDY      : out   std_logic;

        -- Output MVB interface 0
        TX0_DATA        : out   std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        TX0_VLD         : out   std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX0_SRC_RDY     : out   std_logic;
        TX0_DST_RDY     : in    std_logic;

        -- Output MVB interface 1
        TX1_DATA        : out   std_logic_vector(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
        TX1_VLD         : out   std_logic_vector(MVB_ITEMS - 1 downto 0);
        TX1_SRC_RDY     : out   std_logic;
        TX1_DST_RDY     : in    std_logic
    );
end entity;

architecture behavioral of MVB_DEMUX2 is

    signal tx_data_int : std_logic_vector(2 * MVB_ITEMS * DATA_WIDTH - 1 downto 0);
    signal tx_vld_int : std_logic_vector(2 * MVB_ITEMS - 1 downto 0);
    signal tx_src_rdy_int : std_logic_vector(2-1 downto 0);
    signal tx_dst_rdy_int : std_logic_vector(2-1 downto 0);

begin

    gen_demux_e : entity work.GEN_MVB_DEMUX
    generic map (
        MVB_ITEMS   => MVB_ITEMS,
        DATA_WIDTH  => DATA_WIDTH,
        DEMUX_WIDTH => 2,
        VERSION     => VERSION,
        OUTPUT_REG  => OUTPUT_REG
    ) port map (
        CLK         => CLK,
        RESET       => RESET,

        RX_DATA     => RX_DATA,
        RX_SEL      => RX_SEL,
        RX_VLD      => RX_VLD,
        RX_SRC_RDY  => RX_SRC_RDY,
        RX_DST_RDY  => RX_DST_RDY,

        TX_DATA     => tx_data_int,
        TX_VLD      => tx_vld_int,
        TX_SRC_RDY  => tx_src_rdy_int,
        TX_DST_RDY  => tx_dst_rdy_int
    );

    TX0_DATA <= tx_data_int(MVB_ITEMS * DATA_WIDTH - 1 downto 0);
    TX0_VLD <= tx_vld_int(MVB_ITEMS - 1 downto 0);
    TX0_SRC_RDY <= tx_src_rdy_int(0);
    tx_dst_rdy_int(0) <= TX0_DST_RDY;

    TX1_DATA <= tx_data_int(2 * MVB_ITEMS * DATA_WIDTH - 1 downto MVB_ITEMS * DATA_WIDTH);
    TX1_VLD <= tx_vld_int(2 * MVB_ITEMS - 1 downto MVB_ITEMS);
    TX1_SRC_RDY <= tx_src_rdy_int(1);
    tx_dst_rdy_int(1) <= TX1_DST_RDY;

end architecture;
