-- fp_ver_module.vhd: Verification support module for frame_packer
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- NOTE: This component is used for verification due to unpredictable latency of some components
entity FP_VER_MOD is
    generic (
        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        FIFO_DEPTH          : natural := 512;
        USR_RX_PKT_SIZE_MAX : natural := 64;
        USR_RX_PKT_SIZE_MIN : natural := 2**10
    );
    port (
        CLK         : in std_logic;
        RST         : in std_logic;
        -- FIFO read enable
        RX_READ_EN  : in std_logic;

        RX_PKT_NUM          : in std_logic_vector(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
        RX_PKT_NUM_SRC_RDY  : in std_logic;

        -- End of packets at FRAME_SHIFTER input
        RX_EOF              : in std_logic_vector(MFB_REGIONS - 1 downto 0);
        RX_EOF_SRC_RDY      : in std_logic;
        RX_SP_EOF           : in std_logic;
        RX_SP_EOF_SRC_RDY   : in std_logic;

        -- Signals for verification - MVB
        VER_EOF     : out std_logic;
        VER_LAST    : out std_logic;
        VER_VLD     : out std_logic;
        VER_SRC_RDY : out std_logic;
        VER_DST_RDY : out std_logic
    );
end entity;

architecture FULL of FP_VER_MOD is
    constant MAX_PKT_NUM    : natural := 30;

    signal pkt_cnt          : unsigned(MAX_PKT_NUM - 1 downto 0) := (others => '0');

    signal cpt_fifox_do     : std_logic_vector(MAX_PKT_NUM - 1 downto 0);
    signal cpt_fifox_rd     : std_logic;
    signal cpt_fifox_empty  : std_logic;

    signal cnt_load         : std_logic;

    signal small_packets_cnt    : unsigned(30 downto 0);
    signal big_packets_cnt      : unsigned(30 downto 0);

    signal output_pkt_cnt       : unsigned(30 downto 0);

begin

    -- Number of packets of each SuperPacket read from the SPKT_LNG unit
    capt_fifo_i : entity work.FIFOX
    generic map (
        DATA_WIDTH          => MAX_PKT_NUM,
        ITEMS               => 512,
        RAM_TYPE            => "AUTO",
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 1,
        FAKE_FIFO           => false
    )
    port map (
        CLK    => CLK,
        RESET  => RST,

        DI     => std_logic_vector(resize(unsigned(RX_PKT_NUM), MAX_PKT_NUM)),
        WR     => RX_PKT_NUM_SRC_RDY,
        FULL   => open,
        AFULL  => open,
        STATUS => open,

        DO     => cpt_fifox_do,
        RD     => cpt_fifox_rd,
        EMPTY  => cpt_fifox_empty,
        AEMPTY => open
    );

    -- FIFO controller
    process (all)
    begin
        if (cpt_fifox_empty = '0' and pkt_cnt = 0) then
            cnt_load        <= '1';
            cpt_fifox_rd    <= '1';
        else
            cnt_load        <= '0';
            cpt_fifox_rd    <= '0';
        end if;
    end process;

    -- Read
    process (all)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                pkt_cnt <= (others => '0');
            elsif (cnt_load = '1') then
                pkt_cnt <= unsigned(cpt_fifox_do);
            elsif (pkt_cnt /= 0) then
                pkt_cnt <= pkt_cnt - 1;
            end if;
        end if;
    end process;

    VER_EOF     <= '1' when pkt_cnt /= 0 else '0';
    VER_VLD     <= '1' when pkt_cnt /= 0 else '0';
    VER_SRC_RDY <= '1' when pkt_cnt /= 0 else '0';
    VER_DST_RDY <= '1' when pkt_cnt /= 0 else '0';
    VER_LAST    <= '1' when pkt_cnt = 1 else '0';

    -- Debug Counters
    process (all)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                output_pkt_cnt <= (others => '0');
            elsif (VER_EOF = '1') then
                output_pkt_cnt <= output_pkt_cnt + 1;
            end if;
        end if;
    end process;

    debug_small_p : process (all)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                small_packets_cnt   <= (others => '0');
            elsif ((or(RX_EOF) = '1') and (RX_EOF_SRC_RDY = '1')) then
                small_packets_cnt   <= small_packets_cnt + to_unsigned(count_ones(RX_EOF), small_packets_cnt'length);
            end if;
        end if;
    end process;

    debug_big_p : process (all)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                big_packets_cnt   <= (others => '0');
            elsif (RX_SP_EOF = '1' and RX_SP_EOF_SRC_RDY = '1') then
                big_packets_cnt   <= big_packets_cnt + 1;
            end if;
        end if;
    end process;
end architecture;
