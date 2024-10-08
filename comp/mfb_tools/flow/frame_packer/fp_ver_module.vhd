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

--NOTE: This component is used for verification due to unpredictable latency of some components
entity FP_VER_MOD is
    generic(
        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        FIFO_DEPTH          :natural := 512;
        USR_RX_PKT_SIZE_MAX :natural := 64;
        USR_RX_PKT_SIZE_MIN :natural := 2**10
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;
        --FIFO read enable
        RX_READ_EN  : in std_logic;

        RX_PKT_NUM          : in std_logic_vector(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
        RX_PKT_NUM_SRC_RDY  : in std_logic;

        --End of packets at FRAME_SHIFTER input
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

    signal pkt_cnt          : unsigned(MAX_PKT_NUM - 1 downto 0):= (others => '0');
    signal eve_cnt_reg      : unsigned(MAX_PKT_NUM - 1 downto 0);

    signal cpt_fifox_do     : std_logic_vector(MAX_PKT_NUM - 1 downto 0);
    signal cpt_fifox_rd     : std_logic;
    signal cpt_fifox_empty  : std_logic;

    signal cnt_load         : std_logic;

    signal small_packets_cnt    : unsigned(30 downto 0);
    signal big_packets_cnt      : unsigned(30 downto 0);

    signal output_pkt_cnt       : unsigned(30 downto 0);

    signal unit_fifo_di         : std_logic_vector(MAX_PKT_NUM - 1 downto 0);
    signal unit_fifo_do         : std_logic_vector(MAX_PKT_NUM - 1 downto 0);
    signal unit_fifo_rd         : std_logic;
    signal number_of_packets    : unsigned(MAX_PKT_NUM - 1 downto 0);

    signal request_fifo_do      : std_logic_vector(MAX_PKT_NUM - 1 downto 0);
    signal request_fifo_rd      : std_logic;
    signal request_fifo_empty   : std_logic;

    signal sp_pkt_cnt_prev      : unsigned(MAX_PKT_NUM - 1 downto 0);
    signal sp_pkt_cnt           : unsigned(MAX_PKT_NUM - 1 downto 0);
    signal req_cnt_load         : std_logic;

    signal capt_fifo_wr_en      : std_logic;

    signal unit_fifo_status     : std_logic_vector(log2(2048) downto 0);
    signal request_fifo_status  : std_logic_vector(log2(2048) downto 0);

begin

    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                eve_cnt_reg <= (others => '0');
            elsif (RX_SP_EOF_SRC_RDY = '1') then
                if (RX_SP_EOF = '0') then
                    eve_cnt_reg     <= to_unsigned(count_ones(RX_EOF), MAX_PKT_NUM) + eve_cnt_reg;
                else
                    eve_cnt_reg     <= (others => '0');
                end if;
            end if;
        end if;
    end process;

    unit_fifo_di    <= std_logic_vector(to_unsigned(count_ones(RX_EOF), MAX_PKT_NUM) + eve_cnt_reg);

    unit_fifo_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => MAX_PKT_NUM,
        ITEMS               => 2048,
        RAM_TYPE            => "AUTO",
        ALMOST_FULL_OFFSET  => 1     ,
        ALMOST_EMPTY_OFFSET => 1     ,
        FAKE_FIFO           => false
    )
    port map(
        CLK    => CLK  ,
        RESET  => RST,

        DI     => unit_fifo_di,
        WR     => RX_SP_EOF and RX_SP_EOF_SRC_RDY,
        FULL   => open,
        AFULL  => open,
        STATUS => unit_fifo_status,

        DO     => unit_fifo_do,
        RD     => unit_fifo_rd,
        EMPTY  => open,
        AEMPTY => open
    );

    request_fifo_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => MAX_PKT_NUM,
        ITEMS               => 2048,
        RAM_TYPE            => "AUTO",
        ALMOST_FULL_OFFSET  => 1     ,
        ALMOST_EMPTY_OFFSET => 1     ,
        FAKE_FIFO           => false
    )
    port map(
        CLK    => CLK  ,
        RESET  => RST,

        DI     => resize(RX_PKT_NUM, MAX_PKT_NUM),
        WR     => RX_PKT_NUM_SRC_RDY,
        FULL   => open,
        AFULL  => open,
        STATUS => request_fifo_status,

        DO     => request_fifo_do,
        RD     => request_fifo_rd,
        EMPTY  => request_fifo_empty,
        AEMPTY => open
    );

    process(all)
    begin
        if request_fifo_empty = '0' and sp_pkt_cnt = 0 then
            req_cnt_load    <= '1';
            request_fifo_rd <= '1';
        else
            req_cnt_load    <= '0';
            request_fifo_rd <= '0';
        end if;
    end process;

    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                sp_pkt_cnt <= (others => '0');
            elsif req_cnt_load = '1' then
                sp_pkt_cnt          <= unsigned(request_fifo_do);
                number_of_packets   <= (others => '0');
            else
                if sp_pkt_cnt /= 0 then
                    sp_pkt_cnt          <= sp_pkt_cnt - unsigned(unit_fifo_do);
                    number_of_packets   <= number_of_packets + unsigned(unit_fifo_do);
                end if;
            end if;
        end if;
    end process;

    process(all)
    begin
        unit_fifo_rd    <= '0';
        if sp_pkt_cnt /= 0 then
            unit_fifo_rd    <= '1';
        end if;
    end process;

    process(all)
    begin
        if rising_edge(CLK) then
            sp_pkt_cnt_prev <= sp_pkt_cnt;
        end if;
    end process;

    capt_fifo_wr_en     <= '1' when sp_pkt_cnt = 0 and sp_pkt_cnt_prev /= 0 else '0';

    --  Capture FIFO
    capt_fifo_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => MAX_PKT_NUM,
        ITEMS               => 512,
        RAM_TYPE            => "AUTO",
        ALMOST_FULL_OFFSET  => 1     ,
        ALMOST_EMPTY_OFFSET => 1     ,
        FAKE_FIFO           => false
    )
    port map(
        CLK    => CLK  ,
        RESET  => RST,

        DI     => std_logic_vector(number_of_packets),
        WR     => capt_fifo_wr_en,
        FULL   => open,
        AFULL  => open,
        STATUS => open,

        DO     => cpt_fifox_do   ,
        RD     => cpt_fifox_rd   ,
        EMPTY  => cpt_fifox_empty,
        AEMPTY => open
    );

    -- FIFO controller
    process(all)
    begin
        if cpt_fifox_empty = '0' and pkt_cnt = 0 then
            cnt_load        <= '1';
            cpt_fifox_rd    <= '1';
        else
            cnt_load        <= '0';
            cpt_fifox_rd    <= '0';
        end if;
    end process;

    -- Read
    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                pkt_cnt <= (others => '0');
            elsif cnt_load = '1' then
                pkt_cnt <= unsigned(cpt_fifox_do);
            elsif pkt_cnt /= 0 then
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
    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                output_pkt_cnt <= (others => '0');
            elsif VER_EOF = '1' then
                output_pkt_cnt <= output_pkt_cnt + 1;
            end if;
        end if;
    end process;

    debug_small_p:process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                small_packets_cnt   <= (others => '0');
            elsif ((or(RX_EOF) = '1') and (RX_EOF_SRC_RDY = '1')) then
                small_packets_cnt   <= small_packets_cnt + to_unsigned(count_ones(RX_EOF), small_packets_cnt'length);
            end if;
        end if;
    end process;

    debug_big_p:process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                big_packets_cnt   <= (others => '0');
            elsif (RX_SP_EOF = '1' and RX_SP_EOF_SRC_RDY = '1') then
                big_packets_cnt   <= big_packets_cnt + 1;
            end if;
        end if;
    end process;
 end architecture;
