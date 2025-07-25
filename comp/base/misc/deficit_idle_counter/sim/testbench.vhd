-- testbench.vhd.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use std.env.all;
use std.textio.all;

library work;
use work.type_pack.all;
use work.math_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use std.textio.all;

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------
entity TESTBENCH is
end entity;
--! ----------------------------------------------------------------------------
--!                      Architecture declaration
--! ----------------------------------------------------------------------------
architecture BEHAVIORAL of TESTBENCH is

    constant CLK_PERIOD : time := 1 ns;
    constant PKT_CHANCE : natural := 100;

    constant PKTS         : natural := 4;
    constant PKT_SIZE     : natural := 2**12;
    constant GAP_SIZE     : natural := 12;
    constant ALIGN        : natural := 8;
    constant MIN_GAP_SIZE : natural := GAP_SIZE-4;

    signal clk          : std_logic;
    signal reset        : std_logic;

    signal rx_pkt_len     : slv_array_t     (PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal rx_pkt_vld     : std_logic_vector(PKTS-1 downto 0);
    signal rx_pkt_src_rdy : std_logic;
    signal rx_pkt_dst_rdy : std_logic; -- propagated from TX_PKT_DST_RDY

    signal tx_pkt_gap     : slv_array_t     (PKTS-1 downto 0)(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
    signal tx_pkt_vld     : std_logic_vector(PKTS-1 downto 0);
    signal tx_pkt_src_rdy : std_logic; -- propagated from RX_PKT_SRC_RDY
    signal tx_pkt_dst_rdy : std_logic;

begin

    uut : entity work.DEFICIT_IDLE_COUNTER
    generic map (
        PKTS         => PKTS,
        PKT_SIZE     => PKT_SIZE,
        GAP_SIZE     => GAP_SIZE,
        ALIGN        => ALIGN,
        MIN_GAP_SIZE => MIN_GAP_SIZE
    )
    port map (
        CLK   => clk,
        RESET => reset,

        RX_PKT_LEN     => rx_pkt_len,
        RX_PKT_VLD     => rx_pkt_vld,
        RX_PKT_SRC_RDY => rx_pkt_src_rdy,
        RX_PKT_DST_RDY => rx_pkt_dst_rdy,

        TX_PKT_GAP     => tx_pkt_gap,
        TX_PKT_VLD     => tx_pkt_vld,
        TX_PKT_SRC_RDY => tx_pkt_src_rdy,
        TX_PKT_DST_RDY => tx_pkt_dst_rdy
    );

    tx_pkt_dst_rdy <= '1';

    -- generating clock signal
    clk_pr : process
    begin
        clk <= '1';
        wait for CLK_PERIOD/2;
        clk <= '0';
        wait for CLK_PERIOD/2;
    end process;

    -- generating reset signal
    reset_pr : process
    begin
        reset <= '1';
        wait for CLK_PERIOD*2;
        reset <= '0';
        wait;
    end process;

    -- input generation
    input_pr : process
        variable s0 : integer := 11;
        variable s1 : integer := 15;
        variable x  : integer := 0;
        variable c  : unsigned(log2(PKT_SIZE+1)-1 downto 0) := to_unsigned(64,log2(PKT_SIZE+1));
    begin
        rx_pkt_src_rdy <= '0';

        wait for CLK_PERIOD/2;
        wait until reset /= '1';
        wait for CLK_PERIOD/2;

        -- Packets with size 64 B
        for i in 0 to 16-1 loop
            rx_pkt_len     <= (others => (others => 'X'));
            rx_pkt_vld     <= (others => '0');
            rx_pkt_src_rdy <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,x);
                if (x < PKT_CHANCE) then
                    rx_pkt_len(i)  <= std_logic_vector(to_unsigned(64,log2(PKT_SIZE+1)));
                    rx_pkt_vld(i)  <= '1';
                    rx_pkt_src_rdy <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        rx_pkt_src_rdy <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with size 65 B
        for i in 0 to 16-1 loop
            rx_pkt_len     <= (others => (others => 'X'));
            rx_pkt_vld     <= (others => '0');
            rx_pkt_src_rdy <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,x);
                if (x < PKT_CHANCE) then
                    rx_pkt_len(i)  <= std_logic_vector(to_unsigned(65,log2(PKT_SIZE+1)));
                    rx_pkt_vld(i)  <= '1';
                    rx_pkt_src_rdy <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        rx_pkt_src_rdy <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with size 71 B
        for i in 0 to 16-1 loop
            rx_pkt_len     <= (others => (others => 'X'));
            rx_pkt_vld     <= (others => '0');
            rx_pkt_src_rdy <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,x);
                if (x < PKT_CHANCE) then
                    rx_pkt_len(i)  <= std_logic_vector(to_unsigned(71,log2(PKT_SIZE+1)));
                    rx_pkt_vld(i)  <= '1';
                    rx_pkt_src_rdy <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        rx_pkt_src_rdy <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with incrementing size
        for i in 0 to 32-1 loop
            rx_pkt_len     <= (others => (others => 'X'));
            rx_pkt_vld     <= (others => '0');
            rx_pkt_src_rdy <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,x);
                if (x < PKT_CHANCE) then
                    rx_pkt_len(i)  <= std_logic_vector(c);
                    c              := c+1;
                    rx_pkt_vld(i)  <= '1';
                    rx_pkt_src_rdy <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        rx_pkt_src_rdy <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with random size B
        while (true) loop
            rx_pkt_len     <= (others => (others => 'X'));
            rx_pkt_vld     <= (others => '0');
            rx_pkt_src_rdy <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,x);
                if (x < PKT_CHANCE) then
                    randint(s0,s1,64,128,x);
                    rx_pkt_len(i)  <= std_logic_vector(to_unsigned(x,log2(PKT_SIZE+1)));
                    rx_pkt_vld(i)  <= '1';
                    rx_pkt_src_rdy <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        rx_pkt_src_rdy <= '0';
        wait for CLK_PERIOD*8;

        wait;
    end process;

end architecture;
