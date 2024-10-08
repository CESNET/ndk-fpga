-- testbench.vhd: Testbench for elastic FIFO
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity TESTBENCH is
end entity;

architecture behavioral of TESTBENCH is
    constant WR_CLK_PER : time := 10ns;
    constant RD_CLK_PER : time := 10.2ns;

    constant BLOCK_WIDTH : natural := 64;
    constant BLOCK_COUNT : natural := 4;
    constant DIN_WIDTH   : natural := BLOCK_COUNT * BLOCK_WIDTH;

    signal wr_clk   : std_logic;
    signal rd_clk   : std_logic;
    signal wr_ce    : std_logic;
    signal rd_ce    : std_logic;

    signal rst      : std_logic;

    signal data_in  : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal aux_in   : std_logic_vector(DIN_WIDTH / 8 - 1 downto 0);
    signal mask_in  : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    signal mask_out : std_logic_vector(BLOCK_COUNT - 1 downto 0);
    signal data_out : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal aux_out  : std_logic_vector(DIN_WIDTH / 8 - 1 downto 0);

begin
    -- WR_CLK generation
    wr_clk_gen_p : process
    begin
        wr_clk <= '1';
        wait for WR_CLK_PER / 2;
        wr_clk <= '0';
        wait for WR_CLK_PER / 2;
    end process;

    -- RD_CLK generation
    rd_clk_gen_p : process
    begin
        rd_clk <= '1';
        wait for RD_CLK_PER / 2;
        rd_clk <= '0';
        wait for RD_CLK_PER / 2;
    end process;

    wr_tb_p : process

        procedure send_data(data : std_logic_vector(DIN_WIDTH - 1 downto 0);
                            aux  : std_logic_vector(DIN_WIDTH / 8 - 1 downto 0);
                            mask : std_logic_vector(BLOCK_COUNT - 1 downto 0)) is
        begin
            data_in <= data;
            aux_in <= aux;
            mask_in <= mask;
            wait until rising_edge(wr_clk);
        end;

    begin

        rst <= '1';
        data_in <= (others => '0');
        aux_in <= (others => '0');
        mask_in <= (others => '0');
        wr_ce <= '1';
        wait until rising_edge(wr_clk);
        rst <= '0';
        for i in 0 to 7 loop
            wait until rising_edge(wr_clk);
        end loop;
        send_data(x"3333333333333333222222222222222211111111111111110000000000000000", x"33221100", "1100");
        wr_ce <= '0';
        send_data(x"7777777777777777666666666666666655555555555555554444444444444444", x"77665544", "1100");
        wr_ce <= '1';
        send_data(x"BBBBBBBBBBBBBBBBAAAAAAAAAAAAAAAA99999999999999998888888888888888", x"BBAA9988", "1100");
        send_data(x"FFFFfFFFFFFFFFFFEEEEEEEEEEEEEEEEDDDDDDDDDDDDDDDDCCCCCCCCCCCCCCCC", x"FFEEDDCC", "1100");
        send_data(x"3333333333333333222222222222222211111111111111110000000000000000", x"33221100", "0000");
        send_data(x"7777777777777777666666666666666655555555555555554444444444444444", x"77665544", "1001");
        wr_ce <= '0';
        send_data(x"BBBBBBBBBBBBBBBBAAAAAAAAAAAAAAAA99999999999999998888888888888888", x"BBAA9988", "1001");
        wr_ce <= '1';
        send_data(x"FFFFfFFFFFFFFFFFEEEEEEEEEEEEEEEEDDDDDDDDDDDDDDDDCCCCCCCCCCCCCCCC", x"FFEEDDCC", "1001");
        send_data(x"3333333333333333222222222222222211111111111111110000000000000000", x"33221100", "1001");
        send_data(x"7777777777777777666666666666666655555555555555554444444444444444", x"77665544", "1001");
        wait;

    end process;

    rd_tb_p : process

        procedure send_rd_mask(mask : std_logic_vector(BLOCK_COUNT - 1 downto 0)) is
        begin
            mask_out <= mask;
            wait until rising_edge(rd_clk);
        end;

    begin
        rd_ce <= '1';
        send_rd_mask("0000");
        for i in 0 to 6 loop
            wait until rising_edge(rd_clk);
        end loop;
        for i in 0 to 23 loop
            send_rd_mask("0100");
            send_rd_mask("0010");
            send_rd_mask("0001");
            rd_ce <= '0';
            send_rd_mask("0100");
            rd_ce <= '1';
        end loop;
        wait;
    end process;

    elastic_fifo_e : entity work.ELASTIC_FIFO
    generic map (
        BLOCK_WIDTH => BLOCK_WIDTH,
        BLOCK_COUNT => BLOCK_COUNT,
        OUTPUT_REGISTERS => true
    )
    port map (
        WR_CLK => wr_clk,
        WR_CE => wr_ce,
        RD_CLK => rd_clk,
        RD_CE => rd_ce,
        AS_RST => rst,
        DIN => data_in,
        AUX_IN => aux_in,
        MASK_IN => mask_in,
        DOUT => data_out,
        AUX_OUT => aux_out
    );

end architecture;
