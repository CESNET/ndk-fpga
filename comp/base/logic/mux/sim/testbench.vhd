-- testbench.vhd: Testbench for merger from n inputs to m outputs
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use ieee.math_real.all;
use work.math_pack.all;
use ieee.numeric_std.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

    -- Constants declaration ---------------------------------------------------

    -- Synchronization
    constant C_CLK_PER            : time := 5.0 ns;
    constant C_RST_TIME           : time := 10 * C_CLK_PER + 1 ns;

    constant DATA_WIDTH           : integer := 4;
    constant MUX_WIDTH            : integer := 8;
    constant LATENCY              : integer := 2;
    constant METADATA_WIDTH       : integer := log2(MUX_WIDTH);
    constant INPUT_REG            : boolean := true;
    constant OUTPUT_REG           : boolean := false;

    -- Signals declaration -----------------------------------------------------

    -- Synchronization
    signal clk                                : std_logic;
    signal rst                                : std_logic;

    signal rx_data     : std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
    signal rx_sel      : std_logic_vector(log2(MUX_WIDTH)-1 downto 0);
    signal rx_metadata : std_logic_vector(METADATA_WIDTH-1 downto 0) := (others => '0');
    signal rx_src_rdy  : std_logic;
    signal rx_dst_rdy  : std_logic;

    signal tx_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal tx_metadata : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal tx_src_rdy  : std_logic;
    signal tx_dst_rdy  : std_logic;

    signal test_ok : std_logic := '1';
-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- CROSSBAR SCHEDULER planner
    -- -------------------------------------------------------------------------

    uut: entity work.GEN_MUX_PIPED
    generic map(
        DATA_WIDTH     => DATA_WIDTH,
        MUX_WIDTH      => MUX_WIDTH,
        MUX_LATENCY    => LATENCY,
        METADATA_WIDTH => METADATA_WIDTH,
        INPUT_REG      => INPUT_REG,
        OUTPUT_REG     => OUTPUT_REG
    )
    port map(
        CLK        => clk,
        RESET      => rst,

        RX_DATA     => rx_data    ,
        RX_SEL      => rx_sel     ,
        RX_METADATA => rx_metadata,
        RX_SRC_RDY  => rx_src_rdy ,
        RX_DST_RDY  => rx_dst_rdy ,

        TX_DATA     => tx_data    ,
        TX_METADATA => tx_metadata,
        TX_SRC_RDY  => tx_src_rdy ,
        TX_DST_RDY  => tx_dst_rdy
    );

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen: process
    begin
        clk <= '1';
        wait for C_CLK_PER / 2;
        clk <= '0';
        wait for C_CLK_PER / 2;
    end process clk_gen;

    -- generating reset
    rst_gen: process
    begin
        rst <= '1';
        wait for C_RST_TIME;
        rst <= '0';
        wait;
    end process rst_gen;

    -- -------------------------------------------------------------------------

    tb: process
        variable seed1 : positive := 42;
        variable seed2 : positive := 42;

        variable rand  : real;
        variable X     : integer;

        variable value : unsigned(DATA_WIDTH-1 downto 0) := (others => '1');
    begin
        wait for 1 ns;
        -- Wait for the reset
        if (rst='1') then
            wait until rst='0';
        end if;

        -- input gen
        rx_src_rdy  <= '0';
        rx_data     <= (others => '0');
        rx_metadata <= (others => '0');
        rx_sel      <= (others => '0');

        uniform(seed1,seed2,rand);
        X := integer(rand*real(100));
        if (X<80) then
            rx_src_rdy <= '1';

            uniform(seed1,seed2,rand);
            X := integer(rand*real(MUX_WIDTH-1));
            rx_sel  <= std_logic_vector(to_unsigned(X,rx_sel'length));
            rx_data((X+1)*DATA_WIDTH-1 downto X*DATA_WIDTH) <= std_logic_vector(value);
            rx_metadata <= std_logic_vector(resize_left(value,METADATA_WIDTH));
            value := value+1;
        end if;

        -- output check
        test_ok <= '1';
        if (tx_src_rdy='1' and tx_dst_rdy='1') then
            if (tx_data/=(DATA_WIDTH-1 downto 0 => '1') or tx_metadata/=(METADATA_WIDTH-1 downto 0 => '1')) then
                test_ok <= '0';
            end if;
        end if;

        -- dst_rdy gen
        tx_dst_rdy <= '0';

        uniform(seed1,seed2,rand);
        X := integer(rand*real(100));
        if (X<80) then
            tx_dst_rdy <= '1';
        end if;

        wait for C_CLK_PER -1 ns;
    end process;

end architecture behavioral;
