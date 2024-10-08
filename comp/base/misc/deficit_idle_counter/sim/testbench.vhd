-- testbench.vhd.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use std.env.all;
use STD.textio.all;

library work;
use work.type_pack.all;
use work.math_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

--! ----------------------------------------------------------------------------
--!                        Entity declaration
--! ----------------------------------------------------------------------------
entity TESTBENCH is
end entity TESTBENCH;
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

    signal CLK          : std_logic;
    signal RESET        : std_logic;

    signal RX_PKT_LEN     : slv_array_t     (PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    signal RX_PKT_VLD     : std_logic_vector(PKTS-1 downto 0);
    signal RX_PKT_SRC_RDY : std_logic;
    signal RX_PKT_DST_RDY : std_logic; -- propagated from TX_PKT_DST_RDY

    signal TX_PKT_GAP     : slv_array_t     (PKTS-1 downto 0)(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
    signal TX_PKT_VLD     : std_logic_vector(PKTS-1 downto 0);
    signal TX_PKT_SRC_RDY : std_logic; -- propagated from RX_PKT_SRC_RDY
    signal TX_PKT_DST_RDY : std_logic;

begin

    uut : entity work.DEFICIT_IDLE_COUNTER
    generic map (
        PKTS         => PKTS        ,
        PKT_SIZE     => PKT_SIZE    ,
        GAP_SIZE     => GAP_SIZE    ,
        ALIGN        => ALIGN       ,
        MIN_GAP_SIZE => MIN_GAP_SIZE
    )
    port map (
        CLK   => CLK  ,
        RESET => RESET,

        RX_PKT_LEN     => RX_PKT_LEN    ,
        RX_PKT_VLD     => RX_PKT_VLD    ,
        RX_PKT_SRC_RDY => RX_PKT_SRC_RDY,
        RX_PKT_DST_RDY => RX_PKT_DST_RDY,

        TX_PKT_GAP     => TX_PKT_GAP    ,
        TX_PKT_VLD     => TX_PKT_VLD    ,
        TX_PKT_SRC_RDY => TX_PKT_SRC_RDY,
        TX_PKT_DST_RDY => TX_PKT_DST_RDY
    );

    TX_PKT_DST_RDY <= '1';

    -- generating clock signal
    clk_pr : process
    begin
        CLK <= '1';
        wait for CLK_PERIOD/2;
        CLK <= '0';
        wait for CLK_PERIOD/2;
    end process;

    -- generating reset signal
    reset_pr : process
    begin
        RESET <= '1';
        wait for CLK_PERIOD*2;
        RESET <= '0';
        wait;
    end process;

    -- input generation
    input_pr :process
        variable s0 : integer := 11;
        variable s1 : integer := 15;
        variable X  : integer := 0;
        variable C  : unsigned(log2(PKT_SIZE+1)-1 downto 0) := to_unsigned(64,log2(PKT_SIZE+1));
    begin
        RX_PKT_SRC_RDY <= '0';

        wait for CLK_PERIOD/2;
        wait until RESET/='1';
        wait for CLK_PERIOD/2;

        -- Packets with size 64 B
        for i in 0 to 16-1 loop
            RX_PKT_LEN     <= (others => (others => 'X'));
            RX_PKT_VLD     <= (others => '0');
            RX_PKT_SRC_RDY <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,X);
                if (X<PKT_CHANCE) then
                    RX_PKT_LEN(i)  <= std_logic_vector(to_unsigned(64,log2(PKT_SIZE+1)));
                    RX_PKT_VLD(i)  <= '1';
                    RX_PKT_SRC_RDY <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        RX_PKT_SRC_RDY <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with size 65 B
        for i in 0 to 16-1 loop
            RX_PKT_LEN     <= (others => (others => 'X'));
            RX_PKT_VLD     <= (others => '0');
            RX_PKT_SRC_RDY <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,X);
                if (X<PKT_CHANCE) then
                    RX_PKT_LEN(i)  <= std_logic_vector(to_unsigned(65,log2(PKT_SIZE+1)));
                    RX_PKT_VLD(i)  <= '1';
                    RX_PKT_SRC_RDY <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        RX_PKT_SRC_RDY <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with size 71 B
        for i in 0 to 16-1 loop
            RX_PKT_LEN     <= (others => (others => 'X'));
            RX_PKT_VLD     <= (others => '0');
            RX_PKT_SRC_RDY <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,X);
                if (X<PKT_CHANCE) then
                    RX_PKT_LEN(i)  <= std_logic_vector(to_unsigned(71,log2(PKT_SIZE+1)));
                    RX_PKT_VLD(i)  <= '1';
                    RX_PKT_SRC_RDY <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        RX_PKT_SRC_RDY <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with incrementing size
        for i in 0 to 32-1 loop
            RX_PKT_LEN     <= (others => (others => 'X'));
            RX_PKT_VLD     <= (others => '0');
            RX_PKT_SRC_RDY <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,X);
                if (X<PKT_CHANCE) then
                    RX_PKT_LEN(i)  <= std_logic_vector(C);
                    C := C+1;
                    RX_PKT_VLD(i)  <= '1';
                    RX_PKT_SRC_RDY <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        RX_PKT_SRC_RDY <= '0';
        wait for CLK_PERIOD*8;

        -- Packets with random size B
        while (true) loop
            RX_PKT_LEN     <= (others => (others => 'X'));
            RX_PKT_VLD     <= (others => '0');
            RX_PKT_SRC_RDY <= '0';

            for i in 0 to PKTS-1 loop
                randint(s0,s1,0,99,X);
                if (X<PKT_CHANCE) then
                    randint(s0,s1,64,128,X);
                    RX_PKT_LEN(i)  <= std_logic_vector(to_unsigned(X,log2(PKT_SIZE+1)));
                    RX_PKT_VLD(i)  <= '1';
                    RX_PKT_SRC_RDY <= '1';
                end if;
            end loop;

            wait for CLK_PERIOD;
        end loop;

        RX_PKT_SRC_RDY <= '0';
        wait for CLK_PERIOD*8;

        wait;
    end process;

end architecture BEHAVIORAL;
