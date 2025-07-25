--! testbench.vhd: Testbench for BRAM_XILINX
--! # Copyright (C) 2015 CESNET
--! # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER            : time := 10 ns;           -- Clock period
    constant RESET_TIME        : time := 2*CLKPER + 5 ns; -- Reset duration
    constant DATA_WIDTH        : integer := 37;
    constant ADDRESS_WIDTH     : integer := 12;
    constant BRAM_TYPE         : integer := 36;
    constant WRITE_MODE_B      : string := "READ_FIRST";
    constant ENABLE_OUT_REG    : boolean := true;
    constant DEVICE            : string := "ULTRASCALE";

    --! Clock and reset signals
    signal clk        : std_logic;
    signal reset      : std_logic;
    signal pipe_ena   : std_logic;
    signal wea        : std_logic;
    signal addra      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal dia        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal pipe_enb   : std_logic;
    signal reb        : std_logic;
    signal addrb      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal dob_dv     : std_logic;
    signal dob        : std_logic_vector(DATA_WIDTH-1 downto 0);
begin

    --! BRAM_XILINX
    uut : entity work.SDP_BRAM_XILINX
    generic map (
        --! Input data width
        DATA_WIDTH     => DATA_WIDTH,
        --! Address bus width
        ADDRESS_WIDTH  => ADDRESS_WIDTH,
        --! Block Ram Type, only 18Kb,36Kb blocks
        BRAM_TYPE      => BRAM_TYPE,
        --! What operation will be performed first when both WE and RE are
        --! active? Only for behavioral simulation purpose.
        --! WRITE_FIRST(default) | READ_FIRST | NO_CHANGE
        WRITE_MODE_B   => WRITE_MODE_B,
        --! Enable output register
        ENABLE_OUT_REG => ENABLE_OUT_REG,
        --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
        DEVICE         => DEVICE
    )
    port map (
        --! \name Interface A
        --! Clock A
        CLKA     => clk,
        --! Pipe enable
        PIPE_ENA => pipe_ena,
        --! Write enable
        WEA      => wea,
        --! Address A
        ADDRA    => addra,
        --! Data A In
        DIA      => dia,

        --! \name Interface B
        --! Clock B
        CLKB     => clk,
        --! CLKB sync reset
        RSTB     => reset,
        --! Pipe enable
        PIPE_ENB => pipe_enb,
        --! Read Enable
        REB      => reb,
        --! Address B
        ADDRB    => addrb,
        --! Data B Valid
        DOB_DV   => dob_dv,
        --! Data B Out
        DOB      => dob
    );

    -- Generate clock
    clk_gen_p : process
    begin
        clk <= '1';
        wait for CLKPER/2;
        clk <= '0';
        wait for CLKPER/2;
    end process;

    -- Generate reset
    reset_gen : process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process;

    --! Simulating input flow
    input_flow : process
    begin
        pipe_ena <= '1';
        wea      <= '0';
        addra    <= (others => '0');
        dia      <= (others => '0');
        pipe_enb <= '1';
        reb      <= '0';
        addrb    <= (others => '0');

        wait for RESET_TIME;
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- write on A, address -> 0
        dia    <= (35 => '1', others => '0');
        wea    <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        wea    <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read on B, address -> 0
        addra  <= (0 => '0', others => '0');
        reb    <= '1';
        addrb  <= (0 => '0', others => '0');
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read on B, address -> 1
        reb    <= '1';
        addrb  <= (0 => '1', others => '0');
        wait for CLKPER; wait until (clk'event and clk = '1');
        reb    <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- write on A, address -> X'802
        dia    <= (36 => '1', others => '0');
        addra  <= (11 => '1', 1 => '1', others => '0');
        wea    <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read on B, address -> X'802
        wea    <= '0';
        addra  <= (11 => '1', 1 => '1', others => '0');
        reb    <= '1';
        addrb  <= (11 => '1', 1 => '1', others => '0');
        wait for CLKPER; wait until (clk'event and clk = '1');
        reb    <= '0';
        wait;
    end process;
end architecture;
