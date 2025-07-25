--! testbench.vhd: Testbench for DP_URAM_XILINX
--! # Copyright (C) 2015 CESNET
--! # Author: Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER                : time := 10 ns;           -- Clock period
    constant RESET_TIME            : time := 2*CLKPER + 5 ns; -- Reset duration
    constant DATA_WIDTH            : integer := 37;
    constant ADDRESS_WIDTH         : integer := 12;
    constant EXTERNAL_OUT_REG      : boolean := false;
    constant DEVICE                : string := "ULTRASCALE";
    constant ADDITIONAL_REG        : integer := 0;
    constant INTERNAL_OUT_REG      : boolean := false;
    --! Clock and reset signals
    signal   clk                   : std_logic;
    signal   reset                 : std_logic;
    signal   pipe_ena              : std_logic;
    signal   rea                   : std_logic;
    signal   wea                   : std_logic;
    signal   addra                 : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal   dia                   : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal   doa_dv                : std_logic;
    signal   doa                   : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal   pipe_enb              : std_logic;
    signal   reb                   : std_logic;
    signal   web                   : std_logic;
    signal   addrb                 : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal   dib                   : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal   dob_dv                : std_logic;
    signal   dob                   : std_logic_vector(DATA_WIDTH-1 downto 0);
begin

    --! BRAM_XILINX
    uut : entity work.DP_URAM_XILINX
    generic map (
        --! Input data width
        DATA_WIDTH         => DATA_WIDTH,
        --! Address bus width
        ADDRESS_WIDTH      => ADDRESS_WIDTH,
        --! Enable output register
        EXTERNAL_OUT_REG   => EXTERNAL_OUT_REG,
        --! Set input -> output latency
        ADDITIONAL_REG     => ADDITIONAL_REG,
        --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
        DEVICE             => DEVICE,
        INTERNAL_OUT_REG   => INTERNAL_OUT_REG
    )
    port map (
        --! \name Interface A
        --! Clock A
        CLK      => clk,
        --! CLKA sync reset
        RSTA     => reset,
        --! Pipe enable
        PIPE_ENA => pipe_ena,
        --! Read Enable
        REA      => rea,
        --! Write enable
        WEA      => wea,
        --! Address A
        ADDRA    => addra,
        --! Data A In
        DIA      => dia,
        --! Data A Valid
        DOA_DV   => doa_dv,
        --! Data A Out
        DOA      => doa,

        --! \name Interface B,
        --! CLKB sync reset
        RSTB     => reset,
        --! Pipe enable
        PIPE_ENB => pipe_enb,
        --! Read Enable
        REB      => reb,
        --! Write enable
        WEB      => web,
        --! Address B
        ADDRB    => addrb,
        --! Data B In
        DIB      => dib,
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
        rea      <= '0';
        wea      <= '0';
        addra    <= (others => '0');
        dia      <= (others => '0');
        pipe_enb <= '1';
        reb      <= '0';
        web      <= '0';
        addrb    <= (others => '0');
        dib      <= (others => '0');

        wait for RESET_TIME;
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- write on B, address -> 0
        dib    <= (35 => '1', others => '0');
        web    <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        web    <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read from A, address 0
        rea   <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        rea   <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');
        -- Write to B, address 42, read from A, address 41, 42, 43
        addra <= std_logic_vector(to_unsigned(42, ADDRESS_WIDTH));
        dia   <= std_logic_vector(to_unsigned(18, DATA_WIDTH));
        wea   <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');

        wea      <= '0';
        wait for 5*CLKPER; wait until (clk'event and clk = '1');
        reb      <= '1';
        rea      <= '1';
        addra    <= std_logic_vector(to_unsigned(40, ADDRESS_WIDTH));
        addrb    <= std_logic_vector(to_unsigned(42, ADDRESS_WIDTH));
        wait for CLKPER; wait until (clk'event and clk = '1');
        rea      <= '0';
        reb      <= '0';
        --! Port A write, port B read. Same address
        wait for 2*CLKPER; wait until (clk'event and clk = '1');
        rea      <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        rea      <= '0';
        wait for 10*CLKPER; wait until (clk'event and clk = '1');
        addra    <= std_logic_vector(to_unsigned(88, ADDRESS_WIDTH));
        addrb    <= std_logic_vector(to_unsigned(88, ADDRESS_WIDTH));
        dia      <= std_logic_vector(to_unsigned(36, DATA_WIDTH));
        wea      <= '1';
        reb      <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        wea      <= '0';
        reb      <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');
        --! Port B write, port A read. Same address
        addra    <= std_logic_vector(to_unsigned(66, ADDRESS_WIDTH));
        addrb    <= std_logic_vector(to_unsigned(66, ADDRESS_WIDTH));
        dib      <= std_logic_vector(to_unsigned(120, DATA_WIDTH));
        rea      <= '1';
        web      <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        rea      <= '0';
        web      <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');
        wea      <= '1';
        reb      <= '1';
        addra    <= std_logic_vector(to_unsigned(90, ADDRESS_WIDTH));
        addrb    <= std_logic_vector(to_unsigned(90, ADDRESS_WIDTH));
        dia      <= std_logic_vector(to_unsigned(36, DATA_WIDTH));
        wait for CLKPER; wait until (clk'event and clk = '1');
        addra    <= std_logic_vector(to_unsigned(91, ADDRESS_WIDTH));
        addrb    <= std_logic_vector(to_unsigned(91, ADDRESS_WIDTH));
        dia      <= std_logic_vector(to_unsigned(39, DATA_WIDTH));
        wait for CLKPER; wait until (clk'event and clk = '1');
        addra    <= std_logic_vector(to_unsigned(92, ADDRESS_WIDTH));
        addrb    <= std_logic_vector(to_unsigned(92, ADDRESS_WIDTH));
        dia      <= std_logic_vector(to_unsigned(38, DATA_WIDTH));
        wait for CLKPER; wait until (clk'event and clk = '1');
        wea      <= '0';
        reb      <= '0';
        pipe_ena <= '0';
        pipe_enb <= '0';
        wait for 4*CLKPER; wait until (clk'event and clk = '1');
        pipe_ena <= '1';
        pipe_enb <= '1';
        wait;
    end process;
end architecture;
