--! testbench.vhd: Testbench for BRAM_V7
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
    constant RESET_TIME        : time := 2*CLKPER + 1 ns; -- Reset durati
    constant DATA_WIDTH        : integer := 37;
    constant ADDRESS_WIDTH     : integer := 12;
    constant BRAM_TYPE         : integer := 36;
    constant WRITE_MODE_A      : string := "WRITE_FIRST";
    constant WRITE_MODE_B      : string := "WRITE_FIRST";
    constant ENABLE_OUT_REG    : boolean := false;
    constant DEVICE            : string := "7SERIES";

    --! Clock and reset signals
    signal clk        : std_logic;
    signal reset      : std_logic;
    signal pipe_ena   : std_logic;
    signal rea        : std_logic;
    signal wea        : std_logic;
    signal addra      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal dia        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal doa_dv     : std_logic;
    signal doa        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal pipe_enb   : std_logic;
    signal reb        : std_logic;
    signal web        : std_logic;
    signal addrb      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal dib        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal dob_dv     : std_logic;
    signal dob        : std_logic_vector(DATA_WIDTH-1 downto 0);
begin

    --! BRAM_V7
    uut : entity work.DP_BRAM_V7
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
        WRITE_MODE_A   => WRITE_MODE_A,
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

        --! \name Interface B
        --! Clock B
        CLKB     => clk,
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
        wait for CLKPER;
        -- write on B , address -> 0
        dib    <= (35 => '1', others => '0');
        web    <= '1';
        wait for CLKPER;
        web    <= '0';
        wait for CLKPER;

        -- read on A,B , address -> 0
        rea    <= '1';
        addra  <= (0 => '0',others => '0');
        reb    <= '1';
        addrb  <= (0 => '0',others => '0');
        wait for CLKPER;

        -- read on B , address -> 1
        reb    <= '1';
        addrb  <= (0 => '1',others => '0');
        wait for CLKPER;
        reb    <= '0';
        rea    <= '0';
        wait for CLKPER;

        -- write on A , address -> X'802
        dia    <= (36 => '1', others => '0');
        addra  <= (11 => '1', 1 => '1', others => '0');
        wea    <= '1';
        wait for CLKPER;

        -- read on A,B , address -> X'802
        wea    <= '0';
        rea    <= '1';
        addra  <= (11 => '1', 1 => '1', others => '0');
        reb    <= '1';
        addrb  <= (11 => '1', 1 => '1', others => '0');
        wait for CLKPER;
        reb    <= '0';
        rea    <= '0';
        wait;
    end process;
end architecture;
