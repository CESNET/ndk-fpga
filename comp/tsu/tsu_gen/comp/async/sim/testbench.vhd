-- testbench.vhd: testbench of assynchronous unit for tsu_cv2
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture BEHAVIORAL of TESTBENCH is
    -- ============================
    -- Global Constant Declaration
    -- ============================

    -- 125MHz
    constant IN_PERIOD    : time := 5 ns;
    -- 160MHz
    constant OUT_PERIOD   : time := 6.25 ns;
    constant DELAY        : time := 5.5 ns;
    constant RESET_DELAY  : time := 100 ns;

    -- Signal declaration
    signal in_clk          : std_logic := '0';
    signal mi32_reset      : std_logic;
    signal tsu_core_reset  : std_logic;
    signal out_clk         : std_logic := '0';
    signal rqst            : std_logic;
    signal rdy             : std_logic;
    signal out_rqst        : std_logic;

    -- ----------------------------------------------------------------------------
    --                      Architecture body
    -- ----------------------------------------------------------------------------
begin

    -- -------------------------------------------------------------------------
    --                         ASYNC UNIT
    -- -------------------------------------------------------------------------
    uut : entity work.ASYNC
    port map (
        -- input clk
        IN_CLK     => in_clk,
        IN_RESET   => mi32_reset,
        -- data write request
        RQST       => rqst,
        -- address ready signal - when we are ready for another transaction
        RDY        => rdy,

        -- output clk and write enable
        OUT_CLK    => out_clk,
        OUT_RESET  => tsu_core_reset,
        OUT_RQST   => out_rqst
    );

    -- ----------------------------------------------------
    -- IN_CLK generator - 125 MHz
    in_clk_gen : process
    begin
        in_clk <= '1';
        wait for IN_PERIOD/2;
        in_clk <= '0';
        wait for IN_PERIOD/2;
    end process;

    -- ----------------------------------------------------
    -- OUT_CLK generator - 160 MHz
    out_clk_gen : process
    begin
        out_clk <= '1';
        wait for OUT_PERIOD/2;
        out_clk <= '0';
        wait for OUT_PERIOD/2;
    end process;

    -- ----------------------------------------------------
    -- MI32 Reset generation
    proc_mi32_reset : process
    begin
        mi32_reset     <= '1';
        tsu_core_reset <= '1';
        wait for RESET_DELAY;
        mi32_reset     <= '0';
        tsu_core_reset <= '0';
        wait;
    end process;

    -- ----------------------------------------------------------------------------
    --                         Main testbench process
    -- ----------------------------------------------------------------------------
    async_test : process
        -- ----------------------------------------------------------------
        --                        Testbench Body
        -- ----------------------------------------------------------------
    begin
        rqst <= '0';
        wait for RESET_DELAY;

        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';

        wait for 20*IN_PERIOD;

        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';
        wait for 2*IN_PERIOD;
        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';

        wait for 10*IN_PERIOD;

        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';
        wait for 4*IN_PERIOD;
        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';

        wait for 9*IN_PERIOD;

        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';
        wait for 5*IN_PERIOD;
        rqst <= '1';
        wait for IN_PERIOD;
        rqst <= '0';

        wait;

    end process;

end architecture;
