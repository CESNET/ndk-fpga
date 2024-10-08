-- emif_refresh.vhd: Component for manual refresh of the EMIF IP
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component is able to trigger DDR memory refresh
-- Refresh is performed by editing EMIF MMR registers via MMR Avalon-MM bus
-- (MMR = memory mapped registers)
-- Deassertion of bits inside MMR reg is done automaticaly by EMIF

entity EMIF_REFRESH is
generic (
    -- Avalon MMR bus --
    AMM_DATA_WIDTH          : integer := 32;
    AMM_ADDR_WIDTH          : integer := 10;
    AMM_BURST_COUNT_WIDTH   : integer := 7;

    -- Control --
    -- Refresh will be performed automaticaly
    PERIODIC_REFRESH        : boolean := false;
    REFRESH_PERIOD_WIDTH    : integer := 32;

    -- Others --
    RANK_CNT                : integer := 4;
    REFRESH_REG_ADDR        : integer := 44;
    ACK_REG_ADDR            : integer := 50;
    DEVICE                  : string
);
port(
    -- Main --
    CLK                     : in  std_logic;
    RST                     : in  std_logic;

    -- Will trigger refresh on specified rank
    REFRESH                 : in  std_logic_vector(RANK_CNT - 1 downto 0);
    REFRESHING              : out std_logic_vector(RANK_CNT - 1 downto 0);
    REFRESHING_ANY          : out std_logic;
    REFRESH_START_ANY       : out std_logic;
    REFRESH_DONE_ANY        : out std_logic;

    -- Only when automatic refresh is used
    REFRESH_PERIOD_TICKS    : in std_logic_vector(REFRESH_PERIOD_WIDTH - 1 downto 0);

    -- Avalon interface --
    AMM_READY               : in  std_logic;
    AMM_BEGIN_BURST         : out std_logic := '0';
    AMM_READ                : out std_logic;
    AMM_WRITE               : out std_logic;
    AMM_ADDRESS             : out std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    AMM_READ_DATA           : in  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_WRITE_DATA          : out std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_BURST_COUNT         : out std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    AMM_READ_DATA_VALID     : in  std_logic
);
end entity;

-- =========================================================================

architecture FULL of EMIF_REFRESH is

    type STATES_T is (
        INIT,
        PERFORM_REFRESH,
        REQ_ACK,
        WAIT_FOR_ACK
    );

    constant REFRESH_REG_ADDR_VEC : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0)
        := std_logic_vector(to_unsigned(REFRESH_REG_ADDR, AMM_ADDR_WIDTH));
    constant ACK_REG_ADDR_VEC : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0)
        := std_logic_vector(to_unsigned(ACK_REG_ADDR, AMM_ADDR_WIDTH));

    -- To overcome timing issues
    signal rst_intern               : std_logic;

    -- State machine
    signal curr_state               : STATES_T;
    signal next_state               : STATES_T;

    signal any_refresh              : std_logic;
    signal any_refresh_edge         : std_logic;

    signal refresh_cnter_full       : std_logic := '0';
    signal refresh_cnter            : std_logic_vector(REFRESH_PERIOD_WIDTH - 1 downto 0) := (others => '0');

    signal refreshing_ranks         : std_logic_vector(RANK_CNT - 1 downto 0);

begin
    -------------------------
    -- Component instances --
    -------------------------
    refresh_edge_trig_i : entity work.EDGE_DETECT
    port map (
        CLK                 => CLK,
        DI                  => any_refresh,
        EDGE                => any_refresh_edge
    );

    any_refresh_i : entity work.GEN_OR
    generic map (
        OR_WIDTH        => RANK_CNT
    )
    port map (
        DI              => REFRESH,
        DO              => any_refresh
    );

    -------------------------
    -- Combinational logic --
    -------------------------
    refresh_cnter_full_g : if PERIODIC_REFRESH generate
        refresh_cnter_full <= '1' when (refresh_cnter >= REFRESH_PERIOD_TICKS) else
                              '0';
    refreshing_ranks <= (others => '1') when (refresh_cnter_full) else
                        REFRESH;
    end generate;

    refreshing_ranks_g : if not PERIODIC_REFRESH generate
        refreshing_ranks <= REFRESH;
    end generate;

    ---------------
    -- Registers --
    ---------------

    rst_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            rst_intern <= RST;
        end if;
    end process;

    refresh_cnter_g : if PERIODIC_REFRESH generate
        refresh_period_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (rst_intern = '1' or refresh_cnter_full = '1' or any_refresh = '1') then
                    refresh_cnter <= (others => '0');
                else
                    refresh_cnter <= std_logic_vector(unsigned(refresh_cnter) + 1);
                end if;
            end if;
        end process;
    end generate;

    refreshing_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1' or next_state = INIT) then
                REFRESHING      <= (others => '0');
                REFRESHING_ANY  <= '0';
            elsif (next_state = PERFORM_REFRESH) then
                REFRESHING      <= refreshing_ranks;
                REFRESHING_ANY  <= '1';
            end if;
        end if;
    end process;

    -----------------
    -- Control FSM --
    -----------------

    -- Next state process
    state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1') then
                curr_state <= INIT;
            else
                curr_state <= next_state;
            end if;
        end if;
    end process;

    -- Output logic
    process (all)
    begin
        AMM_READ            <= '0';
        AMM_WRITE           <= '0';
        AMM_ADDRESS         <= (others => '0');
        AMM_WRITE_DATA      <= (others => '0');
        AMM_BURST_COUNT     <= std_logic_vector(to_unsigned(1, AMM_BURST_COUNT_WIDTH));

        REFRESH_DONE_ANY    <= '0';
        REFRESH_START_ANY   <= '0';

        case curr_state is
            when INIT =>

            when PERFORM_REFRESH =>
                AMM_ADDRESS         <= REFRESH_REG_ADDR_VEC;
                AMM_WRITE           <= '1';
                AMM_WRITE_DATA(RANK_CNT - 1 downto 0) <= REFRESHING;

                if (AMM_READY = '1') then
                    REFRESH_START_ANY   <= '1';
                end if;

            when REQ_ACK =>
                AMM_ADDRESS         <= ACK_REG_ADDR_VEC;
                AMM_READ            <= '1';

            when WAIT_FOR_ACK =>
                if (AMM_READ_DATA_VALID = '1' and AMM_READ_DATA(0) = '0') then
                    REFRESH_DONE_ANY    <= '1';
                end if;

        end case;
    end process;

    -- Next state logic
    process (all)
    begin
        next_state <= curr_state;

        case curr_state is
            when INIT =>
                if (any_refresh_edge = '1' or refresh_cnter_full = '1') then
                    next_state <= PERFORM_REFRESH;
                end if;

            when PERFORM_REFRESH =>
                if (AMM_READY = '1') then
                    -- Request was send
                    next_state <= REQ_ACK;
                end if;

            when REQ_ACK =>
                if (AMM_READY = '1') then
                    next_state <= WAIT_FOR_ACK;
                end if;

            when WAIT_FOR_ACK =>
                if (AMM_READ_DATA_VALID = '1') then
                    if (AMM_READ_DATA(0) = '0') then
                        next_state <= INIT;
                    else
                        next_state <= REQ_ACK;
                    end if;
                end if;

        end case;
    end process;

end architecture;
