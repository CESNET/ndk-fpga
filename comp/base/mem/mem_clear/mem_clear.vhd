-- mem_clear.vhd: Unit for clearing BRAM memories
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MEM_CLEAR is
generic (
    DATA_WIDTH  : integer := 32;
    ITEMS       : integer := 512;
    -- Will disable memory clearing during RST
    CLEAR_EN    : boolean := true
);
port (
    CLK         : in  std_logic;
    RST         : in  std_logic;

    -- All addresses were generated
    CLEAR_DONE  : out std_logic;
    -- Clear address given by CLEAR_ADDR
    CLEAR_WR    : out std_logic;
    CLEAR_ADDR  : out std_logic_vector(log2(ITEMS) - 1 downto 0)
);
end entity;

architecture FULL of MEM_CLEAR is

    type FSM_STATES_T is (
        INIT,
        CLEAR,
        RUNNING
    );

    constant CNTR_W             : natural := log2(ITEMS);

    -- State machine --

    signal curr_state           : FSM_STATES_T;
    signal next_state           : FSM_STATES_T;

    signal addr_r               : unsigned(CNTR_W-1 downto 0);
    signal addr_r_clr           : std_logic;
    signal addr_r_inc           : std_logic;

 begin

    CLEAR_ADDR          <= std_logic_vector(addr_r);

    reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if addr_r_clr = '1' then
                addr_r <= (others => '0');
            else
                if addr_r_inc = '1' then
                    addr_r <= addr_r + 1;
                end if;
            end if;
        end if;
    end process;

    -------------------
    -- STATE MACHINE --
    -------------------

    state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                curr_state <= INIT;
            else
                curr_state <= next_state;
            end if;
        end if;
    end process;

    -- Output logic
    process (all)
    begin
        CLEAR_DONE          <= '0';
        CLEAR_WR            <= '0';
        addr_r_clr          <= '0';
        addr_r_inc          <= '0';
        next_state          <= curr_state;

        case curr_state is
            when INIT =>
                if (CLEAR_EN) then
                    next_state <= CLEAR;
                else
                    next_state <= RUNNING;
                end if;

                addr_r_clr <= '1';

            when CLEAR =>
                if (addr_r = (ITEMS - 1)) then
                    next_state <= RUNNING;
                end if;

                CLEAR_WR    <= '1';
                addr_r_inc  <= '1';

            when RUNNING =>
                CLEAR_DONE      <= '1';
        end case;
    end process;

end architecture;
