-- pcie_crdt_up_fsm.vhd: PCIe Credit Flow Control Logic
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity PCIE_CRDT_UP_FSM is
    port (
        CLK               : in  std_logic;
        RESET             : in  std_logic;

        CRDT_UP_INIT      : in  std_logic;
        CRDT_UP_INIT_ACK  : out std_logic;
        CRDT_UP_INIT_DONE : out std_logic
    );
end entity;

architecture FULL of PCIE_CRDT_UP_FSM is

    type   crdt_up_fsm_t is (ST_WAIT_FOR_INIT, ST_INIT_START, ST_INIT_ACK, ST_INIT, ST_INIT_DONE);
    signal crdt_up_fsm_pst : crdt_up_fsm_t;
    signal crdt_up_fsm_nst : crdt_up_fsm_t;

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                crdt_up_fsm_pst <= ST_WAIT_FOR_INIT;
            else
                crdt_up_fsm_pst <= crdt_up_fsm_nst;
            end if;
        end if;
    end process;

    process (all)
    begin
        crdt_up_fsm_nst   <= crdt_up_fsm_pst;
        CRDT_UP_INIT_ACK  <= '0';
        CRDT_UP_INIT_DONE <= '0';

        case (crdt_up_fsm_pst) is
            when ST_WAIT_FOR_INIT =>
                if (CRDT_UP_INIT = '1') then
                    crdt_up_fsm_nst <= ST_INIT_START;
                end if;

            when ST_INIT_START =>
                crdt_up_fsm_nst <= ST_INIT_ACK;

            when ST_INIT_ACK =>
                crdt_up_fsm_nst  <= ST_INIT;
                CRDT_UP_INIT_ACK <= '1';

            when ST_INIT =>
                if (CRDT_UP_INIT = '0') then
                    crdt_up_fsm_nst <= ST_INIT_DONE;
                end if;

            when ST_INIT_DONE =>
                CRDT_UP_INIT_DONE <= '1';
        end case;
    end process;

end architecture;
