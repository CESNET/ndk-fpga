-- pcie_crdt_up_fsm.vhd: PCIe Credit Flow Control Logic
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity PCIE_CRDT_UP_FSM is
    port(
        CLK               : in  std_logic;
        RESET             : in  std_logic;

        CRDT_UP_INIT      : in  std_logic;
        CRDT_UP_INIT_ACK  : out std_logic;
        CRDT_UP_INIT_DONE : out std_logic
    );
end entity;

architecture FULL of PCIE_CRDT_UP_FSM is

    type crdt_up_fsm_t is (st_wait_for_init, st_init_start, st_init_ack, st_init, st_init_done);
    signal crdt_up_fsm_pst : crdt_up_fsm_t;
    signal crdt_up_fsm_nst : crdt_up_fsm_t;

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                crdt_up_fsm_pst <= st_wait_for_init;
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
            when st_wait_for_init =>
                if (CRDT_UP_INIT = '1') then
                    crdt_up_fsm_nst <= st_init_start;
                end if;

            when st_init_start =>
                crdt_up_fsm_nst <= st_init_ack;

            when st_init_ack =>
                crdt_up_fsm_nst <= st_init;
                CRDT_UP_INIT_ACK <= '1';

            when st_init =>
                if (CRDT_UP_INIT = '0') then
                    crdt_up_fsm_nst <= st_init_done;
                end if;

            when st_init_done =>
                CRDT_UP_INIT_DONE <= '1';
        end case;
    end process;

end architecture;
