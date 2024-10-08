-- pcie_crdt_dw_fsm.vhd: PCIe Credit Flow Control Logic
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity PCIE_CRDT_DW_FSM is
    port(
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        CRDT_DW_INIT       : out std_logic;
        CRDT_DW_INIT_ACK   : in  std_logic;
        CRDT_DW_INIT_EN    : out std_logic;
        CRDT_DW_INIT_LAST  : in  std_logic;
        CRDT_DW_INIT_DONE  : out std_logic
    );
end entity;

architecture FULL of PCIE_CRDT_DW_FSM is

    type crdt_dw_fsm_t is (st_idle, st_init_start, st_init_ack, st_init_en, st_init_gap, st_init_gap2, st_init_gap3, st_init_done);
    signal crdt_dw_fsm_pst : crdt_dw_fsm_t;
    signal crdt_dw_fsm_nst : crdt_dw_fsm_t;

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                crdt_dw_fsm_pst <= st_idle;
            else
                crdt_dw_fsm_pst <= crdt_dw_fsm_nst;
            end if;
        end if;
    end process;
    
    process (all)
    begin
        crdt_dw_fsm_nst   <= crdt_dw_fsm_pst;
        CRDT_DW_INIT      <= '0';
        CRDT_DW_INIT_EN   <= '0';
        CRDT_DW_INIT_DONE <= '0';

        case (crdt_dw_fsm_pst) is
            when st_idle =>
                crdt_dw_fsm_nst <= st_init_start;

            when st_init_start =>
                crdt_dw_fsm_nst <= st_init_ack;
                CRDT_DW_INIT <= '1';

            when st_init_ack =>
                CRDT_DW_INIT <= '1';
                if (CRDT_DW_INIT_ACK = '1') then
                    crdt_dw_fsm_nst <= st_init_en;
                end if;

            when st_init_en =>
                CRDT_DW_INIT    <= '1';
                CRDT_DW_INIT_EN <= '1';
                if (CRDT_DW_INIT_LAST = '1') then
                    crdt_dw_fsm_nst <= st_init_gap;
                end if;

            when st_init_gap =>
                crdt_dw_fsm_nst <= st_init_gap2;
                CRDT_DW_INIT <= '1';

            when st_init_gap2 =>
                crdt_dw_fsm_nst <= st_init_gap3;
                CRDT_DW_INIT <= '1';

            when st_init_gap3 =>
                crdt_dw_fsm_nst <= st_init_done;
                CRDT_DW_INIT <= '1';

            when st_init_done =>
                CRDT_DW_INIT_DONE <= '1';
        end case;
    end process;

end architecture;
