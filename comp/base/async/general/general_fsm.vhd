-- general_fsm.vhd: Closed-loop solution CDC
-- Copyright (C) 2014 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;

--! -------------------------------------------------------------------------
--!                      Entity declaration
--! -------------------------------------------------------------------------

entity ASYNC_GENERAL_FSM is
    generic (
        DETECT_RISING_EDGE  : BOOLEAN := false;
        DETECT_FALLING_EDGE : BOOLEAN := false
    );
    port (
        ACLK       : in  STD_LOGIC;   --! Clock
        ARST       : in  STD_LOGIC;   --! Reset
        ADATAIN    : in  STD_LOGIC;   --! Signal ADATAIN
        ADATA      : out STD_LOGIC;   --! Signal ADATA
        SIG_AREADY : in  STD_LOGIC;   --! Signal SIG_AREADY
        AREADY     : out STD_LOGIC    --! Signal AREADY
    );
end entity;

--! -------------------------------------------------------------------------
--!                      Architecture declaration
--! -------------------------------------------------------------------------

architecture FULL of ASYNC_GENERAL_FSM is

    signal sig_adata     : std_logic := '0';
    signal adata_next    : std_logic := '0';
    signal last_adatain  : std_logic := '0';

    signal adatain_masked      : std_logic := '0';

    signal comp_last_adatain   : std_logic := '0';
    signal comp_last_adatain2  : std_logic := '0';
    signal comp_adatain        : std_logic := '0';
    signal comp_adatain2       : std_logic := '0';

    type   state is (ST0,ST1);
    signal present_st : state := ST0;
    signal next_st    : state := ST0;

    --! -------------------------------------------------------------------------
begin
    --! -------------------------------------------------------------------------

    ADATA <= sig_adata;

    --! sig_adata and last_adatain register
    process (ACLK)
    begin
        if (rising_edge(ACLK)) then
            if (ARST = '1') then
                sig_adata    <= '0';
                last_adatain <= '0';
            else
                last_adatain <= ADATAIN;
                sig_adata    <= adata_next;
            end if;
        end if;
    end process;

    --! -------------------------------------------------------------------------

    double_mode : if (DETECT_RISING_EDGE and DETECT_FALLING_EDGE) generate
        comp_last_adatain  <= '0';
        comp_adatain       <= '1';
        comp_last_adatain2 <= '1';
        comp_adatain2      <= '0';
    end generate;

    rising_mode : if (DETECT_RISING_EDGE and NOT DETECT_FALLING_EDGE) generate
        comp_last_adatain  <= '0';
        comp_adatain       <= '1';
        comp_last_adatain2 <= '0';
        comp_adatain2      <= '1';
    end generate;

    falling_mode : if (NOT DETECT_RISING_EDGE and DETECT_FALLING_EDGE) generate
        comp_last_adatain  <= '1';
        comp_adatain       <= '0';
        comp_last_adatain2 <= '1';
        comp_adatain2      <= '0';
    end generate;

    --! -------------------------------------------------------------------------
    --!                      FSM
    --! -------------------------------------------------------------------------

    --! Present State register
    present_state_reg : process (ACLK)
    begin
        if (rising_edge(ACLK)) then
            if (ARST = '1') then
                present_st <= ST0;
            else
                present_st <= next_st;
            end if;
        end if;
    end process;

    adatain_masked <= ADATAIN and not ARST;

    --! Next State logic
    next_state_logic : process (present_st, adatain_masked, SIG_AREADY, last_adatain, comp_last_adatain, comp_adatain, comp_last_adatain2, comp_adatain2)
    begin
        case present_st is

            --! STATE st0
            when ST0 =>
                if ((last_adatain = comp_last_adatain and adatain_masked = comp_adatain) or (last_adatain = comp_last_adatain2 and adatain_masked = comp_adatain2)) then
                    next_st <= ST1;
                else
                    next_st <= ST0;
                end if;

            --! STATE st1
            when ST1 =>
                if (SIG_AREADY = '1') then
                    next_st <= ST0;
                else
                    next_st <= ST1;
                end if;

            --! Others STATE
            when others => null;

        end case;
    end process;

    -- Output logic
    output_logic : process (present_st, adatain_masked, sig_adata, last_adatain, comp_last_adatain, comp_adatain, comp_last_adatain2, comp_adatain2)
    begin
        case present_st is

            --! STATE st0
            when ST0 =>
                AREADY <= '1';

                if ((last_adatain = comp_last_adatain and adatain_masked = comp_adatain) or (last_adatain = comp_last_adatain2 and adatain_masked = comp_adatain2)) then
                    if (sig_adata = '1') then
                        adata_next <= '0';
                    else
                        adata_next <= '1';
                    end if;
                else
                    if (sig_adata = '1') then
                        adata_next <= '1';
                    else
                        adata_next <= '0';
                    end if;
                end if;

            --! STATE st1
            when ST1 =>
                AREADY <= '0';

                if (sig_adata = '1') then
                    adata_next <= '1';
                else
                    adata_next <= '0';
                end if;

            --! Others STATE
            when others => null;

        end case;
    end process;

end architecture;
