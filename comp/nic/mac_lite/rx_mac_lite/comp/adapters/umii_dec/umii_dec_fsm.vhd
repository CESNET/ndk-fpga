-- umii_dec_fsm.vhd: FSM for Universal MII decoder
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity UMII_DEC_FSM is
    generic(
        REGIONS : natural := 4
    );
    port(
        -- =====================================================================
        -- CLOCK, RESET AND ENABLE
        -- =====================================================================
        CLK         : in  std_logic;
        RESET       : in  std_logic;
        ENABLE      : in  std_logic;
        -- =====================================================================
        -- INPUT INTERFACE
        -- =====================================================================
        IN_WF       : in  std_logic_vector(REGIONS-1 downto 0);
        IN_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        IN_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        IN_SOF_ERR  : in  std_logic_vector(REGIONS-1 downto 0);
        IN_EOF_ERR  : in  std_logic_vector(REGIONS-1 downto 0);
        IN_CTRL_ERR : in  std_logic_vector(REGIONS-1 downto 0);
        IN_DATA_ERR : in  std_logic_vector(REGIONS-1 downto 0);
        -- =====================================================================
        -- OUTPUT INTERFACE
        -- =====================================================================
        OUT_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        OUT_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        OUT_ERR     : out std_logic_vector(REGIONS-1 downto 0)
    );
end entity;

architecture FULL of UMII_DEC_FSM is

    type fsm_states is (st_ready, st_packet, st_error);
    type fsm_states_array is array (REGIONS downto 0) of fsm_states;

    signal s_any_error : std_logic_vector(REGIONS-1 downto 0);
    signal s_state     : fsm_states_array;

begin

    any_error_g : for r in 0 to REGIONS-1 generate
        s_any_error(r) <= IN_SOF_ERR(r) or IN_EOF_ERR(r) or IN_CTRL_ERR(r) or IN_DATA_ERR(r) or IN_WF(r);
    end generate;

    -- =========================================================================
    -- FSM STATE REGISTER
    -- =========================================================================

    state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_state(0) <= st_ready;
            elsif (ENABLE = '1') then
                s_state(0) <= s_state(REGIONS);
            end if;
        end if;
    end process;

    -- =========================================================================
    -- FSM NEXT STATE LOGIC
    -- =========================================================================

    next_state_logic_g : for r in 0 to REGIONS-1 generate
        next_state_logic_p : process (all)
        begin
            case (s_state(r)) is
                -- st_ready
                when st_ready =>
                    if (IN_SOF(r) = '1' and s_any_error(r) = '0') then
                        s_state(r+1) <= st_packet;
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '0' and s_any_error(r) = '1') then
                        if (IN_DATA_ERR(r) = '1') then
                            s_state(r+1) <= st_ready;
                        else
                            s_state(r+1) <= st_error;
                        end if;
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '1') then
                        if (IN_WF(r) = '1' or IN_DATA_ERR(r) = '1') then
                            s_state(r+1) <= st_ready;
                        elsif (IN_WF(r) = '0' and IN_SOF_ERR(r) = '1') then
                            s_state(r+1) <= st_error;
                        else
                            s_state(r+1) <= st_packet;
                        end if;
                    else
                        s_state(r+1) <= st_ready;
                    end if;

                -- st_packet
                when st_packet =>
                    if (IN_SOF(r) = '0' and IN_EOF(r) = '1') then
                        s_state(r+1) <= st_ready;
                    elsif ((IN_SOF(r) = '1' and IN_EOF(r) = '0') or (IN_SOF(r) = '0' and IN_EOF(r) = '0' and s_any_error(r) = '1')) then
                        s_state(r+1) <= st_error;
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '1') then
                        if (IN_WF(r) = '1' or IN_DATA_ERR(r) = '1') then
                            s_state(r+1) <= st_ready;
                        elsif (IN_WF(r) = '0' and IN_SOF_ERR(r) = '1') then
                            s_state(r+1) <= st_error;
                        else
                            s_state(r+1) <= st_packet;
                        end if;
                    else
                        s_state(r+1) <= st_packet;
                    end if;

                -- st_error
                when st_error =>
                    if (IN_SOF(r) = '0' and IN_EOF(r) = '1') then
                        s_state(r+1) <= st_ready;
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '0') then
                        s_state(r+1) <= st_packet;
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '1') then
                        if (IN_WF(r) = '1' or IN_DATA_ERR(r) = '1') then
                            s_state(r+1) <= st_ready;
                        elsif (IN_WF(r) = '0' and IN_SOF_ERR(r) = '1') then
                            s_state(r+1) <= st_error;
                        else
                            s_state(r+1) <= st_packet;
                        end if;
                    else
                        s_state(r+1) <= st_error;
                    end if;

                when others =>
                    s_state(r+1) <= st_ready;
            end case;
        end process;
    end generate;

    -- =========================================================================
    -- FSM OUTPUT LOGIC
    -- =========================================================================

    output_logic_g : for r in 0 to REGIONS-1 generate
        output_logic_p : process (all)
        begin
            OUT_SOF(r) <= '0';
            OUT_EOF(r) <= '0';
            OUT_ERR(r) <= '0';

            case (s_state(r)) is
                -- st_ready
                when st_ready =>
                    if (IN_SOF(r) = '1' and s_any_error(r) = '0') then
                        OUT_SOF(r) <= '1';
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '0' and s_any_error(r) = '1') then
                        if (IN_DATA_ERR(r) = '1') then
                            OUT_SOF(r) <= '0';
                        else
                            OUT_SOF(r) <= '1';
                        end if;
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '1') then
                        if (IN_DATA_ERR(r) = '1') then
                            OUT_SOF(r) <= '0';
                            OUT_EOF(r) <= '0';
                        elsif (IN_WF(r) = '1') then
                            if (IN_SOF_ERR(r) = '1' or IN_EOF_ERR(r) = '1' or IN_CTRL_ERR(r) = '1') then
                                OUT_SOF(r) <= '1';
                                OUT_EOF(r) <= '1';
                                OUT_ERR(r) <= '1';
                            else
                                OUT_SOF(r) <= '1';
                                OUT_EOF(r) <= '1';
                                OUT_ERR(r) <= '0';
                            end if;
                        elsif (IN_WF(r) = '0' and IN_WF(r) = '1') then
                            OUT_SOF(r) <= '1';
                        else
                            OUT_SOF(r) <= '1';
                        end if;
                    end if;

                -- st_packet
                when st_packet =>
                    if (IN_SOF(r) = '0' and IN_EOF(r) = '1') then
                        OUT_EOF(r) <= '1';
                        OUT_ERR(r) <= s_any_error(r);
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '0') then
                        OUT_SOF(r) <= '0';
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '1') then
                        if (IN_WF(r) = '1' or IN_DATA_ERR(r) = '1') then
                            OUT_EOF(r) <= '1';
                            OUT_ERR(r) <= '1';
                        elsif (IN_WF(r) = '0' and IN_SOF_ERR(r) = '1') then
                            OUT_SOF(r) <= '1';
                            OUT_EOF(r) <= '1';
                            OUT_ERR(r) <= IN_EOF_ERR(r);
                        else
                            OUT_SOF(r) <= '1';
                            OUT_EOF(r) <= '1';
                            OUT_ERR(r) <= '1';
                        end if;
                    else
                        OUT_SOF(r) <= IN_SOF(r);
                        OUT_EOF(r) <= IN_EOF(r);
                    end if;

                -- st_error
                when st_error =>
                    if (IN_SOF(r) = '0' and IN_EOF(r) = '1') then
                        OUT_EOF(r) <= '1';
                        OUT_ERR(r) <= '1';
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '0') then
                        OUT_SOF(r) <= '1';
                        OUT_EOF(r) <= '1';
                        OUT_ERR(r) <= '1';
                    elsif (IN_SOF(r) = '1' and IN_EOF(r) = '1' and s_any_error(r) = '1') then
                        if (IN_WF(r) = '1' or IN_DATA_ERR(r) = '1') then
                            OUT_EOF(r) <= '1';
                            OUT_ERR(r) <= '1';
                        else
                            OUT_SOF(r) <= '1';
                            OUT_EOF(r) <= '1';
                            OUT_ERR(r) <= '1';
                        end if;
                    else
                        OUT_ERR(r) <= '1';
                    end if;

                -- other states
                when others =>
                    OUT_SOF(r) <= '0';
                    OUT_EOF(r) <= '0';
                    OUT_ERR(r) <= '0';
            end case;
        end process;
    end generate;

end architecture;
