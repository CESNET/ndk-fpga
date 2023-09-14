-- barrel_proc_debug_core.vhd: For debugging the traffic coming through MFB
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- Note:

use work.math_pack.all;
use work.type_pack.all;

entity BARREL_PROC_DEBUG_CORE is
    generic(
        -- Width of MI bus
        MI_WIDTH : natural := 32
        );
    port(
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK   : in std_logic;
        RESET : in std_logic;

        RESET_OUT : out std_logic;

        -- =====================================================================
        -- MI interface for SW access
        -- =====================================================================
        MI_ADDR : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR  : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE   : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
        );
end entity;

architecture FULL of BARREL_PROC_DEBUG_CORE is

    -- =============================================================================================
    -- Reset FSM
    -- =============================================================================================
    signal rst_fsm_trigg : std_logic;
    type rst_fsm_state_t is (IDLE, RESET_COUNTING);
    signal rst_pst  : rst_fsm_state_t := IDLE;
    signal rst_nst  : rst_fsm_state_t := IDLE;
    signal rst_cntr_pst : unsigned(9 downto 0);
    signal rst_cntr_nst : unsigned(9 downto 0);

    -- attribute mark_debug                           : string;
    -- attribute mark_debug of rst_fsm_trigg        : signal is "true";
    -- attribute mark_debug of rst_pst        : signal is "true";
    -- attribute mark_debug of rst_cntr_pst        : signal is "true";
    -- attribute mark_debug of MI_ADDR        : signal is "true";
    -- attribute mark_debug of MI_DWR        : signal is "true";
    -- attribute mark_debug of MI_RD        : signal is "true";
    -- attribute mark_debug of MI_WR        : signal is "true";
    -- attribute mark_debug of MI_DRDY        : signal is "true";
begin

    MI_ARDY <= MI_RD or MI_WR;
    MI_DRD  <= (others => '0');
    MI_DRDY <= MI_RD;

    -- =============================================================================================
    -- Resetting FSM
    -- =============================================================================================
    rst_fsm_trigg <= '1' when (MI_WR = '1' and MI_ADDR(1 downto 0) = std_logic_vector(to_unsigned(16#00#,2)) and MI_DWR(0) = '1') else '0';
    reset_fsm_state_reg : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                rst_pst      <= IDLE;
                rst_cntr_pst <= (others => '0');
            else
                rst_pst      <= rst_nst;
                rst_cntr_pst <= rst_cntr_nst;
            end if;
        end if;
    end process;

    reset_fsm_nst_logic : process (all) is
    begin
        rst_nst      <= rst_pst;
        rst_cntr_nst <= rst_cntr_pst;

        RESET_OUT <= '0';

        case rst_pst is
            when IDLE =>

                if (rst_fsm_trigg = '1') then
                    rst_nst <= RESET_COUNTING;
                end if;

            when RESET_COUNTING =>
                RESET_OUT  <= '1';
                rst_cntr_nst <= rst_cntr_pst + 1;

                if (rst_cntr_pst = 1023) then
                    rst_nst <= IDLE;
                end if;
        end case;
    end process;
end architecture;
