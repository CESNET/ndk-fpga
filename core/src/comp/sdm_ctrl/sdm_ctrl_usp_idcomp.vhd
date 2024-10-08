-- sdm_ctrl_usp_idcomp.vhd:
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture USP_IDCOMP of SDM_CTRL is

begin

    id_comp_i : entity work.ID_COMP_MI32_NOREC
    generic map (
        SYSMON_EN => true
    )
    port map (
        CLK           => CLK,
        RESET         => RESET,
        COMMAND       => open,
        STATUS        => X"00000000000000000000000000000000",
        WE            => "1111",
        REPEATER      => open,
        SYSMON_ALARM  => open,
        INTERRUPT_IN  => (others => '0'),
        INTR_RDY_IN   => open,
        INTERRUPT_OUT => open,
        INTR_SENT     => '0',
        MI_DWR        => MI_DWR,
        MI_ADDR       => MI_ADDR,
        MI_RD         => MI_RD,
        MI_WR         => MI_WR,
        MI_BE         => MI_BE,
        MI_DRD        => MI_DRD,
        MI_ARDY       => MI_ARDY,
        MI_DRDY       => MI_DRDY
    );

end architecture;
