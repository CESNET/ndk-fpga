-- jtag_op_ctrl_arch.vhd : JTAG-Over-Protocol controller architecture
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture FULL of JTAG_OP_CTRL is
begin

    jop_g: if JOP_ENABLE generate
        jop_i: entity work.JTAG_OP_CLIENT
        generic map (
            MI_ADDR_WIDTH => MI_ADDR_WIDTH,
            MI_DATA_WIDTH => MI_DATA_WIDTH,
            DEVICE        => DEVICE
        )
        port map (
            USER_CLK      => USER_CLK,
            USER_RESET    => USER_RESET,
            JOP_CLK       => JOP_CLK,
            JOP_RESET     => JOP_RESET,
            MI_DWR        => MI_DWR,
            MI_ADDR       => MI_ADDR,
            MI_RD         => MI_RD,
            MI_WR         => MI_WR,
            MI_BE         => MI_BE,
            MI_DRD        => MI_DRD,
            MI_ARDY       => MI_ARDY,
            MI_DRDY       => MI_DRDY
        );
    else generate
        MI_ARDY <= MI_RD or MI_WR;
        MI_DRDY <= MI_RD;
        MI_DRD  <= X"DEADDEAD";
    end generate;

end architecture;
