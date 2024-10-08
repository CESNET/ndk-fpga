-- sdm_ctrl_s10_adc.vhd:
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture S10_ADC of SDM_CTRL is

begin

    sensor_interface_i: entity work.SENSOR_INTERFACE
    Generic map (
        VERI => false
    )
    Port map (
        CLK   => CLK,
        RESET => RESET,
        DWR   => MI_DWR,
        ADDR  => MI_ADDR,
        RD    => MI_RD,
        WR    => MI_WR,
        BE    => MI_BE,
        DRD   => MI_DRD,
        ARDY  => MI_ARDY,
        DRDY  => MI_DRDY
    );

    CHIP_ID <= X"0ADCDEAD0ADCDEAD";

end architecture;
