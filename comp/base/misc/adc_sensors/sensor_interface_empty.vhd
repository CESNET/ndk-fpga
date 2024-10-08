-- sensor_interface.vhd: An interface to the ADC IP Temperature and Voltage Cores for Stratix 10
-- Copyright (C) 2019 CESNET
-- Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture ARCH of SENSOR_INTERFACE is

begin

    ARDY <= RD or WR;

    process(CLK)
    begin
        if (rising_edge(CLK)) then
            DRD  <= X"DEADCAFE";
            DRDY <= RD;
            if (RESET='1') then
                DRDY <= '0';
            end if;
        end if;
    end process;

end architecture;
