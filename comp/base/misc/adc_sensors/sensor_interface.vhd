-- sensor_interface.vhd: An interface to the ADC IP Temperature and Voltage Cores for Stratix 10
-- Copyright (C) 2019 CESNET
-- Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- Sources
-- https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-adc.pdf
-- https://www.liberouter.org/wiki/index.php/Byte_Enable
-- https://www.liberouter.org/wiki/index.php/Endpoint_komponenta_Lok%C3%A1ln%C3%AD_sb%C4%9Brnice

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity SENSOR_INTERFACE is
    Generic (
        VERI : boolean := false -- if the entity is being used in a verification or not
    );
    Port (
        -- =======================================================================
        -- CONTROL SIGNALS
        -- =======================================================================
        CLK   : in  std_logic;
        RESET : in  std_logic;
        -- =======================================================================
        --  MI32 IN
        -- =======================================================================
        -- Data for W
        DWR  : in std_logic_vector(31 downto 0);
        -- Address for R\W
        ADDR : in std_logic_vector(31 downto 0);
        -- Read request
        RD   : in std_logic;
        -- Write request
        WR   : in std_logic;
        -- Byte enable
        BE   : in std_logic_vector(3 downto 0);
        -- =======================================================================
        --  MI32 OUT
        -- =======================================================================
        -- Data for R
        DRD  : out std_logic_vector(31 downto 0);
        -- conf_regirmation about receiving ADDR
        ARDY : out std_logic;
        -- conf_regirmation about DRD
        DRDY : out std_logic
    );
end entity;
