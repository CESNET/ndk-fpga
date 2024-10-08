-- altdpram_wrap.vhd: altdpram wrapper
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

library altera_mf;
use altera_mf.altera_mf_components.all;

architecture FULL of ALTDPRAM_WRAP is

    constant ALTDPRAM_ITEMS         : natural := 2**ADDR_WIDTH;
    constant ALTDPRAM_RDW_DONT_CARE : string := tsel(RDW_CONSTRAINED,"CONSTRAINED_DONT_CARE","DONT_CARE");
    constant ALTDPRAM_OUTPUT_REG    : string := tsel(OUTPUT_REG,"INCLOCK","UNREGISTERED");

begin

    altdpram_i : altdpram
    generic map (
        indata_aclr                        => "OFF",
        indata_reg                         => "INCLOCK",
        intended_device_family             => DEVICE,
        lpm_type                           => "altdpram",
        ram_block_type                     => RAM_TYPE,
        outdata_aclr                       => "OFF",
        outdata_sclr                       => "OFF",
        outdata_reg                        => ALTDPRAM_OUTPUT_REG,
        rdaddress_aclr                     => "OFF",
        rdaddress_reg                      => "UNREGISTERED",
        rdcontrol_aclr                     => "OFF",
        rdcontrol_reg                      => "UNREGISTERED",
        read_during_write_mode_mixed_ports => ALTDPRAM_RDW_DONT_CARE,
        numwords                           => ALTDPRAM_ITEMS,
        width                              => DATA_WIDTH,
        widthad                            => ADDR_WIDTH,
        width_byteena                      => 1,
        wraddress_aclr                     => "OFF",
        wraddress_reg                      => "INCLOCK",
        wrcontrol_aclr                     => "OFF",
        wrcontrol_reg                      => "INCLOCK"
    )
    PORT MAP (
        data           => DATA,
        inclock        => INCLOCK,
        rdaddress      => RDADDRESS,
        wraddress      => WRADDRESS,
        wren           => WREN,
        q              => Q
    );

end architecture;
