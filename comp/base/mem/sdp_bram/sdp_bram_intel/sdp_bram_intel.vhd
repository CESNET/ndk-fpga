-- sdp_bram_intel.vhd: sdp_bram_intel
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

library altera_lnsim;
use altera_lnsim.altera_lnsim_components.all;

architecture FULL of SDP_BRAM_INTEL is

    constant ADDR_WIDTH           : natural := log2(ITEMS);
    constant INTEL_PORTB_CLK      : string  := tsel(COMMON_CLOCK,"CLOCK0","CLOCK1");
    constant INTEL_REGB_CONF      : string  := tsel(OUTPUT_REG,INTEL_PORTB_CLK,"UNREGISTERED");
    constant INTEL_CE_REGB_CONF   : string  := tsel(OUTPUT_REG,"NORMAL","BYPASS");
    constant INTEL_RDWMMP_CONF    : string  := tsel(COMMON_CLOCK,"OLD_DATA","DONT_CARE");
    constant INTEL_WR_BE_WIDTH    : natural := tsel(BLOCK_ENABLE,(DATA_WIDTH/BLOCK_WIDTH),1);
    constant INTEL_BLOCK_WIDTH    : natural := tsel(BLOCK_ENABLE,BLOCK_WIDTH,8);

    signal rd_pipe_en_internal : std_logic;
    signal rd_addr_internal    : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal wr_clk_internal     : std_logic;
    signal wr_en_internal      : std_logic;
    signal wr_addr_internal    : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal wr_data_internal    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal intel_clock1        : std_logic;
    signal intel_clocken1      : std_logic;
    signal intel_wr_be         : std_logic_vector(INTEL_WR_BE_WIDTH-1 downto 0);

begin

    assert ((DEVICE = "STRATIX10") or (DEVICE = "ARRIA10") or (DEVICE = "AGILEX"))
        report "SDP_BRAM_INTEL: Illegal value of parameter DEVICE '" & DEVICE & "'; allowed devices are: STRATIX10, ARRIA10, AGILEX!"
        severity failure;

    intel_g : if (DEVICE = "STRATIX10") or (DEVICE = "ARRIA10") or (DEVICE = "AGILEX") generate
        wr_clk_internal <= WR_CLK;

        -- needed to synchronise signal assign delay with RD_CLK in ModelSim
        rd_pipe_en_internal <= RD_PIPE_EN;
        rd_addr_internal    <= RD_ADDR;
        wr_en_internal      <= WR_EN;
        wr_addr_internal    <= WR_ADDR;
        wr_data_internal    <= WR_DATA;

        clock1_g : if COMMON_CLOCK generate
            intel_clock1   <= '1';
            intel_clocken1 <= '1';
        else generate
            intel_clock1   <= RD_CLK;
            intel_clocken1 <= RD_PIPE_EN;
        end generate;

        dev_be_g : if BLOCK_ENABLE generate
            intel_wr_be <= WR_BE;
        else generate
            intel_wr_be <= (others => '1');
        end generate;

        bram_i : altera_syncram
        generic map (
            address_aclr_b                     => "NONE",
            address_reg_b                      => INTEL_PORTB_CLK,
            byte_size                          => INTEL_BLOCK_WIDTH,
            clock_enable_input_a               => "BYPASS",
            clock_enable_input_b               => "BYPASS",
            clock_enable_output_b              => INTEL_CE_REGB_CONF,
            enable_force_to_zero               => "FALSE",
            intended_device_family             => DEVICE,
            lpm_type                           => "altera_syncram",
            numwords_a                         => ITEMS,
            numwords_b                         => ITEMS,
            operation_mode                     => "DUAL_PORT",
            outdata_aclr_b                     => "NONE",
            outdata_sclr_b                     => "NONE",
            outdata_reg_b                      => INTEL_REGB_CONF,
            power_up_uninitialized             => "FALSE",
            ram_block_type                     => "M20K",
            rdcontrol_reg_b                    => INTEL_PORTB_CLK,
            read_during_write_mode_mixed_ports => INTEL_RDWMMP_CONF,
            read_during_write_mode_port_a      => INTEL_RDWMMP_CONF,
            read_during_write_mode_port_b      => INTEL_RDWMMP_CONF,
            widthad_a                          => ADDR_WIDTH,
            widthad_b                          => ADDR_WIDTH,
            width_a                            => DATA_WIDTH,
            width_b                            => DATA_WIDTH,
            width_byteena_a                    => INTEL_WR_BE_WIDTH
        )
        port map (
            address_a      => wr_addr_internal,
            address_b      => rd_addr_internal,
            byteena_a      => intel_wr_be,
            clock0         => wr_clk_internal,
            clocken0       => rd_pipe_en_internal,
            clock1         => intel_clock1,
            clocken1       => intel_clocken1,
            data_a         => wr_data_internal,
            rden_b         => rd_pipe_en_internal,
            wren_a         => wr_en_internal,
            q_b            => RD_DATA
        );

    end generate;

end architecture;
