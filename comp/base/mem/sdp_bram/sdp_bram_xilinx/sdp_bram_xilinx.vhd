-- sdp_bram_xilinx.vhd: SDP_BRAM_XILINX
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

library xpm;
use xpm.vcomponents.all;

architecture FULL of SDP_BRAM_XILINX2 is

    constant ADDR_WIDTH           : natural := log2(ITEMS);
    constant XILINX_BLOCK_WIDTH   : natural := tsel(BLOCK_ENABLE,BLOCK_WIDTH,DATA_WIDTH);
    constant XILINX_CLOCKING_MODE : string  := tsel(COMMON_CLOCK,"common_clock","independent_clock");
    constant XILINX_READ_LATENCY  : natural := tsel(OUTPUT_REG,2,1);

    signal xilinx_we           : std_logic_vector((DATA_WIDTH/XILINX_BLOCK_WIDTH)-1 downto 0);

begin

    assert ((DEVICE = "7SERIES") or (DEVICE = "ULTRASCALE"))
        report "SDP_BRAM_XILINX2: Illegal value of parameter DEVICE '" & DEVICE & "'; allowed devices are: 7SERIES, ULTRASCALE!"
        severity failure;

    xilinx_g : if (DEVICE = "7SERIES") or (DEVICE = "ULTRASCALE") generate
        dev_be_g : if BLOCK_ENABLE generate
            xilinx_we <= WR_BE;
        else generate
            xilinx_we(0) <= WR_EN;
        end generate;

        -- use Xilinx XPM macro (UG974)
        bram_i : XPM_MEMORY_SDPRAM
        generic map (
            ADDR_WIDTH_A            => ADDR_WIDTH,
            ADDR_WIDTH_B            => ADDR_WIDTH,
            AUTO_SLEEP_TIME         => 0,
            BYTE_WRITE_WIDTH_A      => XILINX_BLOCK_WIDTH,
            CLOCKING_MODE           => XILINX_CLOCKING_MODE,
            ECC_MODE                => "no_ecc",
            MEMORY_INIT_FILE        => "none",
            MEMORY_INIT_PARAM       => "0",
            MEMORY_OPTIMIZATION     => "true",
            MEMORY_PRIMITIVE        => "block",
            MEMORY_SIZE             => (2**ADDR_WIDTH)*DATA_WIDTH,
            MESSAGE_CONTROL         => 0,
            READ_DATA_WIDTH_B       => DATA_WIDTH,
            READ_LATENCY_B          => XILINX_READ_LATENCY,
            READ_RESET_VALUE_B      => "0",
            USE_EMBEDDED_CONSTRAINT => 0,
            USE_MEM_INIT            => 0,
            WAKEUP_TIME             => "disable_sleep",
            WRITE_DATA_WIDTH_A      => DATA_WIDTH,
            WRITE_MODE_B            => "read_first"
        )
        port map (
            dbiterrb       => open,
            doutb          => RD_DATA,
            sbiterrb       => open,
            addra          => WR_ADDR,
            addrb          => RD_ADDR,
            clka           => WR_CLK,
            clkb           => RD_CLK,
            dina           => WR_DATA,
            ena            => WR_EN,
            enb            => RD_PIPE_EN,
            injectdbiterra => '0',
            injectsbiterra => '0',
            regceb         => RD_PIPE_EN,
            rstb           => '0',
            sleep          => '0',
            wea            => xilinx_we
        );
    end generate;

end architecture;
