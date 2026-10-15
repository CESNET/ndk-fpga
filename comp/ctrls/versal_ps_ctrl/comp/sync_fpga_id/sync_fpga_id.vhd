-- sync_fpga_id.vhd: Synchronize FPGA ID from FPGA_ID clock domain to core
--                   clock domain
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity SYNC_FPGA_ID is
    generic (
        -- Are clocks CLK and FPGA_ID_CLK same
        SAME_CLOCKS        : boolean := false;
        -- Target FPGA
        -- Options: "STRATIX10", "AGILEX", "ULTRASCALE", "7SERIES", "VERSAL"
        DEVICE             : string  := "AGILEX";
        -- Width of FPGA ID
        FPGA_ID_WIDTH      : natural := 64
    );
    port (
        -- Clock and reset
        CLK              :  in std_logic;
        RESET            :  in std_logic;
        FPGA_ID_CLK      :  in std_logic;
        FPGA_ID_RESET    :  in std_logic;

        -- FPGA ID from NDK (clocked on FPGA_ID_CLK)
        FPGA_ID          :  in std_logic_vector(FPGA_ID_WIDTH-1 downto 0);
        FPGA_ID_VLD      :  in std_logic;

        -- Synchronised FPGA ID (clocked on CLK)
        SYNC_FPGA_ID     : out std_logic_vector(FPGA_ID_WIDTH-1 downto 0);
        SYNC_FPGA_ID_VLD : out std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                     Architecture: full
-- ----------------------------------------------------------------------------
architecture FULL of SYNC_FPGA_ID is
    signal sync_fpga_id_out     : std_logic_vector(FPGA_ID_WIDTH-1 downto 0) := (others => '0');
    signal sync_fpga_id_vld_out : std_logic := '0';
    signal sync_fpga_id_vld_int : std_logic := '0';
begin
    gen_sync_g: if SAME_CLOCKS generate
        -- If clocks are same, pipeline register is generated
        pipeline_register : process (CLK)
        begin
            if rising_edge(CLK) then
                sync_fpga_id_out     <= FPGA_ID;
                sync_fpga_id_vld_out <= FPGA_ID_VLD;
            end if;
        end process;
    else generate
        -- If clocks are different generate CDC
        -- CDC for FPGA_ID_VLD signal
        cdc_fpga_id_vld_i: entity work.ASYNC_OPEN_LOOP
        generic map (
            IN_REG  => true,
            TWO_REG => false
        )
        port map (
            ACLK     => FPGA_ID_CLK,
            BCLK     => CLK,
            ARST     => FPGA_ID_RESET,
            BRST     => RESET,
            ADATAIN  => FPGA_ID_VLD,
            BDATAOUT => sync_fpga_id_vld_int
        );
        -- Delay FPGA_ID_VLD to offset any problems caused by simple CDC for
        -- FPGA_ID
        sh_reg_i: entity work.SH_REG_BASE_STATIC
        generic map (
            DATA_WIDTH      => 1,
            -- number of bits save in srl register
            NUM_BITS        => 6,
            INIT_TYPE       => 0,
            IS_CLK_INVERTED => '0',
            OPT             => "REG",
            DEVICE          => DEVICE
        )
        port map (
            CLK      => CLK,
            CE       => '1',

            DIN(0)   => sync_fpga_id_vld_int,
            DOUT(0)  => sync_fpga_id_vld_out
        );
        -- CDC for FPGA_ID
        cdc_fpga_id_i: entity work.ASYNC_OPEN_LOOP_SMD
        generic map (
            DATA_WIDTH => FPGA_ID_WIDTH
        )
        port map (
            ACLK     => FPGA_ID_CLK,
            BCLK     => CLK,
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => FPGA_ID,
            BDATAOUT => sync_fpga_id_out
        );
    end generate;

    SYNC_FPGA_ID     <= sync_fpga_id_out;
    SYNC_FPGA_ID_VLD <= sync_fpga_id_vld_out;
end architecture;
