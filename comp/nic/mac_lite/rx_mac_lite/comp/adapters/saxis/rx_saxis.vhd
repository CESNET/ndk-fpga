-- rx_saxis.vhd: Adapter between Segmented AXI-Stream and MFB
-- Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
--           (C) 2022 CESNET z. s. p. o.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
--            Jakub Cabal <cabal@cesnet.cz>
-- Adapted from component RX_MAC_LITE_ADAPTER_LBUS as Segmented AXI-Stream is
-- very similar to LBUS.
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_ADAPTER_SAXIS is
    generic (
        -- SEGMENTS must be 2 or 4
        SEGMENTS    : natural := 4;
        -- REGIONS must be 1
        REGIONS     : natural := 1;
        -- REGION_SIZE must be 2*SEGMENTS
        REGION_SIZE : natural := 2*SEGMENTS;
        -- Select correct FPGA device.
        DEVICE      : string := "VERSAL"
    );
    port (
        -- CLOCK AND RESET
        CLK              : in  std_logic;
        RESET            : in  std_logic;
        -- INPUT Segmented AXI-Stream
        IN_SAXIS_DATA    : in  slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
        IN_SAXIS_MTY     : in  slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
        IN_SAXIS_ENA     : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_SAXIS_SOP     : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_SAXIS_EOP     : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_SAXIS_ERR     : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_SAXIS_VALID   : in  std_logic;
        -- OUTPUT MFB (allowed MFB configurations: 1,4,8,8 and 1,8,8,8)
        OUT_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
        OUT_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        OUT_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_EOF_POS  : out std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
        OUT_MFB_ERROR    : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_SRC_RDY  : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_ADAPTER_SAXIS is

    signal in_saxis_data_ser : std_logic_vector(SEGMENTS*128-1 downto 0);
    signal in_saxis_sop_vld  : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_saxis_eop_vld  : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_saxis_err_vld  : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_saxis_sop_pos  : std_logic_vector(log2(SEGMENTS)-1 downto 0);
    signal in_saxis_eop_pos  : slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
    signal mfb_sof_pos_comp  : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal mfb_eof_pos_comp  : std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);

begin
    assert SEGMENTS = 2 or SEGMENTS = 4
        report "RX_MAC_LITE_ADAPTER_SAXIS: SEGMENTS generic must be 2 or 4. Actual value is: " & natural'image(SEGMENTS)
        severity failure;
    assert REGIONS = 1
        report "RX_MAC_LITE_ADAPTER_SAXIS: REGIONS generic must be 1. Actual value is: " & natural'image(REGIONS)
        severity failure;
    assert REGION_SIZE = 2*SEGMENTS
        report "RX_MAC_LITE_ADAPTER_SAXIS: REGION_SIZE generic must be 2*SEGMENTS (" & natural'image(2*SEGMENTS) & "). Actual value is: " & natural'image(REGION_SIZE)
        severity failure;

    -- DCMAC sends byte 0 of each segment in bits 7:0, so no byte rotation is needed (PG369).
    in_saxis_data_ser <= slv_array_ser(IN_SAXIS_DATA);
    in_saxis_sop_vld  <= IN_SAXIS_SOP and IN_SAXIS_ENA and IN_SAXIS_VALID;
    in_saxis_eop_vld  <= IN_SAXIS_EOP and IN_SAXIS_ENA and IN_SAXIS_VALID;
    in_saxis_err_vld  <= IN_SAXIS_ERR and in_saxis_eop_vld;

    process (all)
    begin
        in_saxis_sop_pos <= (others => '0');
        for i in 0 to SEGMENTS-1 loop
            if (in_saxis_sop_vld(i) = '1') then
                in_saxis_sop_pos <= std_logic_vector(to_unsigned(i,in_saxis_sop_pos'length));
            end if;
        end loop;
    end process;

    mfb_sof_pos_comp <= in_saxis_sop_pos & '0';

    saxis_eop_pos_g : for s in 0 to SEGMENTS-1 generate
        in_saxis_eop_pos(s) <= std_logic_vector(15-unsigned(IN_SAXIS_MTY(s)));
    end generate;

    process (all)
    begin
        mfb_eof_pos_comp <= (others => '0');
        for i in 0 to SEGMENTS-1 loop
            if (in_saxis_eop_vld(i) = '1') then
                mfb_eof_pos_comp <= std_logic_vector(to_unsigned(i,log2(SEGMENTS))) & in_saxis_eop_pos(i);
            end if;
        end loop;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            OUT_MFB_DATA     <= in_saxis_data_ser;
            OUT_MFB_SOF(0)   <= or in_saxis_sop_vld;
            OUT_MFB_SOF_POS  <= mfb_sof_pos_comp;
            OUT_MFB_EOF(0)   <= or in_saxis_eop_vld;
            OUT_MFB_EOF_POS  <= mfb_eof_pos_comp;
            OUT_MFB_ERROR(0) <= or in_saxis_err_vld;
            OUT_MFB_SRC_RDY  <= IN_SAXIS_VALID;
            if (RESET = '1') then
                OUT_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
