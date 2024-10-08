-- rx_lbus.vhd:
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_ADAPTER_LBUS is
    generic(
        -- SEGMENTS must be 4
        SEGMENTS    : natural := 4;
        -- REGIONS must be 1
        REGIONS     : natural := 1;
        -- REGION_SIZE must be 2*SEGMENTS;
        REGION_SIZE : natural := 2*SEGMENTS;
        -- Select correct FPGA device.
        DEVICE      : string := "ULTRASCALE"
    );
    port(
        -- CLOCK AND RESET
        CLK              : in  std_logic;
        RESET            : in  std_logic;
        -- INPUT LBUS
        IN_LBUS_DATA     : in  slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
        IN_LBUS_MTY      : in  slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
        IN_LBUS_ENA      : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_LBUS_SOP      : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_LBUS_EOP      : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_LBUS_ERR      : in  std_logic_vector(SEGMENTS-1 downto 0);
        -- OUTPUT MFB (allowed MFB configurations: 1,8,8,8)
        OUT_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
        OUT_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        OUT_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_EOF_POS  : out std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
        OUT_MFB_ERROR    : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_SRC_RDY  : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_ADAPTER_LBUS is

    constant BYTES : natural := 128/8;

    signal in_lbus_data_rot : slv_array_t(SEGMENTS-1 downto 0)(128-1 downto 0);
    signal in_lbus_data_ser : std_logic_vector(SEGMENTS*128-1 downto 0);
    signal in_lbus_sop_vld  : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_lbus_eop_vld  : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_lbus_err_vld  : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_lbus_sop_pos  : std_logic_vector(log2(SEGMENTS)-1 downto 0);
    signal in_lbus_eop_pos  : slv_array_t(SEGMENTS-1 downto 0)(4-1 downto 0);
    signal mfb_sof_pos_comp : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal mfb_eof_pos_comp : std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);

begin

    rx_data_rotate_g : for s in 0 to SEGMENTS-1 generate
        rx_data_rotate_g2 : for i in 0 to BYTES-1 generate
            in_lbus_data_rot(s)((i+1)*8-1 downto i*8) <= IN_LBUS_DATA(s)((BYTES-1-i+1)*8-1 downto (BYTES-1-i)*8);
        end generate;
    end generate;

    in_lbus_data_ser <= slv_array_ser(in_lbus_data_rot);

    in_lbus_sop_vld <= IN_LBUS_SOP and IN_LBUS_ENA;
    in_lbus_eop_vld <= IN_LBUS_EOP and IN_LBUS_ENA;
    in_lbus_err_vld <= IN_LBUS_ERR and in_lbus_eop_vld;

    process (all)
    begin
        in_lbus_sop_pos <= (others => '0');
        for i in 0 to SEGMENTS-1 loop
            if (in_lbus_sop_vld(i) = '1') then
                in_lbus_sop_pos <= std_logic_vector(to_unsigned(i,in_lbus_sop_pos'length));
            end if;
        end loop;
    end process;

    mfb_sof_pos_comp <= in_lbus_sop_pos & '0';

    lbus_eop_pos_g : for s in 0 to SEGMENTS-1 generate
        in_lbus_eop_pos(s) <= std_logic_vector(15-unsigned(IN_LBUS_MTY(s)));
    end generate;

    process (all)
    begin
        mfb_eof_pos_comp <= (others => '0');
        for i in 0 to SEGMENTS-1 loop
            if (in_lbus_eop_vld(i) = '1') then
                mfb_eof_pos_comp <= std_logic_vector(to_unsigned(i,log2(SEGMENTS))) & in_lbus_eop_pos(i);
            end if;
        end loop;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            OUT_MFB_DATA     <= in_lbus_data_ser;
            OUT_MFB_SOF(0)   <= or in_lbus_sop_vld;
            OUT_MFB_SOF_POS  <= mfb_sof_pos_comp;
            OUT_MFB_EOF(0)   <= or in_lbus_eop_vld;
            OUT_MFB_EOF_POS  <= mfb_eof_pos_comp;
            OUT_MFB_ERROR(0) <= or in_lbus_err_vld;
            OUT_MFB_SRC_RDY  <= or IN_LBUS_ENA;
            if (RESET = '1') then
                OUT_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
