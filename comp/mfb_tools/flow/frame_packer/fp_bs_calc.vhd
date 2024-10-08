-- fp_bs_calc.vhd: BarrelShifter calculator - calculation of select signal
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The purpose of this component is to generate select signal for each Barrel Shifter
entity FP_BS_CALC is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        BS_NUM              : natural := 0;
        RX_CHANNELS         : natural := 16
    );
    port(
        RX_SOF_POS_UNS  : in  unsigned(max(1,log2(MFB_REGION_SIZE)) - 1 downto 0);

        -- Select correct channel pointer based on current channel
        -- 4 regions: max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))
        RX_CH_PTR_UNS   : in  u_array_t(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);

        -- Select correct number (sum of previous BSs) based on the current channel
        RX_SUM_PREV_UNS : in  u_array_t(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
        RX_BS_CHANNEL   : in  std_logic_vector(max(1,log2(RX_CHANNELS)) - 1 downto 0);

        TX_SEL          : out std_logic_vector(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0)
    );
end entity;

architecture FULL of FP_BS_CALC is
    signal sum  : unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);

    -- Previous SUM
    signal sum_prev_slv : slv_array_t(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
    signal sum_prev_std : std_logic_vector(RX_CHANNELS*(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1) - 1 downto 0);
    signal sum_mux_std  : std_logic_vector(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);

    -- Channel pointer
    signal ch_ptr_slv   : slv_array_t(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
    signal ch_ptr_std   : std_logic_vector(RX_CHANNELS*max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
    signal ch_ptr_mux   : std_logic_vector(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);

begin
    -- u_array_t   => slv_array_t
    uns_to_slv_g: for i in 0 to RX_CHANNELS - 1 generate
        sum_prev_slv(i)    <= std_logic_vector(RX_SUM_PREV_UNS(i));
    end generate;

    -- slv_array_t => std_logic_vector
    sum_prev_std    <= slv_array_ser(sum_prev_slv);

    -- Channel MUX
    bs_mux_i: entity work.GEN_MUX
        generic map(
           DATA_WIDTH  => max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1,
           MUX_WIDTH   => RX_CHANNELS
        )
        port map(
           DATA_IN     => sum_prev_std,
           SEL         => RX_BS_CHANNEL,
           DATA_OUT    => sum_mux_std
    );

    -- u_array_t   => slv_array_t
    uns_to_slv_ptr_g: for i in 0 to RX_CHANNELS - 1 generate
        ch_ptr_slv(i)    <= std_logic_vector(RX_CH_PTR_UNS(i));
    end generate;

    ch_ptr_std  <= slv_array_ser(ch_ptr_slv);

    -- Pointer MUX
    ch_ptr_mux_i: entity work.GEN_MUX
        generic map(
            DATA_WIDTH  => max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)),
            MUX_WIDTH   => RX_CHANNELS
        )
        port map(
            DATA_IN     => ch_ptr_std,
            SEL         => RX_BS_CHANNEL,
            DATA_OUT    => ch_ptr_mux
    );

    sum     <= to_unsigned(BS_NUM*MFB_REGION_SIZE, sum'length) + RX_SOF_POS_UNS - unsigned(ch_ptr_mux) - unsigned(sum_mux_std);
    TX_SEL  <= std_logic_vector(sum(sum'high - 1 downto 0));
end architecture;
