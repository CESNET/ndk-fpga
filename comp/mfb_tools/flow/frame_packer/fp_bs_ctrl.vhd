-- fp_bs_ctrl.vhd: Unit for generating select signal
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
entity FP_BS_CTRL is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        RX_CHANNELS         : natural := 16
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        -- Valid per packet
        RX_BLOCK_VLD    : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- SOF_POS per BS
        RX_SOF_POS_BS   : in  slv_array_t(MFB_REGIONS downto 0)(max(1,log2(MFB_REGION_SIZE)) - 1 downto 0);
        -- Pointer per Channel
        RX_CH_PTR       : in  u_array_t(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
        -- SRC_RDY per channel
        RX_SRC_RDY      : in  std_logic;
        -- Channel per BS
        RX_CHANNEL_BS   : in  slv_array_t(MFB_REGIONS downto 0)(max(1,log2(RX_CHANNELS)) - 1 downto 0);

        -- Select signal for each BS
        TX_SEL          : out slv_array_t(MFB_REGIONS downto 0)(max(1, log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
        -- Pointrer increment per channel (unsigned array)
        TX_PTR_INC      : out u_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
        -- SRC_RDY per channel
        TX_SRC_RDY      : out std_logic_vector(RX_CHANNELS - 1 downto 0);
        -- External demux select
        TX_CHANNEL_BS   : out slv_array_t(MFB_REGIONS downto 0)(max(1,log2(RX_CHANNELS)) - 1 downto 0)
    );
end entity;

architecture FULL of FP_BS_CTRL is
    signal vld_sum_std          : slv_array_t(MFB_REGIONS downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
    signal sof_pos_uns          : u_array_t(MFB_REGIONS downto 0)(max(1,log2(MFB_REGION_SIZE)) - 1 downto 0);

    -- Demux
    signal vld_sum_std_demux    : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS*(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1) - 1 downto 0);
    signal vld_sum_std_demux_2d : slv_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)((max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1) - 1 downto 0);
    signal vld_sum_uns_demux_2d : u_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)((max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1) - 1 downto 0);

    signal vld_sum_per_bs       : u_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
    signal src_rdy_per_bs       : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0);
begin
    -- Transfor VLD array to numbers
    vld_to_std_g: for i in 0 to MFB_REGIONS generate
        vld_sum_std(i) <= std_logic_vector(to_unsigned(count_ones(RX_BLOCK_VLD(i)), max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1));
    end generate;

    -- Demux each BS increment number to the correct channel
    inc_demux_g: for i in 0 to MFB_REGIONS generate
        inc_demux_i: entity work.GEN_DEMUX
            generic map(
                DATA_WIDTH  => max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1,
                DEMUX_WIDTH => RX_CHANNELS,
                DEF_VALUE   => '0'
            )
            port map(
                DATA_IN     => vld_sum_std(i),
                SEL         => RX_CHANNEL_BS(i),
                DATA_OUT    => vld_sum_std_demux(i)
        );
    end generate;

    -- Convert demuxed data to friendly format
    demux_per_bs_g: for i in 0 to MFB_REGIONS generate
        vld_sum_std_demux_2d(i) <= slv_array_deser(vld_sum_std_demux(i), RX_CHANNELS);
    end generate;

    convert_to_uns_per_BS_g: for i in 0 to MFB_REGIONS generate
        convert_to_uns_per_ch_g: for j in 0 to RX_CHANNELS - 1 generate
            vld_sum_uns_demux_2d(i)(j)  <= unsigned(vld_sum_std_demux_2d(i)(j));
        end generate;
    end generate;

    -- STD -> UNS conversion
    sof_to_uns_g: for i in 0 to MFB_REGIONS generate
        sof_pos_uns(i) <= unsigned(RX_SOF_POS_BS(i));
    end generate;

    -- Sum of valid bits per BS and per channel
    vld_sum_per_bs(0)   <= (others => (others => '0'));
    sum_per_bs_g: for i in 0 to MFB_REGIONS - 1 generate
        sum_per_ch_g: for j in 0 to RX_CHANNELS - 1 generate
            vld_sum_per_bs(i + 1)(j)   <= vld_sum_per_bs(i)(j) + vld_sum_uns_demux_2d(i)(j);
        end generate;
    end generate;

    -- Calculation for each BS
    bs_calc_g: for i in 0 to MFB_REGIONS generate
        bs_calc_i: entity work.FP_BS_CALC
            generic map(
                MFB_REGIONS     => MFB_REGIONS,
                MFB_REGION_SIZE => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

                BS_NUM          => max(0, i - 1),
                RX_CHANNELS     => RX_CHANNELS
            )
            port map(
                RX_SOF_POS_UNS  => sof_pos_uns(i),
                RX_CH_PTR_UNS   => RX_CH_PTR,
                RX_SUM_PREV_UNS => vld_sum_per_bs(i),
                RX_BS_CHANNEL   => RX_CHANNEL_BS(i),

                TX_SEL          => TX_SEL(i)
            );
    end generate;

    -- Pointer increment
    ptr_inc_per_bs_g: for i in 0 to MFB_REGIONS generate
        ptr_inc_per_ch_g: for j in 0 to RX_CHANNELS - 1 generate
            TX_PTR_INC(j)(i)  <= vld_sum_uns_demux_2d(i)(j);
        end generate;
    end generate;

    -- Only selected channels gets SRC_RDY
    src_rdy_per_ch_g: for i in 0 to RX_CHANNELS - 1 generate
        src_rdy_per_bs_g: for j in 0 to MFB_REGIONS generate
            src_rdy_per_bs(j)(i) <= '1' when (RX_CHANNEL_BS(j) = std_logic_vector(to_unsigned(i, max(1,log2(RX_CHANNELS))))) and (RX_SRC_RDY = '1') else '0';
        end generate;
    end generate;

    -- SRC_RDY channel redistribution
    out_src_rdy_p: process(all)
        variable src_rdy_per_bs_v   : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0);
    begin
        src_rdy_per_bs_v    := (others => (others => '0'));
        src_rdy_per_bs_v(0) := src_rdy_per_bs(0);
        for i in 0 to RX_CHANNELS - 1 loop
            for j in 1 to MFB_REGIONS loop
                src_rdy_per_bs_v(j)(i)    := src_rdy_per_bs(j)(i) or src_rdy_per_bs_v(j - 1)(i);
            end loop;
        end loop;

        TX_SRC_RDY  <= src_rdy_per_bs_v(src_rdy_per_bs_v'high);
    end process;

    channel_sel_sync_p: process(all)
    begin
        if rising_edge(CLK) then
            TX_CHANNEL_BS <= RX_CHANNEL_BS;
        end if;
    end process;

end architecture;
