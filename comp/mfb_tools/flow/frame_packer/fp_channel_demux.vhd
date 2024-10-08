-- fp_channel_demux.vhd: Unit for correct distribution of signals to FP_Channels
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The purpose of this component to route data to its channel
entity FP_CHANNEL_DEMUX is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        RX_CHANNELS         : natural := 16;
        RX_PKT_SIZE_MAX     : natural := 2**10
    );
    port(
        RX_CHANNEL_BS   : in  slv_array_t(MFB_REGIONS downto 0)(max(1,log2(RX_CHANNELS)) - 1 downto 0);

        RX_DATA         : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_PKT_LNG      : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX+1))- 1 downto 0);
        RX_BLOCK_VLD    : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_SOF_ONE_HOT  : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_EOF_ONE_HOT  : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

        TX_DATA         : out slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_BLOCK_VLD    : out slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        TX_SOF_ONE_HOT  : out slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        TX_EOF_ONE_HOT  : out slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        TX_PKT_LNG      : out slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0)
    );
end entity;

architecture FULL of FP_CHANNEL_DEMUX is
    signal item_eof_pos : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(MFB_ITEM_WIDTH)) - 1 downto 0);

    signal data_demux               : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS*MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH - 1 downto 0);
    signal block_vld_demux          : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS*MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal sof_one_hot_demux        : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS*MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal eof_one_hot_demux        : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS*MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal pkt_lng_demux            : slv_array_t(MFB_REGIONS downto 0)(RX_CHANNELS*MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

    signal data_demux_arr           : slv_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH - 1 downto 0);
    signal block_vld_demux_arr      : slv_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal eof_one_hot_demux_arr    : slv_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal sof_one_hot_demux_arr    : slv_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal pkt_lng_demux_arr        : slv_array_2d_t(MFB_REGIONS downto 0)(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

begin

    demux_g: for i in 0 to MFB_REGIONS generate
        data_demux_i: entity work.GEN_DEMUX
            generic map(
                DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,
                DEMUX_WIDTH => RX_CHANNELS,
                DEF_VALUE   => '0'
            )
            port map(
                DATA_IN     => RX_DATA(i),
                SEL         => RX_CHANNEL_BS(i),
                DATA_OUT    => data_demux(i)
        );
        data_demux_arr(i) <= slv_array_deser(data_demux(i), RX_CHANNELS);

        block_vld_demux_i: entity work.GEN_DEMUX
            generic map(
                DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE,
                DEMUX_WIDTH => RX_CHANNELS,
                DEF_VALUE   => '0'
            )
            port map(
                DATA_IN     => RX_BLOCK_VLD(i),
                SEL         => RX_CHANNEL_BS(i),
                DATA_OUT    =>block_vld_demux(i)
        );
        block_vld_demux_arr(i)  <= slv_array_deser(block_vld_demux(i), RX_CHANNELS);

        soh_demux_i: entity work.GEN_DEMUX
            generic map(
                DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE,
                DEMUX_WIDTH => RX_CHANNELS,
                DEF_VALUE   => '0'
            )
            port map(
                DATA_IN     => RX_SOF_ONE_HOT(i),
                SEL         => RX_CHANNEL_BS(i),
                DATA_OUT    => sof_one_hot_demux(i)
        );
        sof_one_hot_demux_arr(i)    <= slv_array_deser(sof_one_hot_demux(i), RX_CHANNELS);

        eoh_demux_i: entity work.GEN_DEMUX
            generic map(
                DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE,
                DEMUX_WIDTH => RX_CHANNELS,
                DEF_VALUE   => '0'
            )
            port map(
                DATA_IN     => RX_EOF_ONE_HOT(i),
                SEL         => RX_CHANNEL_BS(i),
                DATA_OUT    => eof_one_hot_demux(i)
        );
        eof_one_hot_demux_arr(i)    <= slv_array_deser(eof_one_hot_demux(i), RX_CHANNELS);

        pkt_lng_demux_i: entity work.GEN_DEMUX
        generic map(
            DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)),
            DEMUX_WIDTH => RX_CHANNELS,
            DEF_VALUE   => '0'
        )
        port map(
            DATA_IN     => RX_PKT_LNG(i),
            SEL         => RX_CHANNEL_BS(i),
            DATA_OUT    => pkt_lng_demux(i)
        );
        pkt_lng_demux_arr(i)    <= slv_array_deser(pkt_lng_demux(i), RX_CHANNELS);
    end generate;

    -- Select correct data
    out_conversion_per_bs_g: for i in 0 to MFB_REGIONS generate
        out_conversion_per_ch_g: for ch in 0 to RX_CHANNELS - 1 generate
            TX_DATA(ch)(i)           <= data_demux_arr(i)(ch);
            TX_BLOCK_VLD(ch)(i)      <= block_vld_demux_arr(i)(ch);
            TX_SOF_ONE_HOT(ch)(i)    <= sof_one_hot_demux_arr(i)(ch);
            TX_EOF_ONE_HOT(ch)(i)    <= eof_one_hot_demux_arr(i)(ch);
            TX_PKT_LNG(ch)(i)        <= pkt_lng_demux_arr(i)(ch);
        end generate;
    end generate;
end architecture;
