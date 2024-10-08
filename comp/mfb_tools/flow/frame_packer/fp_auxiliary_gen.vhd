-- fp_auxiliary_gen.vhd: FramePacker specific auxiliary signal generator
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The purpose of this component is to generate auxiliary signals for each packet in the MFB word
entity FP_AUX_GEN is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;
        META_WIDTH          : natural := 0;

        RX_CHANNELS         : natural := 16;
        RX_PKT_SIZE_MAX     : natural := 2**10

    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        -- RX MFB interface
        RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- [Length][Channel]
        RX_MFB_META     : in  std_logic_vector(MFB_REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY  : in  std_logic;
        RX_MFB_DST_RDY  : out std_logic;

        -- TX MFB interface
        TX_MFB_DATA     : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic_vector(MFB_REGIONS downto 0);
        -- Not used
        TX_MFB_DST_RDY  : in  std_logic;

        -- Auxiliary data for each packet:
        -- Channel per Packet
        TX_CHANNEL_BS   : out slv_array_t(MFB_REGIONS downto 0)(max(1, log2(RX_CHANNELS))-1 downto 0);
        -- Packet length per Packet
        TX_PKT_LNG      : out slv_array_t(MFB_REGIONS downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1))-1 downto 0);
        -- Valid per Packet
        TX_BLOCK_VLD    : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
        -- SOF_POS in ONE HOT format for each Packet
        TX_SOF_ONE_HOT  : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
        -- EOF_POS in ONE HOT format for each Packet
        TX_EOF_ONE_HOT  : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
        -- SOF_POS per Packet
        TX_SOF_POS_BS   : out slv_array_t(MFB_REGIONS downto 0)(max(1, log2(MFB_REGION_SIZE))-1 downto 0)
    );
end entity;

architecture FULL of FP_AUX_GEN is
    ------------------------------------------------------------
    --                   SIGNAL DECLARATION                   --
    ------------------------------------------------------------
    -- Extract MVB data
    signal rx_mfb_meta_arr          : slv_array_t(MFB_REGIONS - 1 downto 0)(META_WIDTH - 1 downto 0);
    signal rx_channel_s             : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_CHANNELS)) - 1 downto 0);
    signal rx_pkt_lng_s             : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1))-1 downto 0);

    -- Destination ready per Dropper
    signal rx_dropper_dst_rdy       : std_logic_vector(MFB_REGIONS downto 0);

    -- Decide whether packet continous in the following MFB word
    signal tx_dropper_pkt_cont      : std_logic_vector(MFB_REGIONS downto 0);
    signal rx_pkt_cont_reg_msk      : std_logic;

    -- Masker
    signal rx_drop                  : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS - 1 downto 0);
    signal rx_pkt_cont              : std_logic_vector(MFB_REGIONS downto 0);
    signal rx_drop_lv               : std_logic_vector(MFB_REGIONS downto 0);

    signal tx_dropper_sof           : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS - 1 downto 0);
    signal tx_dropper_eof           : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS - 1 downto 0);
    signal tx_dropper_sof_pos       : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_dropper_eof_pos       : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal tx_dropper_src_rdy       : std_logic_vector(MFB_REGIONS downto 0);

    -- Validator
    signal vld_pkt_cont             : std_logic_vector(MFB_REGIONS downto 0);
    signal rx_pkt_cont_reg_vld      : std_logic;
    signal tx_src_rdy_vld           : std_logic_vector(MFB_REGIONS downto 0);
    signal tx_block_vld_s           : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tx_sof_one_hot_vld       : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tx_eof_one_hot_vld       : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    -- Channel per BS
    signal lv_channel_per_bs        : slv_array_t(MFB_REGIONS downto 0)(max(1, log2(RX_CHANNELS)) - 1 downto 0);
    signal lv_vld_reg_in            : std_logic;
    signal lv_data_reg_out          : std_logic_vector(max(1, log2(RX_CHANNELS)) - 1 downto 0);
    signal lv_vld_reg_out           : std_logic;
    signal lv_wr_reg_out            : std_logic;
    signal lv_tx_data               : std_logic_vector(MFB_REGIONS*max(1, log2(RX_CHANNELS)) - 1 downto 0);

    -- Packet round-up
    signal pkt_len_rounded          : u_array_t(MFB_REGIONS - 1 downto 0)(log2(RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal pkt_len_rounded_std_arr  : slv_array_t(MFB_REGIONS downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

    signal tx_sof_pos_arr           : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    signal mfb_sof_pos_reg          : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);

begin
    ------------------------------------------------------------
    --                   METADATA EXTRACTION                  --
    ------------------------------------------------------------
    rx_mfb_meta_arr <= slv_array_deser(RX_MFB_META, MFB_REGIONS);

    extract_meta_g: for r in 0 to MFB_REGIONS - 1 generate
        rx_channel_s(r) <= rx_mfb_meta_arr(r)(max(1, log2(RX_CHANNELS)) - 1 downto 0);
        rx_pkt_lng_s(r) <= rx_mfb_meta_arr(r)(max(1, log2(RX_PKT_SIZE_MAX+1)) + log2(RX_CHANNELS) - 1 downto log2(RX_CHANNELS));
    end generate;

    ------------------------------------------------------------
    --                      Masker [msk]                      --
    ------------------------------------------------------------
    RX_MFB_DST_RDY  <= and (rx_dropper_dst_rdy);

    pkt_cont_reg_msk_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                rx_pkt_cont_reg_msk  <= '0';
            elsif (RX_MFB_SRC_RDY = '1') then
                rx_pkt_cont_reg_msk  <= or (tx_dropper_pkt_cont);
            end if;
        end if;
    end process;

    dropper_select_p: process(all)
        -- [Packets][Regions]
        variable rx_drop_v      : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS - 1 downto 0);
        -- [Packets]
        variable rx_pkt_cont_v  : std_logic_vector(MFB_REGIONS downto 0);
        -- [Packets]
        variable rx_drop_lv_v   : std_logic_vector(MFB_REGIONS downto 0);
    begin
        -- Default state
        rx_drop_v       := (others => (others => '1'));
        rx_pkt_cont_v   := (others => '0');
        rx_drop_lv_v    := (others => '1');

        -- Individual operations
        drop_select_l: for i in 0 to MFB_REGIONS - 1 loop
            rx_drop_v(i+1)(i)    := '0';
        end loop;

        rx_pkt_cont_v(0)    := rx_pkt_cont_reg_msk;

        rx_drop_lv_v(0)     := '0';

        -- Assign variables
        rx_drop     <= rx_drop_v;
        rx_pkt_cont <= rx_pkt_cont_v;
        rx_drop_lv  <= rx_drop_lv_v;
    end process;

    mfb_dropper_g: for i in 0 to MFB_REGIONS generate
        mfb_dropper_i: entity work.FP_MFB_DROPPER
            generic map(
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REGION_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH
            )
            port map(
                CLK     => CLK,
                RESET   => RST,

                RX_SOF_POS  => RX_MFB_SOF_POS,
                RX_EOF_POS  => RX_MFB_EOF_POS,
                RX_SOF      => RX_MFB_SOF,
                RX_EOF      => RX_MFB_EOF,
                RX_SRC_RDY  => RX_MFB_SRC_RDY,
                RX_DST_RDY  => rx_dropper_dst_rdy(i),
                RX_DROP     => rx_drop(i),
                RX_PKT_CONT => rx_pkt_cont(i),
                TX_PKT_CONT => tx_dropper_pkt_cont(i),
                RX_DROP_LV  => rx_drop_lv(i),
                TX_SOF_POS  => tx_dropper_sof_pos(i),
                TX_EOF_POS  => tx_dropper_eof_pos(i),
                TX_SOF      => tx_dropper_sof(i),
                TX_EOF      => tx_dropper_eof(i),
                TX_SRC_RDY  => tx_dropper_src_rdy(i),
                TX_DST_RDY  => '1'
        );
    end generate;

    ------------------------------------------------------------
    --                      Channel per BS                    --
    ------------------------------------------------------------
    -- External register for last_vld
    channel_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                lv_channel_per_bs(0)  <= (others => '0');
                lv_vld_reg_in         <= '0';
            elsif lv_wr_reg_out = '1' then
                lv_channel_per_bs(0)  <= lv_data_reg_out;
                lv_vld_reg_in         <= lv_vld_reg_out;
            end if;
        end if;
    end process;

    -- The first BS handles EOF - Channel from the register
    channel_per_bs_i : entity work.MVB_AGGREGATE_LAST_VLD
        generic map(
            ITEMS           => MFB_REGIONS,
            ITEM_WIDTH      => max(1, log2(RX_CHANNELS)),
            IMPLEMENTATION  => "serial",
            INTERNAL_REG    => false
        )
        port map(
            CLK             => CLK,
            RESET           => RST,

            RX_DATA         => slv_array_ser(rx_channel_s),
            RX_VLD          => RX_MFB_SOF,
            RX_SRC_RDY      => RX_MFB_SRC_RDY,
            RX_DST_RDY      => open,

            REG_IN_DATA     => lv_channel_per_bs(0),
            REG_IN_VLD      => lv_vld_reg_in,
            REG_OUT_DATA    => lv_data_reg_out,
            REG_OUT_VLD     => lv_vld_reg_out,
            REG_OUT_WR      => lv_wr_reg_out,

            TX_DATA         => lv_tx_data,
            TX_VLD          => open,
            TX_PRESCAN_DATA => open,
            TX_PRESCAN_VLD  => open,
            TX_SRC_RDY      => open,
            TX_DST_RDY      => '1'
    );

    lv_channel_per_bs(lv_channel_per_bs'high downto 1) <= slv_array_deser(lv_tx_data, MFB_REGIONS);

    -- Synchronization with the rest of the auxiliary signals
    channel_sync_p: process(all)
    begin
        if rising_edge(CLK) then
            TX_CHANNEL_BS   <= lv_channel_per_bs;
        end if;
    end process;

    ------------------------------------------------------------
    --                    Validator [vld]                     --
    ------------------------------------------------------------
    -- Synchronization
    pkt_cont_reg_vld_p: process(all)
    begin
        if rising_edge(CLK) then
            rx_pkt_cont_reg_vld <=  rx_pkt_cont_reg_msk;
        end if;
    end process;

    vld_pkt_select_p: process(all)
        variable vld_pkt_cont_v : std_logic_vector(MFB_REGIONS downto 0);
    begin
        -- Default state
        vld_pkt_cont_v      := (others => '0');
        vld_pkt_cont_v(0)   := rx_pkt_cont_reg_vld;

        vld_pkt_cont    <= vld_pkt_cont_v;
    end process;

    block_valid_g: for i in 0 to MFB_REGIONS generate
        block_valid_0_i: entity work.FP_BLOCK_VLD
            generic map(
                MFB_REGIONS       => MFB_REGIONS,
                MFB_REGION_SIZE   => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE    => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH    => MFB_ITEM_WIDTH
            )
            port map(
                RX_PKT_CONT     => vld_pkt_cont(i),

                RX_SOF          => tx_dropper_sof(i),
                RX_EOF          => tx_dropper_eof(i),
                RX_SOF_POS      => tx_dropper_sof_pos(i),
                RX_EOF_POS      => tx_dropper_eof_pos(i),
                RX_SRC_RDY      => tx_dropper_src_rdy(i),
                RX_DST_RDY      => open,

                TX_SRC_RDY      => tx_src_rdy_vld(i),
                TX_DST_RDY      => '1',

                TX_BLOCK_VLD    => tx_block_vld_s(i),
                TX_SOF_OH       => tx_sof_one_hot_vld(i),
                TX_EOF_OH       => tx_eof_one_hot_vld(i)
        );
    end generate;

    -- Round up current packet length
    process(all)
        variable pkt_len_rounded_v  : u_array_t(MFB_REGIONS - 1 downto 0)(log2(RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
    begin
        for r in 0 to MFB_REGIONS - 1 loop
            if (or(rx_pkt_lng_s(r)(log2(MFB_BLOCK_SIZE) - 1 downto 0))) = '1' then
                pkt_len_rounded_v(r)   := unsigned(rx_pkt_lng_s(r)) + to_unsigned(MFB_BLOCK_SIZE, pkt_len_rounded_v(r)'length);
            else
                pkt_len_rounded_v(r)   := unsigned(rx_pkt_lng_s(r));
            end if;
            pkt_len_rounded_v(r)(log2(MFB_BLOCK_SIZE) - 1 downto 0) := (others => '0');

            pkt_len_rounded(r)  <= pkt_len_rounded_v(r);
        end loop;

    end process;

    -- Create Packet Length field
    pkt_len_rounded_std_arr(0)     <= (others => '0');
    uns_to_slv_g: for r in 1 to MFB_REGIONS generate
        pkt_len_rounded_std_arr(r)     <= std_logic_vector(pkt_len_rounded(r-1));
    end generate;

    -- Synchronization of AUX signals with DATA
    data_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            TX_MFB_DATA         <= RX_MFB_DATA;
            TX_PKT_LNG          <= pkt_len_rounded_std_arr;
            mfb_sof_pos_reg     <= RX_MFB_SOF_POS;
        end if;
    end process;

    TX_BLOCK_VLD    <= tx_block_vld_s;
    TX_SOF_ONE_HOT  <= tx_sof_one_hot_vld;
    TX_EOF_ONE_HOT  <= tx_eof_one_hot_vld;
    TX_MFB_SRC_RDY  <= tx_src_rdy_vld;

    -- SOF_POS per Packet
    tx_sof_pos_arr      <= slv_array_deser(mfb_sof_pos_reg, MFB_REGIONS);
    TX_SOF_POS_BS(0)    <= (others => '0');
    sof_pos_per_bs_g: for i in 1 to MFB_REGIONS generate
        TX_SOF_POS_BS(i)    <= tx_sof_pos_arr(i - 1);
    end generate;

end architecture;
