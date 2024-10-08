-- mfb_frame_extender.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The MFB_FRAME_EXTENDER component allows an MFB frame to be extended by adding
-- empty MFB blocks to its beginning. This component can be used, for example,
-- to efficiently insert metadata into the framework.
entity MFB_FRAME_EXTENDER is
generic (
    -- The number of MFB regions
    MFB_REGIONS     : natural := 4;
    -- MFB region size in blocks, must be power of two
    MFB_REGION_SIZE : natural := 8;
    -- MFB block size in items, must be 8
    MFB_BLOCK_SIZE  : natural := 8;
    -- MFB item size in bits, must be 8
    MFB_ITEM_WIDTH  : natural := 8;
    -- Maximum size of a MFB frame (in bytes)
    PKT_MTU         : natural := 2**14;
    -- Set the depth of RX MVB FIFOX Multi
    MVB_FIFO_DEPTH  : natural := 32;
    -- Set the depth of RX MFB FIFOX Multi
    MFB_FIFO_DEPTH  : natural := 32;
    -- Width of User Metadata information
    USERMETA_WIDTH  : natural := 32;
    -- Target device: AGILEX, STRATIX10, ULTRASCALE,...
    DEVICE          : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK                    : in  std_logic;
    RESET                  : in  std_logic;

    -- =========================================================================
    -- RX MFB+MVB interface
    -- =========================================================================
    RX_MVB_USERMETA        : in  std_logic_vector(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    -- RX MFB frame size in MFB items
    RX_MVB_FRAME_LENGTH    : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU)-1 downto 0);
    -- Frame extension size in MFB items, but must be divisible by MFB_BLOCK_SIZE
    RX_MVB_EXT_SIZE        : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU)-1 downto 0);
    -- It only uses the new part (EXT_SIZE) of the frame, the rest is discarded.
    -- This can be useful, for example, when we need to send only metadata instead of the frame.
    RX_MVB_EXT_ONLY        : in  std_logic_vector(MFB_REGIONS-1 downto 0) := (others => '0');
    -- Enables the extension of the MFB frame
    RX_MVB_EXT_EN          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_VLD             : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MVB_SRC_RDY         : in  std_logic;
    RX_MVB_DST_RDY         : out std_logic;

    RX_MFB_DATA            : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_SOF             : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF             : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SOF_POS         : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS         : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SRC_RDY         : in  std_logic;
    RX_MFB_DST_RDY         : out std_logic;

    -- =========================================================================
    --  TX MFB interface
    -- =========================================================================
    TX_MVB_USERMETA        : out std_logic_vector(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    TX_MVB_VLD             : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MVB_SRC_RDY         : out std_logic;
    TX_MVB_DST_RDY         : in  std_logic;

    TX_MFB_DATA            : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_MFB_USERMETA        : out std_logic_vector(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    TX_MFB_SOF             : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF             : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SOF_POS         : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS         : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SRC_RDY         : out std_logic;
    TX_MFB_DST_RDY         : in  std_logic
);
end entity;

architecture FULL of MFB_FRAME_EXTENDER is

    constant LEN_WIDTH      : natural := log2(PKT_MTU);
    constant GEN_META_WIDTH : natural := USERMETA_WIDTH+LEN_WIDTH+1;

    signal rx_mvb_usermeta_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_WIDTH-1 downto 0);
    signal rx_mvb_frame_length_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal rx_mvb_ext_size_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);

    signal gen_mode                 : slv_array_t(MFB_REGIONS-1 downto 0)(2-1 downto 0);
    signal gen_len_ext_on           : u_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal gen_len_ext_off          : u_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal gen_len_ext_only         : u_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal gen_len                  : slv_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal gen_insert               : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal gen_offset               : slv_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal gen_meta                 : slv_array_t(MFB_REGIONS-1 downto 0)(GEN_META_WIDTH-1 downto 0);
    signal gen_vld                  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal gen_src_rdy              : std_logic;
    signal gen_dst_rdy              : std_logic;

    signal fifo_mvb_meta            : std_logic_vector(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    signal fifo_mvb_vld             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifo_mvb_src_rdy         : std_logic;
    signal fifo_mvb_dst_rdy         : std_logic;

    signal pkt_meta_ser             : std_logic_vector(MFB_REGIONS*GEN_META_WIDTH-1 downto 0);
    signal pkt_meta                 : slv_array_t(MFB_REGIONS-1 downto 0)(GEN_META_WIDTH-1 downto 0);
    signal pkt_insert               : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pkt_offset               : slv_array_t(MFB_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal pkt_usermeta             : slv_array_t(MFB_REGIONS-1 downto 0)(USERMETA_WIDTH-1 downto 0);
    signal pkt_sof                  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pkt_eof                  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pkt_sof_pos              : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal pkt_eof_pos              : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal pkt_src_rdy              : std_logic;
    signal pkt_dst_rdy              : std_logic;

    signal ctrl_insert_move         : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0)(log2(MFB_REGIONS*MFB_REGION_SIZE)-1 downto 0);
    signal ctrl_insert_mask         : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
    signal ctrl_insert_vld          : std_logic;
    signal ctrl_usermeta            : std_logic_vector(MFB_REGIONS*USERMETA_WIDTH-1 downto 0);
    signal ctrl_sof                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ctrl_eof                 : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ctrl_sof_pos             : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal ctrl_eof_pos             : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal ctrl_src_rdy             : std_logic;
    signal ctrl_dst_rdy             : std_logic;

    signal dbg_rx_mvb_pkt_cnt       : unsigned(64-1 downto 0);
    signal dbg_rx_mfb_pkt_cnt       : unsigned(64-1 downto 0);
    signal dbg_tx_mfb_pkt_cnt       : unsigned(64-1 downto 0);

begin

    RX_MVB_DST_RDY <= fifo_mvb_dst_rdy and gen_dst_rdy;

    fifo_mvb_meta    <= RX_MVB_USERMETA;
    fifo_mvb_vld     <= RX_MVB_VLD;
    fifo_mvb_src_rdy <= RX_MVB_SRC_RDY and gen_dst_rdy;

    gen_vld     <= RX_MVB_VLD;
    gen_src_rdy <= RX_MVB_SRC_RDY and fifo_mvb_dst_rdy;

    rx_mvb_usermeta_arr     <= slv_array_deser(RX_MVB_USERMETA, MFB_REGIONS);
    rx_mvb_frame_length_arr <= slv_array_deser(RX_MVB_FRAME_LENGTH, MFB_REGIONS);
    rx_mvb_ext_size_arr     <= slv_array_deser(RX_MVB_EXT_SIZE, MFB_REGIONS);

    gen_meta_g : for rr in 0 to MFB_REGIONS-1 generate
        gen_mode(rr) <= RX_MVB_EXT_EN(rr) & RX_MVB_EXT_ONLY(rr);

        gen_len_ext_on(rr)   <= unsigned(rx_mvb_frame_length_arr(rr)) + unsigned(rx_mvb_ext_size_arr(rr));
        gen_len_ext_off(rr)  <= unsigned(rx_mvb_frame_length_arr(rr));
        gen_len_ext_only(rr) <= unsigned(rx_mvb_ext_size_arr(rr));

        with gen_mode(rr) select
            gen_len(rr) <= std_logic_vector(gen_len_ext_on(rr))   when "10",
                           std_logic_vector(gen_len_ext_only(rr)) when "11",
                           std_logic_vector(gen_len_ext_off(rr))  when "00",
                           std_logic_vector(gen_len_ext_off(rr))  when others;

        gen_offset(rr) <= rx_mvb_ext_size_arr(rr) when (gen_mode(rr) = "10") else (others => '0');
        gen_insert(rr) <= not (RX_MVB_EXT_EN(rr) and RX_MVB_EXT_ONLY(rr));

        gen_meta(rr)(0)                                               <= gen_insert(rr);
        gen_meta(rr)(LEN_WIDTH+1-1 downto 1)                          <= gen_offset(rr);
        gen_meta(rr)(USERMETA_WIDTH+LEN_WIDTH+1-1 downto LEN_WIDTH+1) <= rx_mvb_usermeta_arr(rr);
    end generate;

    tx_mvb_fifo_i : entity work.MVB_FIFOX
    generic map(
        ITEMS      => MFB_REGIONS,
        ITEM_WIDTH => USERMETA_WIDTH,
        FIFO_DEPTH => MVB_FIFO_DEPTH,
        RAM_TYPE   => "AUTO",
        DEVICE     => DEVICE
    ) port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => fifo_mvb_meta,
        RX_VLD     => fifo_mvb_vld,
        RX_SRC_RDY => fifo_mvb_src_rdy,
        RX_DST_RDY => fifo_mvb_dst_rdy,

        TX_DATA    => TX_MVB_USERMETA,
        TX_VLD     => TX_MVB_VLD,
        TX_SRC_RDY => TX_MVB_SRC_RDY,
        TX_DST_RDY => TX_MVB_DST_RDY
    );

    pkt_gen_i : entity work.MFB_USER_PACKET_GEN
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REGION_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => GEN_META_WIDTH,
        FIFO_DEPTH  => MVB_FIFO_DEPTH,
        LEN_WIDTH   => LEN_WIDTH,
        DEVICE      => DEVICE
    )
    port map(
        CLK         => CLK,
        RESET       => RESET,

        GEN_DATA    => slv_array_ser(gen_len),
        GEN_META    => slv_array_ser(gen_meta),
        GEN_VLD     => gen_vld,
        GEN_SRC_RDY => gen_src_rdy,
        GEN_DST_RDY => gen_dst_rdy,

        TX_DATA     => open,
        TX_META     => pkt_meta_ser,
        TX_SOF_POS  => pkt_sof_pos,
        TX_EOF_POS  => pkt_eof_pos,
        TX_SOF      => pkt_sof,
        TX_EOF      => pkt_eof,
        TX_SRC_RDY  => pkt_src_rdy,
        TX_DST_RDY  => pkt_dst_rdy
    );

    pkt_meta <= slv_array_deser(pkt_meta_ser, MFB_REGIONS);

    pkt_meta_g : for rr in 0 to MFB_REGIONS-1 generate
        pkt_insert(rr)   <= pkt_meta(rr)(0);
        pkt_offset(rr)   <= pkt_meta(rr)(LEN_WIDTH+1-1 downto 1);
        pkt_usermeta(rr) <= pkt_meta(rr)(USERMETA_WIDTH+LEN_WIDTH+1-1 downto LEN_WIDTH+1);
    end generate;

    dm_ctrl_i : entity work.MFB_FRAME_EXTENDER_DM_CTRL
    generic map(
        REGIONS        => MFB_REGIONS,
        REGION_SIZE    => MFB_REGION_SIZE,
        BLOCK_SIZE     => MFB_BLOCK_SIZE,
        ITEM_WIDTH     => MFB_ITEM_WIDTH,
        LEN_WIDTH      => LEN_WIDTH,
        USERMETA_WIDTH => USERMETA_WIDTH,
        DEVICE         => DEVICE
    )
    port map(
        CLK            => CLK,
        RESET          => RESET,

        RX_INSERT      => pkt_insert,
        RX_OFFSET      => slv_array_ser(pkt_offset),
        RX_USERMETA    => slv_array_ser(pkt_usermeta),
        RX_SOF_POS     => pkt_sof_pos,
        RX_EOF_POS     => pkt_eof_pos,
        RX_SOF         => pkt_sof,
        RX_EOF         => pkt_eof,
        RX_SRC_RDY     => pkt_src_rdy,
        RX_DST_RDY     => pkt_dst_rdy,

        TX_INSERT_MOVE => ctrl_insert_move,
        TX_INSERT_MASK => ctrl_insert_mask,
        TX_INSERT_VLD  => ctrl_insert_vld,
        TX_USERMETA    => ctrl_usermeta,
        TX_SOF_POS     => ctrl_sof_pos,
        TX_EOF_POS     => ctrl_eof_pos,
        TX_SOF         => ctrl_sof,
        TX_EOF         => ctrl_eof,
        TX_SRC_RDY     => ctrl_src_rdy,
        TX_DST_RDY     => ctrl_dst_rdy
    );

    data_mover_i : entity work.MFB_FRAME_EXTENDER_DATAMOVER
    generic map(
        REGIONS        => MFB_REGIONS,
        REGION_SIZE    => MFB_REGION_SIZE,
        BLOCK_SIZE     => MFB_BLOCK_SIZE,
        ITEM_WIDTH     => MFB_ITEM_WIDTH,
        LEN_WIDTH      => LEN_WIDTH,
        FIFO_DEPTH     => MFB_FIFO_DEPTH,
        USERMETA_WIDTH => USERMETA_WIDTH,
        DEVICE         => DEVICE
    )
    port map(
        CLK                 => CLK,
        RESET               => RESET,

        RX_CTRL_INSERT_MOVE => ctrl_insert_move,
        RX_CTRL_INSERT_MASK => ctrl_insert_mask,
        RX_CTRL_INSERT_VLD  => ctrl_insert_vld,
        RX_CTRL_USERMETA    => ctrl_usermeta,
        RX_CTRL_SOF_POS     => ctrl_sof_pos,
        RX_CTRL_EOF_POS     => ctrl_eof_pos,
        RX_CTRL_SOF         => ctrl_sof,
        RX_CTRL_EOF         => ctrl_eof,
        RX_CTRL_SRC_RDY     => ctrl_src_rdy,
        RX_CTRL_DST_RDY     => ctrl_dst_rdy,

        RX_MFB_DATA         => RX_MFB_DATA,
        RX_MFB_SOF          => RX_MFB_SOF,
        RX_MFB_EOF          => RX_MFB_EOF,
        RX_MFB_SOF_POS      => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS      => RX_MFB_EOF_POS,
        RX_MFB_SRC_RDY      => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY      => RX_MFB_DST_RDY,

        TX_MFB_DATA         => TX_MFB_DATA,
        TX_MFB_USERMETA     => TX_MFB_USERMETA,
        TX_MFB_SOF          => TX_MFB_SOF,
        TX_MFB_EOF          => TX_MFB_EOF,
        TX_MFB_SOF_POS      => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS      => TX_MFB_EOF_POS,
        TX_MFB_SRC_RDY      => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY      => TX_MFB_DST_RDY
    );

    -- =========================================================================
    -- DEBUG LOGIC
    -- =========================================================================

    --pragma synthesis_off
    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rx_mvb_pkt_cnt <= (others => '0');
            elsif (RX_MVB_SRC_RDY = '1' and RX_MVB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RX_MVB_VLD(i);
                end loop;
                dbg_rx_mvb_pkt_cnt <= dbg_rx_mvb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rx_mfb_pkt_cnt <= (others => '0');
            elsif (RX_MFB_SRC_RDY = '1' and RX_MFB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RX_MFB_EOF(i);
                end loop;
                dbg_rx_mfb_pkt_cnt <= dbg_rx_mfb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_tx_mfb_pkt_cnt <= (others => '0');
            elsif (TX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + TX_MFB_EOF(i);
                end loop;
                    dbg_tx_mfb_pkt_cnt <= dbg_tx_mfb_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;
    --pragma synthesis_on

end architecture;
