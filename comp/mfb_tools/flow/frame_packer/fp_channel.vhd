-- fp_channel.vhd: Packaging for components belonging to the given FP_Channel
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FP_CHANNEL is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        MUX_WIDTH           : natural := 2;
        FIFO_DEPTH          : natural := 32;
        TIMEOUT_CLK_NO      : natural := 32;
        RX_PKT_SIZE_MIN     : natural := 2**13;
        RX_PKT_SIZE_MAX     : natural := 2**10;

        DEVICE              : string  := "AGILEX"
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        -- Verification probe
        DEBUG_PKT_NUM           : out std_logic_vector(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
        DEBUG_PKT_NUM_SRC_RDY   : out std_logic;
        DEBUG_EOF               : out std_logic_vector(MFB_REGIONS - 1 downto 0);
        DEBUG_EOF_SRC_RDY       : out std_logic;
        DEBUG_SP_EOF            : out std_logic;
        DEBUG_SP_EOF_SRC_RDY    : out std_logic;

        -- Overflow signal - Indicates when to read from TMP_REG
        RX_TMP_OVERFLOW : in  std_logic;
        -- Pointer - TMP_REG status (points to the free block)
        RX_TMP_PTR_UNS  : in  unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))-1 downto 0);

        -- RX interface
        RX_DATA         : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Length per packet
        RX_PKT_LNG      : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX+1))-1 downto 0);
        -- Valid per packet
        RX_BLOCK_VLD    : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- SOF_POS in ONE HOT format
        RX_SOF_ONE_HOT  : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- EOF_POS in ONE HOT format
        RX_EOF_ONE_HOT  : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

        -- TX interface
        TX_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_PKT_LNG      : out std_logic_vector(log2(RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
        TX_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY      : out std_logic;
        TX_DST_RDY      : in  std_logic;

        -- Indication that the FIFO is almost full
        TX_STOP         : out std_logic
    );
end entity;

architecture FULL of FP_CHANNEL is
    ------------------------------------------------------------
    --                 CONSTANT DECLARATION                   --
    ------------------------------------------------------------
    constant BLOCK_WIDTH            : natural := MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant BLOCK_WIDTH_EOF_ITEM   : natural := max(1, log2(MFB_ITEM_WIDTH));
    constant BUFFER_DEPTH           : natural := 8;
    constant EOF_NUM_LEN            : natural := max(1, log2(MFB_REGIONS*FIFO_DEPTH));
    constant LNG_WIDTH              : natural := max(1, log2(RX_PKT_SIZE_MAX+1));

    ------------------------------------------------------------
    --                 SUBTYPE DECLARATION                    --
    ------------------------------------------------------------
    subtype MFB_BLOCK_RANGE         is natural range MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1  downto 0;

    ------------------------------------------------------------
    --                  SIGNAL DECLARATION                    --
    ------------------------------------------------------------
    -- Input MUXes (selects data from correct BS)
    signal mux_arr_data_in      : slv_array_2d_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_REGIONS downto 0)(BLOCK_WIDTH - 1 downto 0);

    signal mux_select           : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1,log2(MUX_WIDTH))-1 downto 0);
    signal mux_block_out        : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_RANGE);
    signal tmp_reg              : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_RANGE);
    signal tmp_pkt_lng          : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

    signal mux_in_pkt_lng_arr   : slv_array_2d_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_REGIONS downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    signal mux_out_pkt_lng_arr  : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

    -- External timeout
    signal ext_timeout_event    : std_logic;
    signal ext_timeout_pkt_len  : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    signal ext_timeout_sof      : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal ext_timeout_eof      : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal ext_timeout_sof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal ext_timeout_eof_pos  : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);

    -- Out Control - Connection to Buffer
    signal out_ctrl_src_rdy     : std_logic;
    signal out_ctrl_timeout     : std_logic;
    signal out_ctrl_sof         : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal out_ctrl_eof         : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal out_ctrl_sof_pos     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal out_ctrl_eof_pos     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    --
    signal out_ctrl_eof_pos_arr : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal fixed_eof_pos_arr    : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    --
    signal out_ctrl_data        : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal out_ctrl_pkt_lng     : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1))- 1 downto 0);

    -- SPKT_LENGTH
    signal spkt_tx_eof_num      : std_logic_vector(EOF_NUM_LEN - 1 downto 0);
    signal spkt_tx_length       : std_logic_vector(log2(RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal spkt_tx_src_rdy      : std_logic;
    signal spkt_tx_dst_rdy      : std_logic;

    -- FIFO
    signal fifo_tx_sof          : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal fifo_tx_eof          : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal fifo_tx_src_rdy      : std_logic;
    signal fifo_tx_dst_rdy      : std_logic;

    -- DEBUG
    signal fifo_status          : std_logic_vector(max(1, log2(FIFO_DEPTH)) downto 0);
    signal fifo_aempty          : std_logic;

    -- Temporary register
    signal sof_or_std           : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal eof_or_std           : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tmp_sof_one_hot      : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tmp_eof_one_hot      : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

begin
    ------------------------------------------------------------
    --                        VER_MOD                         --
    ------------------------------------------------------------
    DEBUG_PKT_NUM           <= spkt_tx_eof_num;
    DEBUG_PKT_NUM_SRC_RDY   <= spkt_tx_src_rdy and spkt_tx_dst_rdy;

    -- Signals that helps to verification outline the SuperPacket
    -- Necessary due to timeout
    DEBUG_EOF               <= ext_timeout_sof;
    DEBUG_EOF_SRC_RDY       <= RX_TMP_OVERFLOW or ext_timeout_event;
    DEBUG_SP_EOF            <= or (out_ctrl_sof);
    DEBUG_SP_EOF_SRC_RDY    <= out_ctrl_src_rdy;

    ------------------------------------------------------------
    --                        MUX select                      --
    ------------------------------------------------------------
    -- Generates signal for each input MUX
    mux_sel_i: entity work.FP_MUX_CTRL
        generic map(
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

            MUX_WIDTH       => MUX_WIDTH
        )
        port map(
            RX_VLD_ARR  => RX_BLOCK_VLD,
            TX_SEL_ARR  => mux_select
    );

    ------------------------------------------------------------
    --                        MUX array                       --
    ------------------------------------------------------------
    -- Convert data to 2d array
    data_merge_blk_g: for i in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
        data_merge_bs_g: for j in 0 to MFB_REGIONS generate
            mux_arr_data_in(i)(j)  <= RX_DATA(j)((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH);
        end generate;
    end generate;

    -- Input MUX Array
    mux_data_arr_g: for i in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
        mux_i: entity work.GEN_MUX
            generic map(
                DATA_WIDTH  => MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,   -- block width
                MUX_WIDTH   => MUX_WIDTH
            )
            port map(
                DATA_IN     => slv_array_ser(mux_arr_data_in(i)),
                SEL         => mux_select(i),
                DATA_OUT    => mux_block_out(i)
        );
    end generate;


    pkt_lng_merge_blk_g: for blk in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
        pkt_lng_merge_bs_g: for bs in 0 to MFB_REGIONS generate
            mux_in_pkt_lng_arr(blk)(bs)    <= RX_PKT_LNG(bs)((blk+1)*LNG_WIDTH-1 downto blk*LNG_WIDTH);
        end generate;
    end generate;

    -- Packet Length
    mux_pkt_lng_arr_g: for blk in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
        mux_pkt_lng_i: entity work.GEN_MUX
            generic map(
                DATA_WIDTH  => max(1, log2(RX_PKT_SIZE_MAX+1)), -- Packet length
                MUX_WIDTH   => MUX_WIDTH
            )
            port map(
                DATA_IN     => slv_array_ser(mux_in_pkt_lng_arr(blk)),
                SEL         => mux_select(blk),
                DATA_OUT    => mux_out_pkt_lng_arr(blk)
        );
    end generate;

    ------------------------------------------------------------
    --                    Temporary register                  --
    ------------------------------------------------------------
    -- Temporary register holds overflow data
    eof_or_std_p: process(all)
        variable sof_or_std_v : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        variable sof_or_arr_v : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_REGIONS downto 0);
        variable eof_or_std_v : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        variable eof_or_arr_v : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_REGIONS downto 0);
    begin
        sof_or_std_v    := (others => '0');
        eof_or_std_v    := (others => '0');

        for blk in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 loop
            for bs in 0 to MFB_REGIONS loop
                sof_or_arr_v(blk)(bs)   := RX_SOF_ONE_HOT(bs)(blk);
                eof_or_arr_v(blk)(bs)   := RX_EOF_ONE_HOT(bs)(blk);
            end loop;
        end loop;

        for blk in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 loop
            sof_or_std_v(blk)   := or (sof_or_arr_v(blk));
            eof_or_std_v(blk)   := or (eof_or_arr_v(blk));
        end loop;

        sof_or_std  <= sof_or_std_v;
        eof_or_std  <= eof_or_std_v;
    end process;

    tmp_reg_i: entity work.FP_TMP_REG
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            RX_PKT_SIZE_MAX     => RX_PKT_SIZE_MAX
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_TMP_OVERFLOW         => RX_TMP_OVERFLOW,
            RX_TMP_PTR_UNS          => RX_TMP_PTR_UNS,
            RX_TMP_DATA_ARR         => mux_block_out,
            RX_TMP_SOF_ONE_HOT      => sof_or_std,
            RX_TMP_EOF_ONE_HOT      => eof_or_std,
            RX_PKT_LNG              => mux_out_pkt_lng_arr,

            TX_TMP_DATA             => tmp_reg,
            TX_TMP_SOF_ONE_HOT      => tmp_sof_one_hot,
            TX_TMP_EOF_ONE_HOT      => tmp_eof_one_hot,
            TX_PKT_LNG              => tmp_pkt_lng
    );

    ------------------------------------------------------------
    --                     External Timeout                   --
    ------------------------------------------------------------
    -- External timeout controls whether there is data in TMP_REG
    -- The second task is to correctly represent SOF and EOF
    ext_timeout_i: entity work.FP_TIMEOUT_EXT
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            RX_PKT_SIZE_MAX     => RX_PKT_SIZE_MAX,

            TIMEOUT_CLK_NO      => TIMEOUT_CLK_NO
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_SOF_ONE_HOT_CURR  => sof_or_std,
            RX_EOF_ONE_HOT_CURR  => eof_or_std,
            RX_PKT_LNG_CURR      => mux_out_pkt_lng_arr,

            RX_SOF_ONE_HOT_REG   => tmp_sof_one_hot,
            RX_EOF_ONE_HOT_REG   => tmp_eof_one_hot,
            RX_PKT_LNG_REG       => tmp_pkt_lng,

            RX_OVERFLOW          => RX_TMP_OVERFLOW,
            RX_TMP_PTR           => RX_TMP_PTR_UNS,

            TX_PKT_LNG           => ext_timeout_pkt_len,
            TX_SOF               => ext_timeout_sof,
            TX_EOF               => ext_timeout_eof,
            TX_EOF_POS           => ext_timeout_eof_pos,
            TX_SOF_POS           => ext_timeout_sof_pos,
            TX_TIMEOUT_EXT       => ext_timeout_event
    );

    ------------------------------------------------------------
    --                         OUT CTRL                       --
    ------------------------------------------------------------
    -- Selects correct data (Current or Register)
    out_ctrl_i: entity work.FP_DATA_SEL
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,

            RX_PKT_SIZE_MAX     => RX_PKT_SIZE_MAX
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_TMP_REG_DATA => slv_array_ser(tmp_reg),
            RX_CURRENT_DATA => slv_array_ser(mux_block_out),
            RX_TMP_PTR      => RX_TMP_PTR_UNS,
            RX_SRC_RDY      => RX_TMP_OVERFLOW or ext_timeout_event,

            RX_TIMEOUT_EXT  => ext_timeout_event,
            RX_PKT_LNG      => ext_timeout_pkt_len,
            RX_SOF          => ext_timeout_sof,
            RX_EOF          => ext_timeout_eof,
            RX_SOF_POS      => ext_timeout_sof_pos,
            RX_EOF_POS      => ext_timeout_eof_pos,

            TX_DATA         => out_ctrl_data,
            TX_PKT_LNG      => out_ctrl_pkt_lng,
            TX_META         => open,
            TX_TIMEOUT_EXT  => out_ctrl_timeout,
            TX_SOF          => out_ctrl_sof,
            TX_EOF          => out_ctrl_eof,
            TX_SOF_POS      => out_ctrl_sof_pos,
            TX_EOF_POS      => out_ctrl_eof_pos,
            TX_SRC_RDY      => out_ctrl_src_rdy
    );
    ------------------------------------------------------------
    --                       SPKT_LENGTH                      --
    ------------------------------------------------------------
    -- Keeps track of the size of the SuperPacket and passes the
    -- number of packets that make up the SuperPacket.
    spkt_len_i: entity work.FP_SPKT_LNG
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            FIFO_DEPTH          => FIFO_DEPTH,
            TIMEOUT_CLK_NO      => 2*TIMEOUT_CLK_NO,
            SPKT_SIZE_MIN       => RX_PKT_SIZE_MIN,
            SPKT_SIZE_MAX       => RX_PKT_SIZE_MAX,
            DEVICE              => DEVICE
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_EXT_TIMEOUT     => out_ctrl_timeout,
            RX_PKT_SOF         => out_ctrl_sof,
            RX_PKT_EOF         => out_ctrl_eof,
            RX_PKT_SRC_RDY     => out_ctrl_src_rdy,
            RX_PKT_LENGTH      => out_ctrl_pkt_lng,

            TX_SPKT_EOF_NUM    => spkt_tx_eof_num,
            TX_SPKT_LENGTH     => spkt_tx_length,
            TX_SPKT_SRC_RDY    => spkt_tx_src_rdy,
            TX_SPKT_DST_RDY    => spkt_tx_dst_rdy
    );

    out_ctrl_eof_pos_arr    <= slv_array_deser(out_ctrl_eof_pos, MFB_REGIONS);
    fill_up_g: for r in 0 to MFB_REGIONS - 1 generate
        fixed_eof_pos_arr(r) <= out_ctrl_eof_pos_arr(r) & "111";
    end generate;

    ------------------------------------------------------------
    --                           FIFO                         --
    ------------------------------------------------------------
    -- Holds SuperPacket
    mfb_out_fifo_i: entity work.MFB_FIFOX
        generic map(
            REGIONS             => MFB_REGIONS,
            REGION_SIZE         => MFB_REGION_SIZE,
            BLOCK_SIZE          => MFB_BLOCK_SIZE,
            ITEM_WIDTH          => MFB_ITEM_WIDTH,
            META_WIDTH          => 0,
            FIFO_DEPTH          => FIFO_DEPTH,
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 8,
            ALMOST_EMPTY_OFFSET => 0
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_DATA     => out_ctrl_data,
            RX_SOF      => out_ctrl_sof,
            RX_EOF      => out_ctrl_eof,
            RX_SOF_POS  => out_ctrl_sof_pos,
            RX_EOF_POS  => slv_array_ser(fixed_eof_pos_arr),
            RX_SRC_RDY  => out_ctrl_src_rdy,
            RX_DST_RDY  => open,

            TX_DATA     => TX_DATA,
            TX_SOF      => fifo_tx_sof,
            TX_EOF      => fifo_tx_eof,
            TX_SOF_POS  => TX_SOF_POS,
            TX_EOF_POS  => TX_EOF_POS,
            TX_SRC_RDY  => fifo_tx_src_rdy,
            TX_DST_RDY  => fifo_tx_dst_rdy,

            FIFO_STATUS => fifo_status,
            FIFO_AFULL  => TX_STOP,
            FIFO_AEMPTY => fifo_aempty
    );

    ------------------------------------------------------------
    --                        FIFO CTRL                       --
    ------------------------------------------------------------
    -- Keeps track of SuperPacket boundaries
    fifo_ctrl_i: entity work.FP_FIFO_CTRL
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            FIFO_DEPTH          => FIFO_DEPTH,
            RX_PKT_SIZE_MAX     => RX_PKT_SIZE_MAX
        )
        port map(
            CLK => CLK,
            RST => RST,

            FIFO_TX_SRC_RDY     => fifo_tx_src_rdy,
            FIFO_TX_DST_RDY     => fifo_tx_dst_rdy,
            FIFO_TX_SOF         => fifo_tx_sof,
            FIFO_TX_EOF         => fifo_tx_eof,
            FIFO_TX_SOF_POS     => TX_SOF_POS,
            FIFO_TX_EOF_POS     => TX_EOF_POS,

            SPKT_RX_EOF_NUM     => spkt_tx_eof_num,
            SPKT_RX_LENGTH      => spkt_tx_length,
            SPKT_RX_SRC_RDY     => spkt_tx_src_rdy,
            SPKT_RX_DST_RDY     => spkt_tx_dst_rdy,

            -- Valid with SOF
            TX_PKT_LEN_DST_RDY  => TX_DST_RDY,
            TX_PKT_LEN_DATA     => TX_PKT_LNG,

            CH_TX_SRC_RDY       => TX_SRC_RDY,
            CH_TX_DST_RDY       => TX_DST_RDY,
            CH_TX_SOF           => TX_SOF,
            CH_TX_EOF           => TX_EOF
    );

end architecture;

