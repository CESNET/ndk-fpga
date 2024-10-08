-- mfb_merger_full.vhd: MFB+MVB bus merger (simpler architecture)
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------
-- Merges two input MVB+MFB interfaces in one output interface
-- Only contains 1 input register for each input interface and 1 output register.
-- Has lower throughput compared to the OLD MFB Merger architecture,
-- but much lesser resource consumption.

-- This is the preffered architecture for this unit!

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture FULL of MFB_MERGER is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    constant SOF_POS_WIDTH      : integer := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH      : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant CORR_SOF_POS_WIDTH : integer := log2(MFB_REG_SIZE);
    constant MFB_DATA_WIDTH     : integer := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    type boolean_array_t is array (natural range <>) of boolean;
    constant PAYLOAD_ENABLED : boolean_array_t(2-1 downto 0) := (RX1_PAYLOAD_ENABLED, RX0_PAYLOAD_ENABLED);
    constant MVB_DATA_W      : natural := HDR_WIDTH+2;

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    -- RX MVB converted to slv_array_t
    signal rx_mvb_hdr      : slv_array_t(2-1 downto 0)(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal rx_mvb_payload  : slv_array_t(2-1 downto 0)(MVB_ITEMS          -1 downto 0);
    signal rx_mvb_vld      : slv_array_t(2-1 downto 0)(MVB_ITEMS          -1 downto 0);
    signal rx_mvb_src_rdy  : std_logic_vector(2-1 downto 0);
    signal rx_mvb_dst_rdy  : std_logic_vector(2-1 downto 0);

    -- RX MFB converted to slv_array_t
    signal rx_mfb_data    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal rx_mfb_meta    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_mfb_sof     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_pos : slv_array_t(2-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal rx_mfb_eof_pos : slv_array_t(2-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal rx_mfb_src_rdy : std_logic_vector(2-1 downto 0);
    signal rx_mfb_dst_rdy : std_logic_vector(2-1 downto 0);

    -- RX MVB hdr with payload added
    signal rx_mvb_hdr_p_arr : slv_array_2d_t(2-1 downto 0)(MVB_ITEMS-1 downto 0)(1+HDR_WIDTH-1 downto 0);
    signal rx_mvb_hdr_p     : slv_array_t(2-1 downto 0)(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);

    -----------------------------------------------

    -- RX MVB hdr from input PIPEs with payload added
    signal rx_in_pipe_mvb_hdr_p     : slv_array_t(2-1 downto 0)(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0) := (others => (others => '0'));
    signal rx_in_pipe_mvb_hdr_p_arr : slv_array_2d_t(2-1 downto 0)(MVB_ITEMS-1 downto 0)(1+HDR_WIDTH-1 downto 0);

    -- RX MVB from input PIPEs
    signal rx_in_pipe_mvb_data     : slv_array_t(2-1 downto 0)(MVB_ITEMS*MVB_DATA_W-1 downto 0);
    signal rx_in_pipe_mvb_hdr      : slv_array_t(2-1 downto 0)(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal rx_in_pipe_mvb_payload  : slv_array_t(2-1 downto 0)(MVB_ITEMS          -1 downto 0);
    signal rx_in_pipe_mvb_vld      : slv_array_t(2-1 downto 0)(MVB_ITEMS          -1 downto 0);
    signal rx_in_pipe_mvb_src_rdy  : std_logic_vector(2-1 downto 0);
    signal rx_in_pipe_mvb_dst_rdy  : std_logic_vector(2-1 downto 0);

    -- RX MFB_in_pipe from input PIPEs
    signal rx_in_pipe_mfb_data    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal rx_in_pipe_mfb_meta    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_in_pipe_mfb_sof     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_in_pipe_mfb_eof     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_in_pipe_mfb_sof_pos : slv_array_t(2-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal rx_in_pipe_mfb_eof_pos : slv_array_t(2-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal rx_in_pipe_mfb_src_rdy : std_logic_vector(2-1 downto 0);
    signal rx_in_pipe_mfb_dst_rdy : std_logic_vector(2-1 downto 0);

    -----------------------------------------------

    -- Extended RX MFB signals
    signal rx_mfb_data_ext    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal rx_mfb_meta_ext    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_mfb_sof_ext     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof_ext     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_pos_ext : slv_array_t(2-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal rx_mfb_eof_pos_ext : slv_array_t(2-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal rx_mfb_vld_ext     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_src_rdy_ext : std_logic_vector(2-1 downto 0);
    signal rx_mfb_dst_rdy_ext : std_logic_vector(2-1 downto 0);

    -----------------------------------------------

    -- MFB input register
    signal mfb_input_data_reg    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal mfb_input_meta_reg    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_input_sof_reg     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_eof_reg     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_sof_pos_reg : slv_array_t(2-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_input_eof_pos_reg : slv_array_t(2-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_input_vld_reg     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_reg_vld     : std_logic_vector(2-1 downto 0);
    signal mfb_input_reg_rd      : std_logic_vector(2-1 downto 0);
    signal mfb_input_reg_wr      : std_logic_vector(2-1 downto 0);

    -----------------------------------------------

    -- MFB input register updating
    signal mfb_input_update_eof       : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_update_vld       : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_reg_upd          : std_logic_vector(2-1 downto 0);

    -- MVB Shakedown
    signal mvb_input_shake_tx_data    : std_logic_vector(MVB_ITEMS*MVB_DATA_W-1 downto 0);
    signal mvb_input_shake_tx_vld     : std_logic_vector(MVB_ITEMS           -1 downto 0);
    signal mvb_input_shake_tx_src_rdy : std_logic;
    signal mvb_input_shake_tx_dst_rdy : std_logic;

    -----------------------------------------------

    -- switch
    signal switch_fifoxm_di    : std_logic_vector(MVB_ITEMS    -1 downto 0);
    signal switch_fifoxm_wr    : std_logic_vector(MVB_ITEMS    -1 downto 0);
    signal switch_fifoxm_full  : std_logic;
    signal switch_fifoxm_do    : std_logic_vector(MFB_REGIONS+1-1 downto 0);
    signal switch_fifoxm_rd    : std_logic_vector(MFB_REGIONS+1-1 downto 0);
    signal switch_fifoxm_empty : std_logic_vector(MFB_REGIONS+1-1 downto 0);

    -----------------------------------------------

    -- currently used switch info
    signal switch_first_0_ptr      : unsigned(log2(MFB_REGIONS+1+1)-1 downto 0);
    signal switch_first_1_ptr      : unsigned(log2(MFB_REGIONS+1+1)-1 downto 0);
    signal switch_currentI         : integer := 0;
    signal switch_current_pac_cntI : integer := 0;

    -- passed packets counter per input region
    signal mfb_input_pac_passed_cntI   : i_array_2d_t(2-1 downto 0)(MFB_REGIONS+1-1 downto 0) := (others => (others => 0));
    -- apeared packets counter per input region
    signal mfb_input_pac_appeared_cntI : i_array_2d_t(2-1 downto 0)(MFB_REGIONS+1-1 downto 0) := (others => (others => 0));

    -- sof_pos / eof_pos comparissons
    signal mfb_input_sof_pos_arr_narrow_u : u_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(CORR_SOF_POS_WIDTH-1 downto 0);
    signal mfb_input_eof_pos_arr_narrow_u : u_array_2d_t(2-1 downto 0)(MFB_REGIONS-1 downto 0)(CORR_SOF_POS_WIDTH-1 downto 0);
    signal mfb_sof_after_eof            : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- MFB data reading
    signal mfb_region_read_req : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_data_mux_selI   : integer := 0;

    -----------------------------------------------

    -- new data for MVB output register
    signal mvb_output_hdr         : std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal mvb_output_payload     : std_logic_vector(MVB_ITEMS          -1 downto 0);
    signal mvb_output_vld         : std_logic_vector(MVB_ITEMS          -1 downto 0);
    signal mvb_output_src_rdy     : std_logic;

    signal mvb_output_hdr_payload : std_logic_vector(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);
    signal tx_mvb_hdr_payload     : std_logic_vector(MVB_ITEMS*(1+HDR_WIDTH)-1 downto 0);

    -- new data for MFB output register
    signal mfb_output_data        : std_logic_vector(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal mfb_output_meta        : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_output_sof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_output_eof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_output_sof_pos     : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_output_eof_pos     : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_output_src_rdy     : std_logic;

    -----------------------------------------------

    -- MVB output register
    signal mvb_output_hdr_reg     : std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal mvb_output_payload_reg : std_logic_vector(MVB_ITEMS          -1 downto 0);
    signal mvb_output_vld_reg     : std_logic_vector(MVB_ITEMS          -1 downto 0);
    signal mvb_output_src_rdy_reg : std_logic;
    signal mvb_output_dst_rdy_reg : std_logic;
    signal mvb_output_dst_rdy     : std_logic;

    -- MFB output register
    signal mfb_output_data_reg    : std_logic_vector(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal mfb_output_meta_reg    : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_output_sof_reg     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_output_eof_reg     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_output_sof_pos_reg : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_output_eof_pos_reg : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_output_src_rdy_reg : std_logic;
    signal mfb_output_dst_rdy_reg : std_logic;
    signal mfb_output_dst_rdy     : std_logic;

    ---------------------------------------------------------------------------

    --attribute mark_debug : string;
    --attribute mark_debug of mfb_input_data_reg    : signal is "true";
    --attribute mark_debug of mfb_input_meta_reg    : signal is "true";
    --attribute mark_debug of mfb_input_sof_reg     : signal is "true";
    --attribute mark_debug of mfb_input_eof_reg     : signal is "true";
    --attribute mark_debug of mfb_input_sof_pos_reg : signal is "true";
    --attribute mark_debug of mfb_input_eof_pos_reg : signal is "true";
    --attribute mark_debug of mfb_input_vld_reg     : signal is "true";
    --attribute mark_debug of mfb_input_reg_vld     : signal is "true";
    --attribute mark_debug of mfb_input_reg_rd      : signal is "true";
    --attribute mark_debug of mfb_input_reg_wr      : signal is "true";
    --attribute mark_debug of mfb_input_update_eof     : signal is "true";
    --attribute mark_debug of mfb_input_update_vld     : signal is "true";
    --attribute mark_debug of mfb_input_reg_upd        : signal is "true";
    --attribute mark_debug of switch_fifoxm_di    : signal is "true";
    --attribute mark_debug of switch_fifoxm_wr    : signal is "true";
    --attribute mark_debug of switch_fifoxm_full  : signal is "true";
    --attribute mark_debug of switch_fifoxm_do    : signal is "true";
    --attribute mark_debug of switch_fifoxm_rd    : signal is "true";
    --attribute mark_debug of switch_fifoxm_empty : signal is "true";
    --attribute mark_debug of switch_first_0_ptr      : signal is "true";
    --attribute mark_debug of switch_first_1_ptr      : signal is "true";
    --attribute mark_debug of switch_currentI         : signal is "true";
    --attribute mark_debug of switch_current_pac_cntI : signal is "true";
    --attribute mark_debug of mfb_input_pac_passed_cntI    : signal is "true";
    --attribute mark_debug of mfb_input_pac_appeared_cntI  : signal is "true";
    --attribute mark_debug of mfb_input_sof_pos_arr_narrow_u : signal is "true";
    --attribute mark_debug of mfb_input_eof_pos_arr_narrow_u : signal is "true";
    --attribute mark_debug of mfb_sof_after_eof            : signal is "true";
    --attribute mark_debug of mfb_region_read_req : signal is "true";
    --attribute mark_debug of mvb_output_vld     : signal is "true";
    --attribute mark_debug of mvb_output_src_rdy : signal is "true";
    --attribute mark_debug of mfb_output_data    : signal is "true";
    --attribute mark_debug of mfb_output_meta    : signal is "true";
    --attribute mark_debug of mfb_output_sof     : signal is "true";
    --attribute mark_debug of mfb_output_eof     : signal is "true";
    --attribute mark_debug of mfb_output_sof_pos : signal is "true";
    --attribute mark_debug of mfb_output_eof_pos : signal is "true";
    --attribute mark_debug of mfb_output_src_rdy : signal is "true";
    --attribute mark_debug of mvb_output_vld_reg : signal is "true";
    --attribute mark_debug of mvb_output_src_rdy_reg : signal is "true";
    --attribute mark_debug of mvb_output_dst_rdy_reg  : signal is "true";
    --attribute mark_debug of mvb_output_dst_rdy  : signal is "true";

begin

    -- -------------------------------------------------------------------------
    -- Converting input MVB to slv_array_t
    -- -------------------------------------------------------------------------

    rx_mvb_hdr    (0) <= RX0_MVB_HDR;
    rx_mvb_payload(0) <= RX0_MVB_PAYLOAD;
    rx_mvb_vld    (0) <= RX0_MVB_VLD;
    rx_mvb_src_rdy(0) <= RX0_MVB_SRC_RDY;
    RX0_MVB_DST_RDY   <= rx_mvb_dst_rdy(0);

    rx_mvb_hdr    (1) <= RX1_MVB_HDR;
    rx_mvb_payload(1) <= RX1_MVB_PAYLOAD;
    rx_mvb_vld    (1) <= RX1_MVB_VLD;
    rx_mvb_src_rdy(1) <= RX1_MVB_SRC_RDY;
    RX1_MVB_DST_RDY   <= rx_mvb_dst_rdy(1);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Converting input MFB to slv_array_t
    -- -------------------------------------------------------------------------

    rx_mfb_data   (0) <= RX0_MFB_DATA;
    rx_mfb_meta   (0) <= RX0_MFB_META;
    rx_mfb_sof    (0) <= RX0_MFB_SOF;
    rx_mfb_eof    (0) <= RX0_MFB_EOF;
    rx_mfb_sof_pos(0) <= RX0_MFB_SOF_POS;
    rx_mfb_eof_pos(0) <= RX0_MFB_EOF_POS;
    rx_mfb_src_rdy(0) <= RX0_MFB_SRC_RDY;
    RX0_MFB_DST_RDY   <= rx_mfb_dst_rdy(0);

    rx_mfb_data   (1) <= RX1_MFB_DATA;
    rx_mfb_meta   (1) <= RX1_MFB_META;
    rx_mfb_sof    (1) <= RX1_MFB_SOF;
    rx_mfb_eof    (1) <= RX1_MFB_EOF;
    rx_mfb_sof_pos(1) <= RX1_MFB_SOF_POS;
    rx_mfb_eof_pos(1) <= RX1_MFB_EOF_POS;
    rx_mfb_src_rdy(1) <= RX1_MFB_SRC_RDY;
    RX1_MFB_DST_RDY   <= rx_mfb_dst_rdy(1);

    -- -------------------------------------------------------------------------

    no_in_pipe_gen : if (IN_PIPE_EN=false) generate

        -- -------------------------------------------------------------------------
        -- no in PIPEs
        -- -------------------------------------------------------------------------

        no_in_pipe_assign_gen : for i in 0 to 2-1 generate
            rx_in_pipe_mvb_hdr    (i) <= rx_mvb_hdr    (i);
            rx_in_pipe_mvb_payload(i) <= rx_mvb_payload(i);
            rx_in_pipe_mvb_vld    (i) <= rx_mvb_vld    (i);
            rx_in_pipe_mvb_src_rdy(i) <= rx_mvb_src_rdy(i);
            rx_mvb_dst_rdy        (i) <= rx_in_pipe_mvb_dst_rdy(i);

            rx_in_pipe_mfb_data   (i) <= rx_mfb_data   (i);
            rx_in_pipe_mfb_meta   (i) <= rx_mfb_meta   (i);
            rx_in_pipe_mfb_sof    (i) <= rx_mfb_sof    (i);
            rx_in_pipe_mfb_eof    (i) <= rx_mfb_eof    (i);
            rx_in_pipe_mfb_sof_pos(i) <= rx_mfb_sof_pos(i);
            rx_in_pipe_mfb_eof_pos(i) <= rx_mfb_eof_pos(i);
            rx_in_pipe_mfb_src_rdy(i) <= rx_mfb_src_rdy(i);
            rx_mfb_dst_rdy        (i) <= rx_in_pipe_mfb_dst_rdy(i);
        end generate;

        -- -------------------------------------------------------------------------

    end generate;

    in_pipe_gen : if (IN_PIPE_EN=true) generate

        -- -------------------------------------------------------------------------
        -- MVB in PIPEs
        -- -------------------------------------------------------------------------

        mvb_in_pipes_gen : for i in 0 to 2-1 generate
        begin

            rx_mvb_hdr_p_gen : for e in 0 to MVB_ITEMS-1 generate
                rx_mvb_hdr_p_payload_en_gen : if (PAYLOAD_ENABLED(i)) generate
                    rx_mvb_hdr_p_arr(i)(e) <= rx_mvb_payload(i)(e) & rx_mvb_hdr(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH);
                end generate;
                rx_mvb_hdr_p_payload_dis_gen : if (not PAYLOAD_ENABLED(i)) generate
                    rx_mvb_hdr_p_arr(i)(e) <= '0' & rx_mvb_hdr(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH);
                end generate;
            end generate;
            rx_mvb_hdr_p(i) <= slv_array_ser(rx_mvb_hdr_p_arr(i));

            mvb_in_pipe_i : entity work.MVB_PIPE
            generic map(
               ITEMS          => MVB_ITEMS  ,
               ITEM_WIDTH     => 1+HDR_WIDTH,
               FAKE_PIPE      => false      ,
               USE_DST_RDY    => true       ,
               DEVICE         => DEVICE
            )
            port map(
               CLK           => CLK  ,
               RESET         => RESET,

               RX_DATA       => rx_mvb_hdr_p  (i),
               RX_VLD        => rx_mvb_vld    (i),
               RX_SRC_RDY    => rx_mvb_src_rdy(i),
               RX_DST_RDY    => rx_mvb_dst_rdy(i),

               TX_DATA       => rx_in_pipe_mvb_hdr_p  (i),
               TX_VLD        => rx_in_pipe_mvb_vld    (i),
               TX_SRC_RDY    => rx_in_pipe_mvb_src_rdy(i),
               TX_DST_RDY    => rx_in_pipe_mvb_dst_rdy(i)
            );

            rx_in_pipe_mvb_hdr_p_arr(i) <= slv_array_deser(rx_in_pipe_mvb_hdr_p(i),MVB_ITEMS);

            rx_in_pipe_mvb_out_gen : for e in 0 to MVB_ITEMS-1 generate
                rx_in_pipe_mvb_hdr(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH) <= rx_in_pipe_mvb_hdr_p_arr(i)(e)(HDR_WIDTH-1 downto 0);

                rx_in_pipe_mvb_out_payload_en_gen : if (PAYLOAD_ENABLED(i)) generate
                    rx_in_pipe_mvb_payload(i)(e) <= rx_in_pipe_mvb_hdr_p_arr(i)(e)(HDR_WIDTH);
                end generate;
                rx_in_pipe_mvb_out_payload_dis_gen : if (not PAYLOAD_ENABLED(i)) generate
                    rx_in_pipe_mvb_payload(i)(e) <= '0';
                end generate;
            end generate;


        end generate;

        -- -------------------------------------------------------------------------

        -- -------------------------------------------------------------------------
        -- MFB in PIPEs
        -- -------------------------------------------------------------------------

        mfb_in_pipes_gen : for i in 0 to 2-1 generate

            mfb_in_pipe_i : entity work.MFB_PIPE
            generic map(
               REGIONS        => MFB_REGIONS           ,
               REGION_SIZE    => MFB_REG_SIZE          ,
               BLOCK_SIZE     => MFB_BLOCK_SIZE        ,
               ITEM_WIDTH     => MFB_ITEM_WIDTH        ,
               META_WIDTH     => MFB_META_WIDTH        ,
               FAKE_PIPE      => not PAYLOAD_ENABLED(i),
               USE_DST_RDY    => true                  ,
               DEVICE         => DEVICE
            )
            port map(
               CLK           => CLK  ,
               RESET         => RESET,

               RX_DATA       => rx_mfb_data   (i),
               RX_META       => rx_mfb_meta   (i),
               RX_SOF_POS    => rx_mfb_sof_pos(i),
               RX_EOF_POS    => rx_mfb_eof_pos(i),
               RX_SOF        => rx_mfb_sof    (i),
               RX_EOF        => rx_mfb_eof    (i),
               RX_SRC_RDY    => rx_mfb_src_rdy(i),
               RX_DST_RDY    => rx_mfb_dst_rdy(i),

               TX_DATA       => rx_in_pipe_mfb_data   (i),
               TX_META       => rx_in_pipe_mfb_meta   (i),
               TX_SOF_POS    => rx_in_pipe_mfb_sof_pos(i),
               TX_EOF_POS    => rx_in_pipe_mfb_eof_pos(i),
               TX_SOF        => rx_in_pipe_mfb_sof    (i),
               TX_EOF        => rx_in_pipe_mfb_eof    (i),
               TX_SRC_RDY    => rx_in_pipe_mfb_src_rdy(i),
               TX_DST_RDY    => rx_in_pipe_mfb_dst_rdy(i)
            );

        end generate;

        -- -------------------------------------------------------------------------

    end generate;

    -- -------------------------------------------------------------------------
    -- RX MFB extention unit
    -- -------------------------------------------------------------------------

    rx_mfb_ext_gen : for i in 0 to 2-1 generate

        rx_mfb_ext_i : entity work.MFB_AUXILIARY_SIGNALS
        generic map(
            REGIONS     => MFB_REGIONS   ,
            REGION_SIZE => MFB_REG_SIZE  ,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,

            REGION_AUX_EN => true        ,
            BLOCK_AUX_EN  => false       ,
            ITEM_AUX_EN   => false
        )
        port map(
            CLK   => CLK  ,
            RESET => RESET,

            RX_DATA       => rx_in_pipe_mfb_data   (i),
            RX_SOF_POS    => rx_in_pipe_mfb_sof_pos(i),
            RX_EOF_POS    => rx_in_pipe_mfb_eof_pos(i),
            RX_SOF        => rx_in_pipe_mfb_sof    (i),
            RX_EOF        => rx_in_pipe_mfb_eof    (i),
            RX_SRC_RDY    => rx_in_pipe_mfb_src_rdy(i),
            RX_DST_RDY    => rx_in_pipe_mfb_dst_rdy(i),

            TX_DATA       => rx_mfb_data_ext   (i),
            TX_SOF_POS    => rx_mfb_sof_pos_ext(i),
            TX_EOF_POS    => rx_mfb_eof_pos_ext(i),
            TX_SOF        => rx_mfb_sof_ext    (i),
            TX_EOF        => rx_mfb_eof_ext    (i),
            TX_REGION_VLD => rx_mfb_vld_ext    (i),
            TX_SRC_RDY    => rx_mfb_src_rdy_ext(i),
            TX_DST_RDY    => rx_mfb_dst_rdy_ext(i)
        );

        rx_mfb_meta_ext(i) <= rx_in_pipe_mfb_meta(i);

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Input MFB registers
    -- -------------------------------------------------------------------------

    mfb_input_reg_g : for i in 0 to 2-1 generate
        mfb_input_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                -- read
                if (mfb_input_reg_rd(i)='1') then
                    mfb_input_reg_vld(i) <= '0';
                end if;

                -- update
                -- Valid bits of Regions and EOFs can be modified
                -- when only part of the data is being read.
                if (mfb_input_reg_upd(i)='1') then
                    mfb_input_eof_reg(i) <= mfb_input_update_eof(i);
                    mfb_input_vld_reg(i) <= mfb_input_update_vld(i);
                end if;

                -- write
                if (mfb_input_reg_wr(i)='1') then
                    mfb_input_data_reg   (i) <= rx_mfb_data_ext   (i);
                    mfb_input_meta_reg   (i) <= rx_mfb_meta_ext   (i);
                    mfb_input_sof_reg    (i) <= rx_mfb_sof_ext    (i);
                    mfb_input_eof_reg    (i) <= rx_mfb_eof_ext    (i);
                    mfb_input_sof_pos_reg(i) <= rx_mfb_sof_pos_ext(i);
                    mfb_input_eof_pos_reg(i) <= rx_mfb_eof_pos_ext(i);
                    mfb_input_vld_reg    (i) <= rx_mfb_vld_ext    (i);
                    mfb_input_reg_vld    (i) <= rx_mfb_src_rdy_ext(i);
                end if;

                if (RESET='1') then
                    mfb_input_reg_vld(i) <= '0';
                end if;
            end if;
        end process;

        mfb_input_reg_wr(i)   <= '1' when mfb_input_reg_vld(i)='0' or mfb_input_reg_rd(i)='1' else '0';
        rx_mfb_dst_rdy_ext(i) <= mfb_input_reg_wr(i);

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB sending
    -- -------------------------------------------------------------------------

    rx_in_pipe_mvb_data_g : for i in 0 to 2-1 generate
        rx_in_pipe_mvb_data_g2 : for e in 0 to MVB_ITEMS-1 generate
            rx_in_pipe_mvb_data(i)(e*(MVB_DATA_W)+HDR_WIDTH-1 downto e*(MVB_DATA_W)) <= rx_in_pipe_mvb_hdr(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH);
            rx_in_pipe_mvb_data(i)(e*(MVB_DATA_W)+HDR_WIDTH)                          <= '0' when (i = 0) else '1';
            rx_in_pipe_mvb_data(i)(e*(MVB_DATA_W)+HDR_WIDTH+1)                        <= rx_in_pipe_mvb_payload(i)(e);
        end generate;
    end generate;

    mvb_merge_st_i : entity work.MVB_MERGE_STREAMS
    generic map(
        MVB_ITEMS       => MVB_ITEMS,
        MVB_ITEM_WIDTH  => MVB_DATA_W, -- payload & switch & header
        RX_STREAMS      => 2,
        RX_SHAKEDOWN_EN => True,
        SW_TIMEOUT_W    => SW_TIMEOUT_WIDTH,
        DEVICE          => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => rx_in_pipe_mvb_data,
        RX_VLD     => rx_in_pipe_mvb_vld,
        RX_SRC_RDY => rx_in_pipe_mvb_src_rdy,
        RX_DST_RDY => rx_in_pipe_mvb_dst_rdy,

        TX_DATA    => mvb_input_shake_tx_data,
        TX_VLD     => mvb_input_shake_tx_vld,
        TX_SRC_RDY => mvb_input_shake_tx_src_rdy,
        TX_DST_RDY => mvb_input_shake_tx_dst_rdy
    );

    mvb_shake_tx_gen : for i in 0 to MVB_ITEMS-1 generate
        mvb_output_hdr        ((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH) <= mvb_input_shake_tx_data(i*(MVB_DATA_W)+HDR_WIDTH-1 downto i*(MVB_DATA_W));
        mvb_output_payload    (i)                                    <= mvb_input_shake_tx_data(i*(MVB_DATA_W)+HDR_WIDTH+1);

        mvb_output_hdr_payload((i+1)*(1+HDR_WIDTH)-1 downto i*(1+HDR_WIDTH)) <= mvb_output_payload(i) & mvb_output_hdr((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH);
    end generate;

    mvb_output_vld             <= mvb_input_shake_tx_vld;
    mvb_output_src_rdy         <= mvb_input_shake_tx_src_rdy and (not switch_fifoxm_full);
    mvb_input_shake_tx_dst_rdy <= mvb_output_dst_rdy and (not switch_fifoxm_full);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Switch decision FIFOX Multi
    -- -------------------------------------------------------------------------

    switch_fifoxm_in_gen : for i in 0 to MVB_ITEMS-1 generate
        switch_fifoxm_di(i) <= mvb_input_shake_tx_data(i*(MVB_DATA_W)+HDR_WIDTH);
        --                    (     src_rdy header      ) and (     valid header      ) and (              header with payload                 ) and ( out reg ready )
        switch_fifoxm_wr(i) <= mvb_input_shake_tx_src_rdy and mvb_input_shake_tx_vld(i) and mvb_input_shake_tx_data(i*(MVB_DATA_W)+HDR_WIDTH+1) and mvb_output_dst_rdy;
    end generate;

    switch_fifoxm_i : entity work.FIFOX_MULTI(SHAKEDOWN)
    generic map(
        DATA_WIDTH     => 1            ,
        ITEMS          => MVB_ITEMS*32 ,
        WRITE_PORTS    => MVB_ITEMS    ,
        READ_PORTS     => MFB_REGIONS+1,
        RAM_TYPE       => "AUTO"       ,
        SAFE_READ_MODE => false        ,
        DEVICE         => DEVICE
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => switch_fifoxm_di   ,
        WR     => switch_fifoxm_wr   ,
        FULL   => switch_fifoxm_full ,
        DO     => switch_fifoxm_do   ,
        RD     => switch_fifoxm_rd   ,
        EMPTY  => switch_fifoxm_empty
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MFB sending
    -- -------------------------------------------------------------------------

    -- count maximum number of packets, that can be accepted from an input now
    switch_info_pr : process (switch_fifoxm_do,switch_fifoxm_empty)
    begin
        switch_first_0_ptr <= (others => '0');
        switch_first_1_ptr <= (others => '0');

        -- first '0' detector
        for i in 0 to MFB_REGIONS+1-1 loop
            exit when (switch_fifoxm_do(i)='0' or switch_fifoxm_empty(i)='1');
            switch_first_0_ptr <= to_unsigned(i+1,log2(MFB_REGIONS+1+1));
        end loop;

        -- first '1' detector
        for i in 0 to MFB_REGIONS+1-1 loop
            exit when (switch_fifoxm_do(i)='1' or switch_fifoxm_empty(i)='1');
            switch_first_1_ptr <= to_unsigned(i+1,log2(MFB_REGIONS+1+1));
        end loop;
    end process;
    switch_currentI         <= 1 when switch_fifoxm_do(0)='1' else 0;
    switch_current_pac_cntI <= to_integer(switch_first_1_ptr) when switch_currentI=0 else to_integer(switch_first_0_ptr);

    -- count the number of packets passed in every region of the input MFB
    pac_passed_cnt_pr : process (mfb_input_vld_reg,mfb_input_eof_reg)
        variable cnt : i_array_t(2-1 downto 0);
    begin
        mfb_input_pac_passed_cntI <= (others => (others => 0));
        cnt := (others => 0);

        for i in 0 to 2-1 loop
            for e in 0 to MFB_REGIONS-1 loop
                mfb_input_pac_passed_cntI(i)(e) <= cnt(i);
                if (mfb_input_vld_reg(i)(e)='1' and mfb_input_eof_reg(i)(e)='1') then
                    cnt(i) := cnt(i)+1;
                end if;
            end loop;
            mfb_input_pac_passed_cntI(i)(MFB_REGIONS) <= cnt(i);
        end loop;
    end process;

    -- count the number of packets appearing in every region of the input MFB
    pac_appeared_cnt_pr : process (mfb_input_vld_reg, mfb_input_sof_reg, mfb_input_eof_reg, mfb_sof_after_eof)
        variable cnt : i_array_t(2-1 downto 0);
    begin
        mfb_input_pac_appeared_cntI <= (others => (others => 0));
        cnt := (others => 0);

        for i in 0 to 2-1 loop
            -- add part of packet continuing from the previous word
            if (mfb_input_vld_reg(i)(0)='1' and ((mfb_sof_after_eof(i)(0)='1' and mfb_input_eof_reg(i)(0)='1') or mfb_input_sof_reg(i)(0)='0')) then
                cnt(i) := cnt(i)+1;
            end if;

            for e in 0 to MFB_REGIONS-1 loop
                if (mfb_input_vld_reg(i)(e)='1' and mfb_input_sof_reg(i)(e)='1') then
                    cnt(i) := cnt(i)+1;
                end if;
                mfb_input_pac_appeared_cntI(i)(e) <= cnt(i);
            end loop;
            mfb_input_pac_appeared_cntI(i)(MFB_REGIONS) <= cnt(i);
        end loop;
    end process;

    -- compare sof pos and eof_pos in every input region
    mfb_sof_eof_cmp_gen : for i in 0 to 2-1 generate
        mfb_sof_eof_cmp_i_gen : for e in 0 to MFB_REGIONS-1 generate

            mfb_input_sof_pos_arr_narrow_u(i)(e) <= unsigned(mfb_input_sof_pos_reg(i)((e+1)*SOF_POS_WIDTH-1 downto (e+1)*SOF_POS_WIDTH-CORR_SOF_POS_WIDTH));
            mfb_input_eof_pos_arr_narrow_u(i)(e) <= unsigned(mfb_input_eof_pos_reg(i)((e+1)*EOF_POS_WIDTH-1 downto (e+1)*EOF_POS_WIDTH-CORR_SOF_POS_WIDTH));

            mfb_sof_after_eof(i)(e) <= '1' when mfb_input_sof_pos_arr_narrow_u(i)(e)>mfb_input_eof_pos_arr_narrow_u(i)(e) else '0';

        end generate;
    end generate;

    -- input regions read requests
    mfb_region_read_req_gen : for i in 0 to 2-1 generate
        mfb_region_read_req_i_gen : for e in 0 to MFB_REGIONS-1 generate

            mfb_region_read_req(i)(e) <= '1' when switch_currentI=i and switch_current_pac_cntI>mfb_input_pac_passed_cntI(i)(e) else '0';

        end generate;
    end generate;

    -- data, sof_pos and eof_pos multiplexing
    mfb_data_mux_selI  <= switch_currentI;
    mfb_output_data    <= mfb_input_data_reg   (mfb_data_mux_selI);
    mfb_output_meta    <= mfb_input_meta_reg   (mfb_data_mux_selI);
    mfb_output_sof_pos <= mfb_input_sof_pos_reg(mfb_data_mux_selI);
    mfb_output_eof_pos <= mfb_input_eof_pos_reg(mfb_data_mux_selI);

    -- sof and eof generation
    mfb_output_sof_eof_gen : for i in 0 to MFB_REGIONS-1 generate

        mfb_output_sof(i) <= '1' when     (mfb_region_read_req(0)(i)='1' or mfb_region_read_req(1)(i)='1')                                   -- some data is being loaded to this region
                                      and mfb_input_vld_reg(mfb_data_mux_selI)(i)='1' and mfb_input_sof_reg(mfb_data_mux_selI)(i)='1'        -- the data contains a valid SOF
                                      and (    switch_current_pac_cntI>=mfb_input_pac_appeared_cntI(mfb_data_mux_selI)(i)                    -- the SOF's packet can be read (continuing to next region)
--                                           or  (mfb_sof_after_eof(mfb_data_mux_selI)(i)='0' and mfb_input_eof_reg(mfb_data_mux_selI)(i)='1') -- the SOF's packet can be read (whole in this region)
                                          )
                                      else '0';

        mfb_output_eof(i) <= '1' when     (mfb_region_read_req(0)(i)='1' or mfb_region_read_req(1)(i)='1')                            -- some data is being loaded to this region
                                      and mfb_input_vld_reg(mfb_data_mux_selI)(i)='1' and mfb_input_eof_reg(mfb_data_mux_selI)(i)='1' -- the data contains a valid EOF
                                      else '0';

    end generate;

    -- input update generation
    mfb_input_update_gen : for i in 0 to 2-1 generate
        mfb_input_update_i_gen : for e in 0 to MFB_REGIONS-1 generate

        mfb_input_update_eof(i)(e) <= '0' when     mfb_region_read_req(i)(e)='1' -- region read
                                               else mfb_input_eof_reg(i)(e);

        mfb_input_update_vld(i)(e) <= '0' when     mfb_region_read_req(i)(e)='1'                                                                      -- region read
                                               and (    mfb_input_sof_reg(i)(e)='0'                                                                   -- no SOF in this region
                                                    or  switch_current_pac_cntI>=mfb_input_pac_appeared_cntI(mfb_data_mux_selI)(e)                    -- the SOF's packet can be read (continuing to next region)
--                                                    or  (mfb_sof_after_eof(mfb_data_mux_selI)(i)='0' and mfb_input_eof_reg(mfb_data_mux_selI)(i)='1') -- the SOF's packet can be read (whole in this region)
                                                   )
                                               else mfb_input_vld_reg(i)(e);

        end generate;
    end generate;

    -- MFB sending control signals setting
    mfb_send_ctrl_gen : for i in 0 to 2-1 generate

        mfb_input_reg_rd (i) <= '1' when     switch_currentI=i and switch_current_pac_cntI>=mfb_input_pac_appeared_cntI(mfb_data_mux_selI)(MFB_REGIONS) -- read whole input when all packets can be processed
                                         and mfb_output_dst_rdy='1'                                                                                      -- only read when output is ready
                                         and switch_fifoxm_empty(0)='0'                                                                                 -- only read when switch info is valid
                                         else '0';

        mfb_input_reg_upd(i) <= '1' when     mfb_output_dst_rdy='1'      -- only update when output is ready
                                         and switch_fifoxm_empty(0)='0' -- only read when switch info is valid
                                         else '0';

    end generate;

    -- Switch FIFOXM reading
    mfb_switch_fifxm_rd_gen : for i in 0 to MFB_REGIONS+1-1 generate

        switch_fifoxm_rd (i) <= '1' when     i<mfb_input_pac_passed_cntI(mfb_data_mux_selI)(MFB_REGIONS) -- read switch for each packet with an EOF in this word
                                         and i<switch_current_pac_cntI                                   -- only read currently active reads
                                         and mfb_output_dst_rdy='1'                                       -- only read when output is ready
                                         and mfb_input_reg_vld(mfb_data_mux_selI)='1'                    -- only read when input is valid
                                         else '0';

    end generate;
    mfb_output_src_rdy <= '1' when switch_fifoxm_empty(0)='0' and mfb_input_reg_vld(mfb_data_mux_selI)='1' and mfb_input_reg_vld(switch_currentI)='1' else '0'; -- output is valid when both switch and data are valid

    -- -------------------------------------------------------------------------

    out_reg_gen : if (OUT_PIPE_EN=false) generate

        -- -------------------------------------------------------------------------
        -- MVB output register
        -- -------------------------------------------------------------------------

        mvb_output_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (mvb_output_dst_rdy='1') then
                    mvb_output_hdr_reg     <= mvb_output_hdr;
                    mvb_output_payload_reg <= mvb_output_payload;
                    mvb_output_vld_reg     <= mvb_output_vld;
                    mvb_output_src_rdy_reg <= mvb_output_src_rdy;
                end if;
                if (RESET='1') then
                    mvb_output_src_rdy_reg <= '0';
                end if;
            end if;
        end process;

        mvb_output_dst_rdy <= mvb_output_dst_rdy_reg or not mvb_output_src_rdy_reg;

        -- -------------------------------------------------------------------------

        -- -------------------------------------------------------------------------
        -- MFB output register
        -- -------------------------------------------------------------------------

        mfb_output_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (mfb_output_dst_rdy='1') then
                    mfb_output_data_reg    <= mfb_output_data;
                    mfb_output_meta_reg    <= mfb_output_meta;
                    mfb_output_sof_reg     <= mfb_output_sof;
                    mfb_output_eof_reg     <= mfb_output_eof;
                    mfb_output_sof_pos_reg <= mfb_output_sof_pos;
                    mfb_output_eof_pos_reg <= mfb_output_eof_pos;
                    mfb_output_src_rdy_reg <= mfb_output_src_rdy;
                end if;
                if (RESET='1') then
                    mfb_output_src_rdy_reg <= '0';
                end if;
            end if;
        end process;

        mfb_output_dst_rdy <= mfb_output_dst_rdy_reg or not mfb_output_src_rdy_reg;

        -- -------------------------------------------------------------------------

        -- -------------------------------------------------------------------------
        -- TX generation
        -- -------------------------------------------------------------------------

        TX_MVB_HDR             <= mvb_output_hdr_reg;
        TX_MVB_PAYLOAD         <= mvb_output_payload_reg;
        TX_MVB_VLD             <= mvb_output_vld_reg;
        TX_MVB_SRC_RDY         <= mvb_output_src_rdy_reg;
        mvb_output_dst_rdy_reg <= TX_MVB_DST_RDY;

        TX_MFB_DATA       <= mfb_output_data_reg;
        TX_MFB_META       <= mfb_output_meta_reg;
        TX_MFB_SOF        <= mfb_output_sof_reg;
        TX_MFB_EOF        <= mfb_output_eof_reg;
        TX_MFB_SOF_POS    <= mfb_output_sof_pos_reg;
        TX_MFB_EOF_POS    <= mfb_output_eof_pos_reg;
        TX_MFB_SRC_RDY    <= mfb_output_src_rdy_reg;
        mfb_output_dst_rdy_reg <= TX_MFB_DST_RDY;

        -- -------------------------------------------------------------------------
    end generate;

    out_pipe_gen : if (OUT_PIPE_EN=true) generate

        -- -------------------------------------------------------------------------
        -- MVB out PIPE
        -- -------------------------------------------------------------------------

        mvb_out_pipe_i : entity work.MVB_PIPE
        generic map(
           ITEMS          => MVB_ITEMS      ,
           ITEM_WIDTH     => HDR_WIDTH+1    , -- add Payload info
           FAKE_PIPE      => not OUT_PIPE_EN,
           USE_DST_RDY    => true           ,
           DEVICE         => DEVICE
        )
        port map(
           CLK           => CLK  ,
           RESET         => RESET,

           RX_DATA       => mvb_output_hdr_payload,
           RX_VLD        => mvb_output_vld        ,
           RX_SRC_RDY    => mvb_output_src_rdy    ,
           RX_DST_RDY    => mvb_output_dst_rdy    ,

           TX_DATA       => tx_mvb_hdr_payload    ,
           TX_VLD        => TX_MVB_VLD            ,
           TX_SRC_RDY    => TX_MVB_SRC_RDY        ,
           TX_DST_RDY    => TX_MVB_DST_RDY
        );

        tx_mvb_hdr_gen : for i in 0 to MVB_ITEMS-1 generate
            TX_MVB_HDR    ((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH) <= tx_mvb_hdr_payload(i*(1+HDR_WIDTH)+HDR_WIDTH-1 downto i*(1+HDR_WIDTH));
            TX_MVB_PAYLOAD(i)                                    <= tx_mvb_hdr_payload(i*(1+HDR_WIDTH)+HDR_WIDTH);
        end generate;

        -- -------------------------------------------------------------------------

        -- -------------------------------------------------------------------------
        -- MFB out PIPE
        -- -------------------------------------------------------------------------

        mfb_out_pipe_i : entity work.MFB_PIPE
        generic map(
           REGIONS        => MFB_REGIONS    ,
           REGION_SIZE    => MFB_REG_SIZE   ,
           BLOCK_SIZE     => MFB_BLOCK_SIZE ,
           ITEM_WIDTH     => MFB_ITEM_WIDTH ,
           META_WIDTH     => MFB_META_WIDTH ,
           FAKE_PIPE      => not PAYLOAD_ENABLED(0) and not PAYLOAD_ENABLED(1),
           USE_DST_RDY    => true           ,
           DEVICE         => DEVICE
        )
        port map(
           CLK           => CLK  ,
           RESET         => RESET,

           RX_DATA       => mfb_output_data   ,
           RX_META       => mfb_output_meta   ,
           RX_SOF_POS    => mfb_output_sof_pos,
           RX_EOF_POS    => mfb_output_eof_pos,
           RX_SOF        => mfb_output_sof    ,
           RX_EOF        => mfb_output_eof    ,
           RX_SRC_RDY    => mfb_output_src_rdy,
           RX_DST_RDY    => mfb_output_dst_rdy ,

           TX_DATA       => TX_MFB_DATA   ,
           TX_META       => TX_MFB_META   ,
           TX_SOF_POS    => TX_MFB_SOF_POS,
           TX_EOF_POS    => TX_MFB_EOF_POS,
           TX_SOF        => TX_MFB_SOF    ,
           TX_EOF        => TX_MFB_EOF    ,
           TX_SRC_RDY    => TX_MFB_SRC_RDY,
           TX_DST_RDY    => TX_MFB_DST_RDY
        );

        -- -------------------------------------------------------------------------

    end generate;

end architecture;
