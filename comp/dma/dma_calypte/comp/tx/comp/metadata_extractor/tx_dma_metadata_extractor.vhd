-- tx_dma_metadata_extractor.vhd: performs initial processing of packets comming to the DMA
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--            David Benes      <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- Note:

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

-- This component processes the incoming PCIe transactions. This does not care about whole DMA
-- frames delimited by the DMA header but processes all frames in general. The metadata on the
-- output are chosen according their usefullness later in the design.
entity TX_DMA_METADATA_EXTRACTOR is
    generic (
        DEVICE : string := "ULTRASCALE";

        -- For generating outputs and calculating the DMA buffers address space
        CHANNELS       : natural := 8;
        -- Pointer with respect to bytes
        POINTER_WIDTH  : natural := 16;

        PCIE_MFB_REGIONS     : natural := 2;
        PCIE_MFB_REGION_SIZE : natural := 1;
        PCIE_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_MFB_ITEM_WIDTH  : natural := 32
        );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- PCIe MFB interface
        -- =========================================================================================
        PCIE_MFB_DATA    : in  std_logic_vector(PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
        -- More information about the content of this port can be found in *pcie_meta_pack*
        PCIE_MFB_META    : in  std_logic_vector(PCIE_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
        PCIE_MFB_SOF     : in  std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        PCIE_MFB_EOF     : in  std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        PCIE_MFB_SOF_POS : in  std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_MFB_EOF_POS : in  std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_MFB_SRC_RDY : in  std_logic;
        PCIE_MFB_DST_RDY : out std_logic;

        -- =========================================================================================
        -- User MFB signals

        -- Metadata are all valid with SOF except for USR_MFB_META_BYTE_EN.
        -- =========================================================================================
        USR_MFB_DATA    : out std_logic_vector(PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
        USR_MFB_META    : out std_logic_vector(PCIE_MFB_REGIONS*(13 + (PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8 + log2(CHANNELS) + 62 +1) -1 downto 0);
        USR_MFB_SOF     : out std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        USR_MFB_EOF     : out std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        USR_MFB_SOF_POS : out std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE)) -1 downto 0);
        USR_MFB_EOF_POS : out std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
        USR_MFB_SRC_RDY : out std_logic;
        USR_MFB_DST_RDY : in  std_logic
        );
end entity;

architecture FULL of TX_DMA_METADATA_EXTRACTOR is

    constant MFB_LENGTH         : natural := PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH;
    constant BAR_APERTURE_INTEL : natural := 24;

    -- =============================================================================================
    -- Defining ranges for meta signal
    -- =============================================================================================
    constant META_IS_DMA_HDR_W : natural := 1;
    constant META_PCIE_ADDR_W  : natural := 62;
    constant META_CHAN_NUM_W   : natural := log2(CHANNELS);
    constant META_BE_W         : natural := (PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8;
    constant META_BYTE_CNT_W   : natural := 13;
    constant META_FBE_W        : natural := 4;
    constant META_LBE_W        : natural := 4;

    constant META_IS_DMA_HDR_O : natural := 0;
    constant META_PCIE_ADDR_O  : natural := META_IS_DMA_HDR_O + META_IS_DMA_HDR_W;
    constant META_CHAN_NUM_O   : natural := META_PCIE_ADDR_O + META_PCIE_ADDR_W;
    constant META_BE_O         : natural := META_CHAN_NUM_O + META_CHAN_NUM_W;
    constant META_BYTE_CNT_O   : natural := META_BE_O + META_BE_W;
    constant META_FBE_O        : natural := META_BYTE_CNT_O + META_BYTE_CNT_W;
    constant META_LBE_O        : natural := META_FBE_O + META_FBE_W;

    subtype META_IS_DMA_HDR is natural range META_IS_DMA_HDR_O + META_IS_DMA_HDR_W -1 downto META_IS_DMA_HDR_O;
    subtype META_PCIE_ADDR is natural range META_PCIE_ADDR_O + META_PCIE_ADDR_W -1 downto META_PCIE_ADDR_O;
    subtype META_CHAN_NUM is natural range META_CHAN_NUM_O + META_CHAN_NUM_W -1 downto META_CHAN_NUM_O;
    subtype META_BE is natural range META_BE_O + META_BE_W -1 downto META_BE_O;
    subtype META_BYTE_CNT is natural range META_BYTE_CNT_O + META_BYTE_CNT_W -1 downto META_BYTE_CNT_O;
    subtype META_FBE is natural range META_FBE_O + META_FBE_W -1 downto META_FBE_O;
    subtype META_LBE is natural range META_LBE_O + META_LBE_W -1 downto META_LBE_O;

    -- =============================================================================================
    -- Internal Signals
    -- =============================================================================================
    -- the extracted pcie header
    signal pcie_hdr_data_int     : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(PCIE_META_REQ_HDR_W -1 downto 0);

    -- Input port arrays
    signal pcie_mfb_data_arr     : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_mfb_meta_arr     : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(PCIE_CQ_META_WIDTH -1 downto 0);

    -- extracted fields from the PCIe header
    signal pcie_hdr_addr         : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(63 downto 0);
    signal pcie_hdr_bar_id       : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(2 downto 0);
    signal pcie_hdr_bar_aperture : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(5 downto 0);
    signal pcie_hdr_fbe          : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(3 downto 0);
    signal pcie_hdr_lbe          : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(3 downto 0);
    signal pcie_hdr_dw_count     : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(10 downto 0);

    signal pcie_addr_mask        : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(63 downto 0);
    signal pcie_addr_masked      : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(63 downto 0);

    -- decoded FBE and LBE signals with continuous rows of 1s
    signal fbe_decoded           : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(3 downto 0);
    signal lbe_decoded           : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(3 downto 0);

    signal chan_num_int          : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(max(1, log2(CHANNELS)) -1 downto 0);
    signal chan_num_stored       : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(max(1, log2(CHANNELS)) -1 downto 0);

    -- Determines if curently contained payload of the incoming PCIe transaction is a DMA header
    signal is_dma_hdr            : std_logic_vector(PCIE_MFB_REGIONS - 1 downto 0);

    -- contains the last byte enable, first byte enable signals from the PCIE META input, the size
    -- of a current PCIE transaction in bytes and one bit indication if DMA header is included in a
    -- current transaction
    signal pcie_mfb_meta_int : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(META_LBE_O + META_LBE_W -1 downto 0);
    signal pcie_tr_byte_cnt  : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(META_BYTE_CNT_W -1 downto 0);

    signal cutt_mfb_data    : std_logic_vector(MFB_LENGTH -1 downto 0);
    signal cutt_mfb_meta    : std_logic_vector(PCIE_MFB_REGIONS*(META_LBE_O + META_LBE_W) -1 downto 0);
    signal cutt_mfb_sof     : std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
    signal cutt_mfb_eof     : std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
    signal cutt_mfb_sof_pos : std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE)) -1 downto 0);
    signal cutt_mfb_eof_pos : std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
    signal cutt_mfb_src_rdy : std_logic;
    signal cutt_mfb_dst_rdy : std_logic;

    signal aux_mfb_data         : std_logic_vector(MFB_LENGTH -1 downto 0);
    signal aux_mfb_meta         : std_logic_vector(PCIE_MFB_REGIONS*(META_LBE_O + META_LBE_W) - 1 downto 0);
    signal aux_mfb_meta_arr     : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(META_LBE_O + META_LBE_W - 1 downto 0);
    signal aux_mfb_sof          : std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
    signal aux_mfb_eof          : std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
    signal aux_mfb_sof_pos      : std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE)) -1 downto 0);
    signal aux_mfb_eof_pos      : std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
    signal aux_mfb_eof_pos_arr  : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
    signal aux_mfb_src_rdy      : std_logic;
    signal aux_mfb_dst_rdy      : std_logic;

    -- reduced meta signal that does not contain FBE and LBE items
    signal aux_mfb_meta_arr_reduced : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(META_BYTE_CNT_O + META_BYTE_CNT_W -1 downto 0);

    signal usr_mfb_lbe_reg  : std_logic_vector(META_LBE_W -1 downto 0);
    signal usr_mfb_lbe_sel  : std_logic_vector(META_LBE_W -1 downto 0);

    -- indicates which items in a current word are valid
    signal mfb_aux_item_vld_int     : std_logic_vector(PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE -1 downto 0);
    signal mfb_aux_item_vld_int_arr : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE -1 downto 0);

    -- byte enable for a whole word
    signal mfb_aux_item_be      : slv_array_2d_t(PCIE_MFB_REGIONS - 1 downto 0)(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE -1 downto 0)(PCIE_MFB_ITEM_WIDTH/8 -1 downto 0);
begin
    -- ============================================================================================
    -- DEBUGGING
    -- ============================================================================================
    pcie_byte_count_g: for i in PCIE_MFB_REGIONS - 1 downto 0 generate
        pcie_byte_count_i : entity work.PCIE_BYTE_COUNT
            generic map (
                OUTPUT_REG => FALSE
            )
            port map (
                CLK            => CLK,
                RESET          => RESET,

                IN_DW_COUNT    => pcie_hdr_dw_count(i),
                IN_FIRST_BE    => pcie_hdr_fbe(i),
                IN_LAST_BE     => pcie_hdr_lbe(i),

                OUT_FIRST_IB   => open,
                OUT_LAST_IB    => open,
                OUT_BYTE_COUNT => pcie_tr_byte_cnt(i));
    end generate;

    -- =============================================================================================
    -- Deserialize input data
    --
    -- NOTE: pcie_hdr_addr_len is not used but it does not make sense anyway since the BAR aperture
    -- is never greater than 32 bits. The top 32 bits are always 0.
    -- =============================================================================================

    pcie_mfb_data_arr   <= slv_array_deser(PCIE_MFB_DATA, PCIE_MFB_REGIONS);
    pcie_mfb_meta_arr   <= slv_array_deser(PCIE_MFB_META, PCIE_MFB_REGIONS);

    pcie_hdr_deparser_g: for i in PCIE_MFB_REGIONS - 1 downto 0 generate
        device_sel_pcie_hdr_g: if (DEVICE = "ULTRASCALE") generate
            pcie_hdr_data_int(i) <= pcie_mfb_data_arr(i)(PCIE_CQ_META_HEADER);
        else generate
            pcie_hdr_data_int(i) <= pcie_mfb_meta_arr(i)(PCIE_CQ_META_HEADER);
        end generate;

        pcie_hdr_deparser_i : entity work.PCIE_CQ_HDR_DEPARSER
            generic map (
                DEVICE => DEVICE)
            port map (
                OUT_TAG          => open,
                OUT_ADDRESS      => pcie_hdr_addr(i),
                OUT_REQ_ID       => open,
                OUT_TC           => open,
                OUT_DW_CNT       => pcie_hdr_dw_count(i),
                OUT_ATTRIBUTES   => open,
                OUT_FBE          => pcie_hdr_fbe(i),
                OUT_LBE          => pcie_hdr_lbe(i),
                OUT_ADDRESS_TYPE => open,
                OUT_TARGET_FUNC  => open,
                OUT_BAR_ID       => pcie_hdr_bar_id(i),
                OUT_BAR_APERTURE => pcie_hdr_bar_aperture(i),
                OUT_ADDR_LEN     => open,
                OUT_REQ_TYPE     => open,

                IN_HEADER     => pcie_hdr_data_int(i),
                IN_FBE        => pcie_mfb_meta_arr(i)(PCIE_CQ_META_FBE),
                IN_LBE        => pcie_mfb_meta_arr(i)(PCIE_CQ_META_LBE),

                IN_INTEL_META => std_logic_vector(to_unsigned(BAR_APERTURE_INTEL, 6)) & pcie_mfb_meta_arr(i)(PCIE_CQ_META_BAR) & (8 - 1 downto 0 => '0'));
    end generate;

    -- =============================================================================================
    -- creates mask for pcie addr based on the BAR APERTURE value in the PCIE header
    -- =============================================================================================
    addr_mask_gen_g: for i in PCIE_MFB_REGIONS - 1 downto 0 generate
        addr_mask_gen_p : process (all)
            variable mask_var : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(63  downto 0);
        begin
            mask_var(i) := (others => '0');
            for j in 0 to 63 loop
                if (j < unsigned(pcie_hdr_bar_aperture(i))) then
                    mask_var(i)(j) := '1';
                end if;
            end loop;
            pcie_addr_mask(i) <= mask_var(i);
        end process;

        pcie_addr_masked(i) <= pcie_hdr_addr(i) and pcie_addr_mask(i);
    end generate;

    -- =============================================================================================
    -- Controling split to different channels according to the current PCIe address
    -- =============================================================================================
    dma_hdr_vld_extract_g: for i in (PCIE_MFB_REGIONS - 1) downto 0 generate
        dma_hdr_vld_extract_p : process (all) is
        begin
            is_dma_hdr(i)   <= '0';

            -- NOTE: does not fully work because a different BAR ID has to drop the transaction
            if PCIE_MFB_SRC_RDY = '1' then
                if PCIE_MFB_SOF(i) = '1' then
                    -- Base address of the first DMA header buffer is always larger by one than the last
                    -- addres for a data buffer in a last channel
                    is_dma_hdr(i) <= pcie_addr_masked(i)(log2(CHANNELS) + POINTER_WIDTH + 1);
                end if;
            end if;
        end process;
    end generate;

    chan_num_extract_g: if (PCIE_MFB_REGIONS = 2) generate

        -- select only the part of the address which indexes DMA channels
        chan_num_extract_p : process (all) is
        begin
            chan_num_int <= chan_num_stored;

            if (PCIE_MFB_SRC_RDY = '1') then
                if (PCIE_MFB_SOF = "11") then
                    chan_num_int(0) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                    chan_num_int(1) <= pcie_addr_masked(1)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);

                elsif (PCIE_MFB_SOF = "01") then
                    chan_num_int(0) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                    chan_num_int(1) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);

                elsif (PCIE_MFB_SOF = "10") then
                    chan_num_int(1) <= pcie_addr_masked(1)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                end if;
            end if;
        end process;

        -- purpose: store the number of channel for the duration of the whole packet
        channel_store_reg_p: process (CLK) is
        begin
            if (rising_edge(CLK)) then
                if (PCIE_MFB_SRC_RDY = '1') then
                    if (PCIE_MFB_SOF = "11") then
                        chan_num_stored(0) <= pcie_addr_masked(1)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                        chan_num_stored(1) <= pcie_addr_masked(1)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);

                    elsif (PCIE_MFB_SOF = "01") then
                        chan_num_stored(0) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                        chan_num_stored(1) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);

                    elsif (PCIE_MFB_SOF = "10") then
                        chan_num_stored(0) <= pcie_addr_masked(1)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                        chan_num_stored(1) <= pcie_addr_masked(1)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                    end if;
                end if;
            end if;
        end process;
    else generate

        -- select only the part of the address which indexes DMA channels
        chan_num_extract_p : process (all) is
        begin
            chan_num_int <= chan_num_stored;

            if (PCIE_MFB_SRC_RDY = '1') then
                if (PCIE_MFB_SOF = "1") then
                    chan_num_int(0) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                end if;
            end if;
        end process;

        -- purpose: store the number of channel for the duration of the whole packet
        channel_store_reg_p: process (CLK) is
        begin
            if (rising_edge(CLK)) then
                if (PCIE_MFB_SRC_RDY = '1') then
                    if (PCIE_MFB_SOF = "1") then
                        chan_num_stored(0) <= pcie_addr_masked(0)(log2(CHANNELS) + POINTER_WIDTH + 1 -1 downto POINTER_WIDTH + 1);
                    end if;
                end if;
            end if;
        end process;
    end generate;

    byte_en_decoder_g: for i in PCIE_MFB_REGIONS - 1 downto 0 generate
        byte_en_decoder_i : entity work.PCIE_BYTE_EN_DECODER
            port map (
                FBE_IN  => pcie_hdr_fbe(i),
                LBE_IN  => pcie_hdr_lbe(i),
                FBE_OUT => fbe_decoded(i),
                LBE_OUT => lbe_decoded(i));

        pcie_mfb_meta_int(i) <= lbe_decoded(i) & fbe_decoded(i) & pcie_tr_byte_cnt(i) & (META_BE_W -1 downto 0 => '0') & chan_num_int(i) & pcie_addr_masked(i)(63 downto 2) & is_dma_hdr(i);
    end generate;

    -- Cutter is used only for Xilinx devices
    pcie_hdr_cutter_g: if (DEVICE="ULTRASCALE" or DEVICE="7SERIES") generate
        pcie_hdr_cutter_i : entity work.MFB_CUTTER_SIMPLE
            generic map (
                REGIONS        => PCIE_MFB_REGIONS,
                REGION_SIZE    => PCIE_MFB_REGION_SIZE,
                BLOCK_SIZE     => PCIE_MFB_BLOCK_SIZE,
                ITEM_WIDTH     => PCIE_MFB_ITEM_WIDTH,
                META_WIDTH     => META_LBE_O + META_LBE_W,
                META_ALIGNMENT => 0,
                -- 4 because the PCIe header is 4 DW long
                CUTTED_ITEMS   => 4
            )
            port map (
                CLK   => CLK,
                RESET => RESET,

                RX_DATA    => PCIE_MFB_DATA,
                RX_META    => slv_array_ser(pcie_mfb_meta_int),
                RX_SOF     => PCIE_MFB_SOF,
                RX_EOF     => PCIE_MFB_EOF,
                RX_SOF_POS => PCIE_MFB_SOF_POS,
                RX_EOF_POS => PCIE_MFB_EOF_POS,
                RX_SRC_RDY => PCIE_MFB_SRC_RDY,
                RX_DST_RDY => PCIE_MFB_DST_RDY,
                RX_CUT     => PCIE_MFB_SOF,

                TX_DATA    => cutt_mfb_data,
                TX_META    => cutt_mfb_meta,
                TX_SOF     => cutt_mfb_sof,
                TX_EOF     => cutt_mfb_eof,
                TX_SOF_POS => cutt_mfb_sof_pos,
                TX_EOF_POS => cutt_mfb_eof_pos,
                TX_SRC_RDY => cutt_mfb_src_rdy,
                TX_DST_RDY => cutt_mfb_dst_rdy);
    else generate
        -- Just connecting the signals
        cutt_mfb_data       <= PCIE_MFB_DATA;
        cutt_mfb_meta       <= slv_array_ser(pcie_mfb_meta_int);
        cutt_mfb_sof        <= PCIE_MFB_SOF;
        cutt_mfb_eof        <= PCIE_MFB_EOF;
        cutt_mfb_sof_pos    <= PCIE_MFB_SOF_POS;
        cutt_mfb_eof_pos    <= PCIE_MFB_EOF_POS;
        cutt_mfb_src_rdy    <= PCIE_MFB_SRC_RDY;
        PCIE_MFB_DST_RDY    <= cutt_mfb_dst_rdy;
    end generate;

    mfb_auxiliary_signals_i : entity work.MFB_AUXILIARY_SIGNALS
        generic map (
            REGIONS       => PCIE_MFB_REGIONS,
            REGION_SIZE   => PCIE_MFB_REGION_SIZE,
            BLOCK_SIZE    => PCIE_MFB_BLOCK_SIZE,
            ITEM_WIDTH    => PCIE_MFB_ITEM_WIDTH,
            META_WIDTH    => META_LBE_O + META_LBE_W,
            REGION_AUX_EN => FALSE,
            BLOCK_AUX_EN  => FALSE,
            ITEM_AUX_EN   => TRUE
        )
        port map (
            CLK   => CLK,
            RESET => RESET,

            RX_DATA    => cutt_mfb_data,
            RX_META    => cutt_mfb_meta,
            RX_SOF_POS => cutt_mfb_sof_pos,
            RX_EOF_POS => cutt_mfb_eof_pos,
            RX_SOF     => cutt_mfb_sof,
            RX_EOF     => cutt_mfb_eof,
            RX_SRC_RDY => cutt_mfb_src_rdy,
            RX_DST_RDY => cutt_mfb_dst_rdy,

            TX_DATA    => aux_mfb_data,
            TX_META    => aux_mfb_meta,
            TX_SOF_POS => aux_mfb_sof_pos,
            TX_EOF_POS => aux_mfb_eof_pos,
            TX_SOF     => aux_mfb_sof,
            TX_EOF     => aux_mfb_eof,
            TX_SRC_RDY => aux_mfb_src_rdy,
            TX_DST_RDY => aux_mfb_dst_rdy,

            TX_REGION_SHARED => open,
            TX_REGION_VLD    => open,
            TX_BLOCK_VLD     => open,
            TX_ITEM_VLD      => mfb_aux_item_vld_int);

    -- This quasi state machine stores the LBE value till the end of a packet
    aux_mfb_meta_arr    <= slv_array_deser(aux_mfb_meta, PCIE_MFB_REGIONS);
    lbe_reg_p: process(CLK) is
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                usr_mfb_lbe_reg <= (others => '0');
            else
                -- Higher takes
                for i in 0 to PCIE_MFB_REGIONS - 1 loop
                    if (aux_mfb_sof(i) = '1' and aux_mfb_eof(i) = '0') then
                        usr_mfb_lbe_reg <= aux_mfb_meta_arr(i)(META_LBE);
                    end if;
                end  loop;
            end if;
        end if;
    end process;

    -- Select process
    lbe_sel_p: process(all)
    begin
        if aux_mfb_sof(0) = '1' then
            usr_mfb_lbe_sel <= aux_mfb_meta_arr(0)(META_LBE);
        else
            usr_mfb_lbe_sel <= usr_mfb_lbe_reg;
        end if;
    end process;

    -- this process creates a byte enable for a whole MFB word
    mfb_aux_item_vld_int_arr    <= slv_array_deser(mfb_aux_item_vld_int, PCIE_MFB_REGIONS);
    aux_mfb_eof_pos_arr         <= slv_array_deser(aux_mfb_eof_pos, PCIE_MFB_REGIONS);
    be_fill_p : process (all) is
    begin
        -- default assignment is to simply copy the validity value of the current item
        mfb_aux_item_be <= (others => (others => (others => '0')));

        if (aux_mfb_src_rdy = '1') then
            for i in 0 to PCIE_MFB_REGIONS - 1 loop
                for j in 0 to (PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE -1) loop
                    mfb_aux_item_be(i)(j) <= (others => mfb_aux_item_vld_int_arr(i)(j));
                end loop;
            end loop;

            -- apply FBE to the BE vector
            for i in 0 to PCIE_MFB_REGIONS - 1 loop
                if (aux_mfb_sof(i) = '1') then
                    mfb_aux_item_be(i)(0) <= aux_mfb_meta_arr(i)(META_FBE);
                end if;

                -- apply LBE to the BE vector
                if (aux_mfb_eof(i) = '1' and aux_mfb_sof(i) = '0') then
                    mfb_aux_item_be(i)(to_integer(unsigned(aux_mfb_eof_pos_arr(i)))) <= usr_mfb_lbe_sel;
                elsif (aux_mfb_eof(i) = '1' and aux_mfb_sof(i) = '1' and unsigned(aux_mfb_eof_pos_arr(i)) > 0) then
                    mfb_aux_item_be(i)(to_integer(unsigned(aux_mfb_eof_pos_arr(i)))) <= aux_mfb_meta_arr(i)(META_LBE);
                end if;
            end loop;
        end if;
    end process;

    ser_usr_mfb_meta_g: for i in PCIE_MFB_REGIONS-1 downto 0 generate
        aux_mfb_meta_arr_reduced(i)(META_CHAN_NUM_W + META_CHAN_NUM_O -1 downto 0) <= aux_mfb_meta_arr(i)(META_CHAN_NUM_W + META_CHAN_NUM_O -1 downto 0);
        aux_mfb_meta_arr_reduced(i)(META_BE)                                       <= slv_array_ser(mfb_aux_item_be(i));
        aux_mfb_meta_arr_reduced(i)(META_BYTE_CNT)                                 <= aux_mfb_meta_arr(i)(META_BYTE_CNT);
    end generate;

    USR_MFB_DATA    <= aux_mfb_data;
    USR_MFB_META    <= slv_array_ser(aux_mfb_meta_arr_reduced);
    USR_MFB_SOF     <= aux_mfb_sof;
    USR_MFB_EOF     <= aux_mfb_eof;
    USR_MFB_SOF_POS <= aux_mfb_sof_pos;
    USR_MFB_EOF_POS <= aux_mfb_eof_pos;
    USR_MFB_SRC_RDY <= aux_mfb_src_rdy;
    aux_mfb_dst_rdy <= USR_MFB_DST_RDY;
end architecture;
