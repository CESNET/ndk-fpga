-- fp_meta_concatenate.vhd: Unit for concatenating MFB data with frame_packer metadata
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The purpose of this component is to concatenate VLD, SOF_OH, EOF_OH and PKT_LNG with MFB data
entity FP_META_CONCATENATE is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;
        RX_PKT_SIZE_MAX     : natural := 2**14
    );
    port(
        -- RX MFB interface
        RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Valid per packet
        RX_BLOCK_VLD    : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- SOF_POS in ONE HOT format
        RX_SOF_ONE_HOT  : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- EOF_POS in ONE HOT format
        RX_EOF_ONE_HOT  : in  slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- Packet length valid with SOF
        RX_PKT_LNG      : in  slv_array_t(MFB_REGIONS downto 0)(max(1, log2(RX_PKT_SIZE_MAX + 1))- 1 downto 0);
        -- TX MFB interface [DATA] [VLD] [SOF_OH] [EOF_OH] [PKT_LNG]
        TX_DATA_CONC    : out slv_array_t(MFB_REGIONS downto 0)((MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0)
    );
end entity;

architecture FULL of FP_META_CONCATENATE is
    signal mfb_data_arr                 : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH - 1 downto 0);

    signal data_arr_per_bs              : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH - 1 downto 0);
    signal vld_arr_per_bs               : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 - 1 downto 0);
    signal sof_oh_arr_per_bs            : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 - 1 downto 0);
    signal eof_oh_arr_per_bs            : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 + 1 - 1 downto 0);
    signal pkt_lng_arr_per_bs           : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 + 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

    signal data_vld_arr_per_bs          : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 - 1 downto 0);
    signal data_vld_sof_oh_arr_per_bs   : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 - 1 downto 0);
    signal data_vld_eof_oh_arr_per_bs   : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 + 1 - 1 downto 0);

begin

    -- Deserialize input word
    mfb_data_arr    <= slv_array_deser(RX_MFB_DATA, MFB_REGIONS*MFB_REGION_SIZE);

    -- Copy data array acros multiple fields
    mfb_per_bs_g: for i in 0 to MFB_REGIONS generate
        data_arr_per_bs(i) <=   mfb_data_arr;
    end generate;

    -- Copy valid array acros multiple fields
    vld_per_bs_g: for i in 0 to MFB_REGIONS generate
        vld_per_block_g: for j in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
            vld_arr_per_bs(i)(j)  <= data_arr_per_bs(i)(j) & RX_BLOCK_VLD(i)(j);
        end generate;
    end generate;

    -- Copy One_hot eof array acros multiple fields
    sof_oh_per_bs_g: for i in 0 to MFB_REGIONS generate
        sof_oh_per_block_g: for j in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
            sof_oh_arr_per_bs(i)(j)    <= vld_arr_per_bs(i)(j) & RX_SOF_ONE_HOT(i)(j);
        end generate;
    end generate;

    -- Copy One_hot eof array acros multiple fields
    eof_oh_per_bs_g: for i in 0 to MFB_REGIONS generate
        eof_oh_per_block_g: for j in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
            eof_oh_arr_per_bs(i)(j)    <= sof_oh_arr_per_bs(i)(j) & RX_EOF_ONE_HOT(i)(j);
        end generate;
    end generate;

    -- Copy Packet_length array acros multiple fields
    pkt_lng_per_bs_g: for i in 0 to MFB_REGIONS generate
        pkt_lng_per_block_g: for j in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
            pkt_lng_arr_per_bs(i)(j)    <= eof_oh_arr_per_bs(i)(j) & RX_PKT_LNG(i);
        end generate;
    end generate;

    -- Copy data across BS
    tx_data_per_bs_g: for i in 0 to MFB_REGIONS generate
        TX_DATA_CONC(i)    <= slv_array_ser(pkt_lng_arr_per_bs(i));
    end generate;

end architecture;
