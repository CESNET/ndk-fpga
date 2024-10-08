-- fp_bs_per_packet.vhd: Barrel Shifters for Frame Packer
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The purpose of this component is to encapsulate all BarrelShifters and extract its data
entity FP_BS_PER_PACKET is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;
        RX_PKT_SIZE_MAX     : natural := 2**10
    );
    port(
        CLK : in std_logic;
        -- Input data [DATA] [VLD] [SOF_OH] [EOF_OH] [PKT_LNG]
        RX_DATA         : in slv_array_t(MFB_REGIONS downto 0)((MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);
        -- Rotation of data
        RX_SEL          : in slv_array_t(MFB_REGIONS downto 0)(max(1, log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);

        -- TX interface
        TX_DATA         : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Valid per packet
        TX_BLOCK_VLD    : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- SOF_POS in ONE HOT format
        TX_SOF_ONE_HOT  : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- EOF_POS in ONE HOT format
        TX_EOF_ONE_HOT  : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        -- Packet Length
        TX_PKT_LNG      : out slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1))- 1 downto 0)
    );
end entity;

architecture FULL of FP_BS_PER_PACKET is
    ------------------------------------------------------------
    --                  CONSTANT DECLARATION                  --
    ------------------------------------------------------------
    constant RX_DATA_H      : natural:= MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 + 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1;
    constant RX_VLD_H       : natural:= 1 + 1 + 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1;
    constant RX_SOH_H       : natural:= 1 + 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1;
    constant RX_EOH_H       : natural:= 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1;
    constant RX_PKT_LNG_H   : natural:= max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1;
    ------------------------------------------------------------
    --                  SIGNAL DECLARATION                    --
    ------------------------------------------------------------
    -- Output of BSs
    signal bs_data_out          : slv_array_t(MFB_REGIONS downto 0)((MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);
    signal bs_data_out_arr      : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 + 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

    -- Data extraction
    signal bs_data_arr          : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(MFB_BLOCK_SIZE*MFB_ITEM_WIDTH - 1 downto 0);
    signal bs_vld_arr           : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(1 - 1 downto 0);
    signal bs_soh_arr           : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(1 - 1 downto 0);
    signal bs_eoh_arr           : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(1 - 1 downto 0);
    signal bs_pkt_vld_arr       : slv_array_2d_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

    -- Pre-register signals
    signal tx_data_s            : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal tx_block_vld_s       : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tx_sof_one_hot_s     : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tx_eof_one_hot_s     : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal tx_pkt_lng_s         : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

begin
    -- Barrel Shifters per packet
    bs_g: for i in 0 to MFB_REGIONS generate
        barrel_shifter_i: entity work.BARREL_SHIFTER_GEN
            generic map(
                BLOCKS      => MFB_REGIONS*MFB_REGION_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE*MFB_ITEM_WIDTH + 1 + 1 + 1 + max(1, log2(RX_PKT_SIZE_MAX + 1)),
                SHIFT_LEFT  => false
            )
            port map(
                DATA_IN     => RX_DATA(i),
                DATA_OUT    => bs_data_out(i),
                SEL         => RX_SEL(i)
        );
    end generate;

    -- Data extraction
    bs_block_extraction_g: for i in 0 to MFB_REGIONS generate
        bs_data_out_arr(i)  <=  slv_array_deser(bs_data_out(i), MFB_REGIONS*MFB_REGION_SIZE);
    end generate;

    extraction_per_bs_g: for i in 0 to MFB_REGIONS generate
        extraction_per_block_g: for j in 0 to MFB_REGIONS*MFB_REGION_SIZE - 1 generate
            bs_data_arr(i)(j)       <= bs_data_out_arr(i)(j)(RX_DATA_H    downto RX_VLD_H + 1);
            bs_vld_arr(i)(j)        <= bs_data_out_arr(i)(j)(RX_VLD_H     downto RX_SOH_H + 1);
            bs_soh_arr(i)(j)        <= bs_data_out_arr(i)(j)(RX_SOH_H     downto RX_EOH_H + 1);
            bs_eoh_arr(i)(j)        <= bs_data_out_arr(i)(j)(RX_EOH_H     downto RX_PKT_LNG_H + 1);
            bs_pkt_vld_arr(i)(j)    <= bs_data_out_arr(i)(j)(RX_PKT_LNG_H downto 0);
        end generate;
    end generate;

    data_out_g: for i in 0 to MFB_REGIONS generate
        tx_data_s(i)          <= slv_array_ser(bs_data_arr(i));
        tx_block_vld_s(i)     <= slv_array_ser(bs_vld_arr(i));
        tx_sof_one_hot_s(i)   <= slv_array_ser(bs_soh_arr(i));
        tx_eof_one_hot_s(i)   <= slv_array_ser(bs_eoh_arr(i));
        tx_pkt_lng_s(i)       <= slv_array_ser(bs_pkt_vld_arr(i));
    end generate;

    -- This register is necessary - helps with pointer synchronization
    out_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            TX_DATA         <= tx_data_s;
            TX_BLOCK_VLD    <= tx_block_vld_s;
            TX_SOF_ONE_HOT  <= tx_sof_one_hot_s;
            TX_EOF_ONE_HOT  <= tx_eof_one_hot_s;
            TX_PKT_LNG      <= tx_pkt_lng_s;
        end if;
    end process;

end architecture;
