-- metadata_insertor.vhd: DUT Wrapper
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

entity DUT_WRAPPER is
    generic(
        ITEMS         : natural := 4;
        ITEM_WIDTH    : natural := 32;
        SRC_CHANNELS  : natural := 4;  -- max value = DST_CHANNELS
        DST_CHANNELS  : natural := 16; -- max value = 256
        MI_DATA_WIDTH : natural := 32; -- min value = 32
        MI_ADDR_WIDTH : natural := 32;
        DEVICE        : string  := "ULTRASCALE"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;

        -- =====================================================================
        -- MI INTERFACE
        -- =====================================================================
        MI_DWR     : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ADDR    : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        MI_BE      : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0); -- Not supported!
        MI_RD      : in  std_logic;
        MI_WR      : in  std_logic;
        MI_ARDY    : out std_logic;
        MI_DRD     : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_DRDY    : out std_logic;

        -- =====================================================================
        --  INPUT MVB INTERFACE
        -- =====================================================================
        RX_DATA    : in  std_logic_vector(ITEMS*(ITEM_WIDTH+log2(SRC_CHANNELS))-1 downto 0);
        --RX_CHANNEL : in  std_logic_vector(ITEMS*log2(SRC_CHANNELS)-1 downto 0);
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- =====================================================================
        --  OUTPUT MVB INTERFACE
        -- =====================================================================
        TX_DATA    : out std_logic_vector(ITEMS*(ITEM_WIDTH+log2(DST_CHANNELS))-1 downto 0);
        --TX_CHANNEL : in  std_logic_vector(ITEMS*log2(DST_CHANNELS)-1 downto 0);
        TX_VLD     : out std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic

        ---------------------------------------------------------------------------
    );
end entity;

architecture FULL of DUT_WRAPPER is

    constant NEW_DATA_WIDTH   : natural := ITEM_WIDTH+log2(DST_CHANNELS);

    signal rx_data_all_arr : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH+log2(SRC_CHANNELS)-1 downto 0);
    signal rx_data_arr     : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal rx_channel_arr  : slv_array_t(ITEMS-1 downto 0)(log2(SRC_CHANNELS)-1 downto 0);

    signal mvb_data_arr_deser : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal mvb_ch_arr_deser   : slv_array_t(ITEMS-1 downto 0)(log2(DST_CHANNELS)-1 downto 0);
    signal mvb_new_data_arr   : slv_array_t(ITEMS-1 downto 0)(NEW_DATA_WIDTH-1 downto 0);
    signal mvb_new_data_ser   : std_logic_vector(ITEMS*NEW_DATA_WIDTH-1 downto 0);

    signal mvb_data           : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal mvb_tx_ch          : std_logic_vector(ITEMS*log2(DST_CHANNELS)-1 downto 0);

begin

    rx_data_all_arr <= slv_array_deser(RX_DATA,ITEMS,ITEM_WIDTH+log2(SRC_CHANNELS));
    rx_unpack_g : for i in 0 to ITEMS-1 generate
        rx_channel_arr(i) <= rx_data_all_arr(i)(log2(SRC_CHANNELS)-1 downto 0);
        rx_data_arr(i) <= rx_data_all_arr(i)(ITEM_WIDTH+log2(SRC_CHANNELS)-1 downto log2(SRC_CHANNELS));
    end generate;

    mvb_ch_arr_deser <= slv_array_deser(mvb_tx_ch,ITEMS,log2(DST_CHANNELS));
    mvb_data_arr_deser <= slv_array_deser(mvb_data,ITEMS,ITEM_WIDTH);

    data_g : for i in 0 to ITEMS-1 generate
        mvb_new_data_arr(i) <= mvb_ch_arr_deser(i) & mvb_data_arr_deser(i);
    end generate;

    mvb_new_data_ser <= slv_array_ser(mvb_new_data_arr,ITEMS,NEW_DATA_WIDTH);
    TX_DATA <= mvb_new_data_ser;

    dut_i : entity work.MVB_CHANNEL_ROUTER_MI
    generic map(
        ITEMS          => ITEMS,
        ITEM_WIDTH     => ITEM_WIDTH,
        SRC_CHANNELS   => SRC_CHANNELS,
        DST_CHANNELS   => DST_CHANNELS,
        MI_DATA_WIDTH  => MI_DATA_WIDTH,
        MI_ADDR_WIDTH  => MI_ADDR_WIDTH,

        DEVICE  => DEVICE    )
    port map(
        CLK         => CLK,
        RESET       => RESET,

        MI_DWR      => MI_DWR,
        MI_ADDR     => MI_ADDR,
        MI_BE       => MI_BE,
        MI_RD       => MI_RD,
        MI_WR       => MI_WR,
        MI_ARDY     => MI_ARDY,
        MI_DRD      => MI_DRD,
        MI_DRDY     => MI_DRDY,

        RX_DATA     => slv_array_ser(rx_data_arr,ITEMS,ITEM_WIDTH),
        RX_CHANNEL  => slv_array_ser(rx_channel_arr,ITEMS,log2(SRC_CHANNELS)),
        RX_VLD      => RX_VLD,
        RX_SRC_RDY  => RX_SRC_RDY,
        RX_DST_RDY  => RX_DST_RDY,

        TX_DATA     => mvb_data,
        TX_CHANNEL  => mvb_tx_ch,
        TX_VLD      => TX_VLD,
        TX_SRC_RDY  => TX_SRC_RDY,
        TX_DST_RDY  => TX_DST_RDY
    );

end architecture;
