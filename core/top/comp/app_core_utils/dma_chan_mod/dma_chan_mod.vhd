-- dma_chan_mod.vhd:
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity APP_DMA_CHAN_MOD is
generic (
    -- MFB parameters
    MFB_REGIONS     : natural := 1;
    -- Number of channels for one DMA Stream
    DMA_RX_CHANNELS : natural := 16;
    DMA_TX_CHANNELS : natural := 16;
    -- Divider of DMA channels, typically:
    -- the number of APP streams per one DMA stream
    DIVIDER         : natural := 2;
    -- ID number of this instance
    STREAM_ID       : natural := 0;
    -- Enable channel modifications
    ENABLE_MOD      : boolean := False
);
port (
    APP_RX_MVB_CHANNEL : in  std_logic_vector(MFB_REGIONS*log2(DMA_RX_CHANNELS/DIVIDER)-1 downto 0);
    DMA_RX_MVB_CHANNEL : out std_logic_vector(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);

    APP_TX_MVB_CHANNEL : out std_logic_vector(MFB_REGIONS*log2(DMA_TX_CHANNELS/DIVIDER)-1 downto 0);
    DMA_TX_MVB_CHANNEL : in  std_logic_vector(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0)
);
end entity;

architecture FULL of APP_DMA_CHAN_MOD is

    signal app_rx_chan_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(DMA_RX_CHANNELS/DIVIDER)-1 downto 0);
    signal dma_rx_chan_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(DMA_RX_CHANNELS)-1 downto 0);
    signal app_tx_chan_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(DMA_TX_CHANNELS/DIVIDER)-1 downto 0);
    signal dma_tx_chan_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(DMA_TX_CHANNELS)-1 downto 0);

begin

    mod_g: if (ENABLE_MOD and (DIVIDER > 1)) generate
        app_rx_chan_arr <= slv_array_deser(APP_RX_MVB_CHANNEL,MFB_REGIONS);
        dma_tx_chan_arr <= slv_array_deser(DMA_TX_MVB_CHANNEL,MFB_REGIONS);
        chan_mod_g: for i in 0 to MFB_REGIONS-1 generate
            dma_rx_chan_arr(i) <= std_logic_vector(to_unsigned(STREAM_ID,log2(DIVIDER))) & app_rx_chan_arr(i);
            app_tx_chan_arr(i) <= dma_tx_chan_arr(i)(log2(DMA_TX_CHANNELS/DIVIDER)-1 downto 0);
        end generate;
        DMA_RX_MVB_CHANNEL <= slv_array_ser(dma_rx_chan_arr);
        APP_TX_MVB_CHANNEL <= slv_array_ser(app_tx_chan_arr);
    else generate
        DMA_RX_MVB_CHANNEL <= APP_RX_MVB_CHANNEL;
        APP_TX_MVB_CHANNEL <= DMA_TX_MVB_CHANNEL;
    end generate;

end architecture;
