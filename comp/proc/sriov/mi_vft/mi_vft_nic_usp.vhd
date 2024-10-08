-- mi_vft.vhd: MI Virtual Function Translator
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Martin Spinler
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;

architecture mi_vft_arch of MI_VFT is

    constant DMA_CTRL_SPACE         : integer := log2(tsel(DMA_TYPE = 3, 128, 64));
    constant MAX_DMA_CHANNELS       : integer := tsel(DMA_TYPE = 3, 16384, 32768);
    -- First VF will have this number in signal in_function
    constant VF0_ID_OFFSET          : integer := 4;
    constant VF0_DMA_RX_OFFSET      : integer := DMA_RX_CHANNELS - (PF0_VFS * VF0_DMA_RX_CHANNELS);
    constant VF0_DMA_TX_OFFSET      : integer := DMA_TX_CHANNELS - (PF0_VFS * VF0_DMA_TX_CHANNELS);

    signal vf_dma_channel           : std_logic_vector(log2(MAX_DMA_CHANNELS)-1 downto 0);
    signal is_dma_tx_space          : std_logic;
    signal is_vf_dma_space          : std_logic;
    signal is_vf_dma_control_reg    : std_logic;

    signal in_fn                    : integer;

    signal in_function              : std_logic_vector(7 downto 0); -- TODO

begin

    in_function <= IN_MWR(7 downto 0); -- TODO

    vf_g: if PF0_VFS > 0 generate
        assert VF0_DMA_RX_CHANNELS = VF0_DMA_TX_CHANNELS and DMA_RX_CHANNELS = DMA_TX_CHANNELS
                report "Non-symmetric DMA channel count when Virtual function enabled in MI_VFT!" severity error;

        in_fn                       <= to_integer(ieee.numeric_std.unsigned(IN_FUNCTION));
        is_vf_dma_control_reg       <= '1' when IN_ADDR(5 downto 2) = X"0" and DMA_TYPE = 0 else '0';

        -- TODO
        is_dma_tx_space             <= '0';
        -- TODO
        is_vf_dma_space             <= '1'; -- when IN_ADDR(31 downto 23) = X"01" & "0";
                                    --(IN_ADDR = X"01400000" or IN_ADDR = X"01600000") else '0';

        vf_dma_channel  <= std_logic_vector(to_unsigned(in_fn - VF0_ID_OFFSET + VF0_DMA_TX_OFFSET, log2(MAX_DMA_CHANNELS))) when is_dma_tx_space = '1' else
                           std_logic_vector(to_unsigned(in_fn - VF0_ID_OFFSET + VF0_DMA_RX_OFFSET, log2(MAX_DMA_CHANNELS)));

        -- VF BAR is smaller than PF BAR, so we need keep MI space usage low.
        OUT_ADDR        <= IN_ADDR when in_fn = 0 else
                           X"01" & "00" & IN_ADDR(12) & (20 downto log2(MAX_DMA_CHANNELS)+DMA_CTRL_SPACE => '0') & vf_dma_channel & IN_ADDR(DMA_CTRL_SPACE-1 downto 0);

        -- Add VFID to the highest byte of the Control register in the DMA controller
        OUT_DWR         <= IN_FUNCTION & IN_DWR(23 downto 0) when in_fn /= 0 and is_vf_dma_control_reg = '1' and is_vf_dma_space = '1' else
                           IN_DWR;
    else generate
        OUT_ADDR        <= IN_ADDR;
        OUT_DWR         <= IN_DWR;
    end generate;


    OUT_BE          <= IN_BE;
    OUT_WR          <= IN_WR;
    OUT_RD          <= IN_RD;
    OUT_MWR         <= IN_MWR;

    IN_DRD          <= OUT_DRD;
    IN_DRDY         <= OUT_DRDY;
    IN_ARDY         <= OUT_ARDY;

end mi_vft_arch;
