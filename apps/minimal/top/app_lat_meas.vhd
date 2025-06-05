-- app_core_empty_arch.vhd: Empty architecture of the application core
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture EMPTY of APPLICATION_CORE is
    function lm_mi_addr_base_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(DMA_STREAMS-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    begin
        for i in 0 to DMA_STREAMS-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*x"30", MI_ADDR_WIDTH));
        end loop;
        return mi_addr_base_var;
    end function;
begin

    MI_CLK     <= CLK_USER;
    DMA_CLK    <= CLK_USER_X2;
    DMA_CLK_X2 <= CLK_USER_X4;
    APP_CLK    <= CLK_USER_X2;

    MI_RESET     <= RESET_USER;
    DMA_RESET    <= RESET_USER_X2;
    DMA_RESET_X2 <= RESET_USER_X4;
    APP_RESET    <= RESET_USER_X2;

    ETH_RX_MVB_DST_RDY <= (others => '1');
    ETH_RX_MFB_DST_RDY <= (others => '1');

    ETH_TX_MFB_DATA    <= (others => '0');
    ETH_TX_MFB_HDR     <= (others => '0');
    ETH_TX_MFB_SOF     <= (others => '0');
    ETH_TX_MFB_EOF     <= (others => '0');
    ETH_TX_MFB_SOF_POS <= (others => '0');
    ETH_TX_MFB_EOF_POS <= (others => '0');
    ETH_TX_MFB_SRC_RDY <= (others => '0');

    DMA_RX_MVB_LEN      <= (others => '0');
    DMA_RX_MVB_HDR_META <= (others => '0');
    DMA_RX_MVB_CHANNEL  <= (others => '0');
    DMA_RX_MVB_DISCARD  <= (others => '0');
    DMA_RX_MVB_VLD      <= (others => '0');
    DMA_RX_MVB_SRC_RDY  <= (others => '0');

    DMA_RX_MFB_DATA    <= (others => '0');
    DMA_RX_MFB_SOF     <= (others => '0');
    DMA_RX_MFB_EOF     <= (others => '0');
    DMA_RX_MFB_SOF_POS <= (others => '0');
    DMA_RX_MFB_EOF_POS <= (others => '0');
    DMA_RX_MFB_SRC_RDY <= (others => '0');

    DMA_TX_MVB_DST_RDY <= (others => '1');
    DMA_TX_MFB_DST_RDY <= (others => '1');

    MEM_AVMM_READ       <= (others => '0');
    MEM_AVMM_WRITE      <= (others => '0');
    MEM_AVMM_ADDRESS    <= (others => (others => '0'));
    MEM_AVMM_BURSTCOUNT <= (others => (others => '0'));
    MEM_AVMM_WRITEDATA  <= (others => (others => '0'));

    MEM_REFR_PERIOD <= (others => (others => '0'));
    MEM_REFR_REQ    <= (others => '0');

    EMIF_RST_REQ        <= (others => '0');
    EMIF_AUTO_PRECHARGE <= (others => '0');

    lm_mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map (
            ADDR_WIDTH   => MI_ADDR_WIDTH,
            DATA_WIDTH   => MI_DATA_WIDTH,
            META_WIDTH   => 0,

            PORTS        => DMA_STREAMS,
            PIPE_OUT     => (others => true),
            PIPE_TYPE    => "REG",
            PIPE_OUTREG  => false,
            ADDR_BASES   => DMA_STREAMS,
            ADDR_BASE    => lm_mi_addr_base_f,
            DEVICE       => DEVICE)
        port map (
            CLK     => MI_CLK,
            RESET   => MI_RESET(0),

            RX_DWR  => MI_DWR,
            RX_MWR  => (others => '0'),
            RX_ADDR => MI_ADDR,
            RX_BE   => MI_BE,
            RX_RD   => MI_RD,
            RX_WR   => MI_WR,
            RX_ARDY => MI_ARDY,
            RX_DRD  => MI_DRD,
            RX_DRDY => MI_DRDY,

            TX_DWR  => LM_MI_DWR,
            TX_MWR  => open,
            TX_ADDR => LM_MI_ADDR,
            TX_BE   => LM_MI_BE,
            TX_RD   => LM_MI_RD,
            TX_WR   => LM_MI_WR,
            TX_ARDY => LM_MI_ARDY,
            TX_DRD  => LM_MI_DRD,
            TX_DRDY => LM_MI_DRDY);
end architecture;
