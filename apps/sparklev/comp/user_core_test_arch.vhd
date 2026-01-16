-- user_core_test_arch.vhd: Testing architecture of the user core
-- Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
--
-- SPDX-License-Identifier: CERN-OHL-P-2.0

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

library unisim;
use unisim.vcomponents.BUFG;

architecture TEST of USER_CORE is
    signal hbm_rst_bufg : std_logic;
    signal c2h_dma_mfb_data_int : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto 0);
    signal c2h_dma_mfb_meta_int : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_HDR_META_WIDTH+log2(maximum(C2H_DMA_CHANNELS, H2C_DMA_CHANNELS)) -1 downto 0);
    constant CNTR_WIDTH : natural := 64;
    signal cntr : u_array_t(DMA_STREAMS -1 downto 0)(CNTR_WIDTH -1  downto 0);    
begin
    -- =============================================================================================
    -- Loopback of DMA data adding a counter into user data
    -- =============================================================================================
    dma_str_g: for stream in 0 to (DMA_STREAMS-1) generate
        dma_mfb_pipe_i : entity work.MFB_PIPE
            generic map (
                REGIONS     => DMA_MFB_REGIONS,
                REGION_SIZE => DMA_MFB_REGION_SIZE,
                BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,
                META_WIDTH  => DMA_HDR_META_WIDTH + log2(maximum(C2H_DMA_CHANNELS, H2C_DMA_CHANNELS)),

                FAKE_PIPE   => false,
                USE_DST_RDY => true,
                PIPE_TYPE   => "REG",
                DEVICE      => DEVICE)
            port map (
                CLK        => DMA_CLK(stream),
                RESET      => DMA_RST(stream),

                RX_DATA    => H2C_DMA_MFB_DATA(stream),
                RX_META    => H2C_DMA_MFB_META_HDR_META(stream) & H2C_DMA_MFB_META_CHAN(stream),
                RX_SOF_POS => H2C_DMA_MFB_SOF_POS(stream),
                RX_EOF_POS => H2C_DMA_MFB_EOF_POS(stream),
                RX_SOF     => H2C_DMA_MFB_SOF(stream),
                RX_EOF     => H2C_DMA_MFB_EOF(stream),
                RX_SRC_RDY => H2C_DMA_MFB_SRC_RDY(stream),
                RX_DST_RDY => H2C_DMA_MFB_DST_RDY(stream),

                TX_DATA    => c2h_dma_mfb_data_int(stream),
                TX_META    => c2h_dma_mfb_meta_int(stream),
                TX_SOF_POS => C2H_DMA_MFB_SOF_POS(stream),
                TX_EOF_POS => C2H_DMA_MFB_EOF_POS(stream),
                TX_SOF     => C2H_DMA_MFB_SOF(stream),
                TX_EOF     => C2H_DMA_MFB_EOF(stream),
                TX_SRC_RDY => C2H_DMA_MFB_SRC_RDY(stream),
                TX_DST_RDY => C2H_DMA_MFB_DST_RDY(stream));

        cntr_i: process (DMA_CLK(stream)) is
        begin
            if (rising_edge(DMA_CLK(stream))) then
                if (DMA_RST(stream) = '1') then
                    cntr(stream) <= (others => '0');                                
                else
                    if (C2H_DMA_MFB_SRC_RDY(stream) = '1' and C2H_DMA_MFB_DST_RDY(stream) = '1') then
                        cntr(stream) <= cntr(stream) + 1;

                        C2H_DMA_MFB_DATA(stream)(CNTR_WIDTH-1 downto 0) <= std_logic_vector(cntr(stream));
                        C2H_DMA_MFB_DATA(stream)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto CNTR_WIDTH)
                            <= c2h_dma_mfb_data_int(stream)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto CNTR_WIDTH);
                    else
                        C2H_DMA_MFB_DATA(stream) <= c2h_dma_mfb_data_int(stream);                        
                    end if;
                end if;
            end if;
        end process;

        C2H_DMA_MFB_META_HDR_META(stream) <= c2h_dma_mfb_meta_int(stream)(DMA_HDR_META_WIDTH + log2(maximum(C2H_DMA_CHANNELS, H2C_DMA_CHANNELS)) -1 downto log2(maximum(C2H_DMA_CHANNELS, H2C_DMA_CHANNELS)));
        C2H_DMA_MFB_META_CHAN(stream)     <= c2h_dma_mfb_meta_int(stream)(log2(C2H_DMA_CHANNELS) -1 downto 0);
    end generate;

    -- =============================================================================================
    -- HBM memory tester
    -- =============================================================================================
    HBM_AXI_CLK   <= (others => USR_CLK);

    sysclk_bufg_i : BUFG
    port map (
        I => not USR_RST,
        O => hbm_rst_bufg
    );
    HBM_AXI_RESET <= (others => hbm_rst_bufg);

    hbm_tester_i : entity work.HBM_TESTER
    generic map (
        DEBUG           => True,

        PORTS           => HBM_PORTS,
        CNT_WIDTH       => 24,

        AXI_ADDR_WIDTH  => HBM_ADDR_WIDTH,
        AXI_DATA_WIDTH  => HBM_DATA_WIDTH,
        AXI_BURST_WIDTH => HBM_BURST_WIDTH,
        AXI_ID_WIDTH    => HBM_ID_WIDTH,
        AXI_LEN_WIDTH   => HBM_LEN_WIDTH,
        AXI_SIZE_WIDTH  => HBM_SIZE_WIDTH,
        AXI_RESP_WIDTH  => HBM_RESP_WIDTH,
        USR_DATA_WIDTH  => HBM_DATA_WIDTH,
        -- HBM address bits:
        --     - Stack Select:            33
        --     - Destination AXI Port: 32:29
        --     - HBM Address Bits      28:5
        --     - Unused Address Bits    4:0
        PORT_ADDR_HBIT  => 28,
        DEVICE          => DEVICE
    )
    port map (
        HBM_CLK             => USR_CLK,
        HBM_RESET           => hbm_rst_bufg,

        MI_CLK              => MI_CLK,
        MI_RESET            => MI_RST,
        MI_DWR              => MI_DWR,
        MI_ADDR             => MI_ADDR,
        MI_BE               => MI_BE,
        MI_RD               => MI_RD,
        MI_WR               => MI_WR,
        MI_ARDY             => MI_ARDY,
        MI_DRD              => MI_DRD,
        MI_DRDY             => MI_DRDY,

        WR_ADDR             => (others => (others => '0')),
        WR_DATA             => (others => (others => '0')),
        WR_DATA_LAST        => (others => '0'),
        WR_VALID            => (others => '0'),
        WR_READY            => open,
        WR_RSP_ACK          => open,
        WR_RSP_VALID        => open,
        WR_RSP_READY        => (others => '1'),
        RD_ADDR             => (others => (others => '0')),
        RD_ADDR_VALID       => (others => '0'),
        RD_ADDR_READY       => open,
        RD_DATA             => open,
        RD_DATA_LAST        => open,
        RD_DATA_VALID       => open,
        RD_DATA_READY       => (others => '1'),

        AXI_AWID            => HBM_AXI_AWID,
        AXI_AWADDR          => HBM_AXI_AWADDR,
        AXI_AWLEN           => HBM_AXI_AWLEN,
        AXI_AWSIZE          => HBM_AXI_AWSIZE,
        AXI_AWBURST         => HBM_AXI_AWBURST,
        AXI_AWPROT          => open,
        AXI_AWQOS           => open,
        AXI_AWUSER          => open,
        AXI_AWVALID         => HBM_AXI_AWVALID,
        AXI_AWREADY         => HBM_AXI_AWREADY,
        AXI_WDATA           => HBM_AXI_WDATA,
        AXI_WSTRB           => HBM_AXI_WSTRB,
        AXI_WUSER_DATA      => HBM_AXI_WDATA_PARITY,
        AXI_WUSER_STRB      => open,
        AXI_WLAST           => HBM_AXI_WLAST,
        AXI_WVALID          => HBM_AXI_WVALID,
        AXI_WREADY          => HBM_AXI_WREADY,
        AXI_BID             => HBM_AXI_BID,
        AXI_BRESP           => HBM_AXI_BRESP,
        AXI_BVALID          => HBM_AXI_BVALID,
        AXI_BREADY          => HBM_AXI_BREADY,
        AXI_ARID            => HBM_AXI_ARID,
        AXI_ARADDR          => HBM_AXI_ARADDR,
        AXI_ARLEN           => HBM_AXI_ARLEN,
        AXI_ARSIZE          => HBM_AXI_ARSIZE,
        AXI_ARBURST         => HBM_AXI_ARBURST,
        AXI_ARPROT          => open,
        AXI_ARQOS           => open,
        AXI_ARUSER          => open,
        AXI_ARVALID         => HBM_AXI_ARVALID,
        AXI_ARREADY         => HBM_AXI_ARREADY,
        AXI_RID             => HBM_AXI_RID,
        AXI_RDATA           => HBM_AXI_RDATA,
        AXI_RUSER_DATA      => HBM_AXI_RDATA_PARITY,
        AXI_RUSER_ERR_DBE   => (others => '0'),
        AXI_RRESP           => HBM_AXI_RRESP,
        AXI_RLAST           => HBM_AXI_RLAST,
        AXI_RVALID          => HBM_AXI_RVALID,
        AXI_RREADY          => HBM_AXI_RREADY
    );
end architecture;
