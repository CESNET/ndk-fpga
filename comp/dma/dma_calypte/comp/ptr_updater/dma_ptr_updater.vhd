-- dma_ptr_updater.vhd: observes the amount of written bytes to the transaction buffer and
-- dispatches HHP and HDP update towards host if specific threshold has been crossed
-- Copyright (C) 2025 MAGMIO, a.s.
-- Author(s): Vladislav Válek  <vladislawalek@gmail.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- Note:

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

entity DMA_PTR_UPDATER is
    generic (
        DEVICE : string := "ULTRASCALE";

        MFB_REGIONS     : positive := 2;
        MFB_REGION_SIZE : positive := 1;
        MFB_BLOCK_SIZE  : positive := 8;
        MFB_ITEM_WIDTH  : positive := 32;

        RX_CHANNELS  : positive := 4;
        RX_PTR_WIDTH : positive := 16;

        TX_CHANNELS       : positive := 4;
        TX_DATA_PTR_WIDTH : positive := 13;
        TX_HDR_PTR_WIDTH  : positive := 10;
        TX_UPD_THRESHOLD  : positive := 2**12
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- Interface to create update when a RX channel gets stopped
        -- =========================================================================================
        RX_STOP_REQ_BUFF_BA : in  std_logic_vector(64 -1 downto 0);
        RX_STOP_REQ_P2P_EN  : in  std_logic;
        RX_STOP_REQ_HDP     : in  std_logic_vector(RX_PTR_WIDTH -1 downto 0);
        RX_STOP_REQ_HHP     : in  std_logic_vector(RX_PTR_WIDTH -1 downto 0);
        RX_STOP_REQ_EN      : in  std_logic;
        RX_STOP_REQ_ACK     : out std_logic;

        -- =========================================================================================
        -- Runtime TX update interface
        -- =========================================================================================
        -- Retrieving parameters for runtime updates
        TX_RT_UPD_CH      : out std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
        TX_RT_UPD_BUFF_BA : in  std_logic_vector(64 -1 downto 0);
        TX_RT_UPD_P2P_EN  : in  std_logic;

        -- Update from Packet dispatcher
        TX_PKT_DISP_CH  : in std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
        TX_PKT_DISP_HDP : in std_logic_vector(TX_DATA_PTR_WIDTH -1 downto 0);
        TX_PKT_DISP_HHP : in std_logic_vector(TX_HDR_PTR_WIDTH -1 downto 0);
        TX_PKT_DISP_EN  : in std_logic;

        -- =========================================================================================
        -- Start request from Software manager
        -- =========================================================================================
        TX_START_REQ_CH  : in  std_logic_vector(log2(TX_CHANNELS)-1 downto 0);
        TX_START_REQ_VLD : in  std_logic;
        TX_START_REQ_ACK : out std_logic;

        -- =========================================================================================
        -- Interface to create update when a TX channel gets stopped
        -- =========================================================================================
        TX_STOP_REQ_BUFF_BA : in  std_logic_vector(64 -1 downto 0);
        TX_STOP_REQ_P2P_EN  : in  std_logic;
        TX_STOP_REQ_HDP     : in  std_logic_vector(TX_DATA_PTR_WIDTH -1 downto 0);
        TX_STOP_REQ_HHP     : in  std_logic_vector(TX_HDR_PTR_WIDTH -1 downto 0);
        TX_STOP_REQ_EN      : in  std_logic;
        TX_STOP_REQ_ACK     : out std_logic;

        -- =========================================================================================
        -- PCIe interface to dispatch pointer update within the PCIe transaction
        -- =========================================================================================
        PCIE_RQ_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        PCIE_RQ_MFB_META    : out std_logic_vector(MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
        PCIE_RQ_MFB_SOF     : out std_logic_vector(MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_EOF     : out std_logic_vector(MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0) := (others => '0');
        PCIE_RQ_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_SRC_RDY : out std_logic;
        PCIE_RQ_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of DMA_PTR_UPDATER is
    constant MFB_LENGTH : positive                        := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant IS_INTEL   : boolean                         := (DEVICE = "STRATIX10") or (DEVICE = "AGILEX");
    constant ADDR_NULL  : std_logic_vector(64-1 downto 0) := (others => '0');

    signal hhp_ptr_reg  : u_array_t(TX_CHANNELS -1 downto 0)(TX_PKT_DISP_HHP'length -1 downto 0);
    signal hdp_ptr_reg  : u_array_t(TX_CHANNELS -1 downto 0)(TX_PKT_DISP_HDP'length -1 downto 0);
    signal hhp_ptr_next : u_array_t(TX_CHANNELS -1 downto 0)(TX_PKT_DISP_HHP'length -1 downto 0);
    signal hdp_ptr_next : u_array_t(TX_CHANNELS -1 downto 0)(TX_PKT_DISP_HDP'length -1 downto 0);

    signal hhp_ptr_to_wr_reg   : std_logic_vector(TX_PKT_DISP_HHP'length -1 downto 0);
    signal hdp_ptr_to_wr_reg   : std_logic_vector(TX_PKT_DISP_HDP'length -1 downto 0);
    signal hhp_ptr_to_wr_next  : std_logic_vector(TX_PKT_DISP_HHP'length -1 downto 0);
    signal hdp_ptr_to_wr_next  : std_logic_vector(TX_PKT_DISP_HDP'length -1 downto 0);
    signal upd_req_vld_int     : std_logic;
    signal upd_req_vld_int_reg : std_logic;

    -- Size of a PCIE RQ header and 2 pointers (HHP and HDP, that are aligned to 4 byte boundary)
    constant FIFO_DATA_W   : positive := 3*16 + PCIE_META_REQ_HDR_W;
    constant FIFO_WR_PORTS : positive := 3;
    constant FIFO_RD_PORTS : positive := MFB_REGIONS;
    constant FIFO_SIZE     : positive := 64;

    signal fifo_din     : std_logic_vector(3*FIFO_DATA_W -1 downto 0);
    signal fifo_din_arr : slv_array_t(FIFO_WR_PORTS-1 downto 0)(FIFO_DATA_W -1 downto 0);
    signal fifo_wr      : std_logic_vector(FIFO_WR_PORTS-1 downto 0);
    signal fifo_do      : std_logic_vector(FIFO_RD_PORTS*FIFO_DATA_W -1 downto 0);
    signal fifo_do_arr  : slv_array_t(FIFO_RD_PORTS-1 downto 0)(FIFO_DATA_W -1 downto 0);
    signal fifo_full    : std_logic;
    signal fifo_rd      : std_logic_vector(FIFO_RD_PORTS-1 downto 0);
    signal fifo_empty   : std_logic_vector(FIFO_RD_PORTS-1 downto 0);

    signal tx_rt_pcie_addr_len   : std_logic;
    signal tx_rt_pcie_hdr_data   : std_logic_vector(PCIE_META_REQ_HDR_W -1 downto 0);
    signal rx_stop_pcie_addr_len : std_logic;
    signal rx_stop_pcie_hdr_data : std_logic_vector(PCIE_META_REQ_HDR_W -1 downto 0);
    signal tx_stop_pcie_addr_len : std_logic;
    signal tx_stop_pcie_hdr_data : std_logic_vector(PCIE_META_REQ_HDR_W -1 downto 0);

    signal tx_mfb_data_arr    : slv_array_t(MFB_REGIONS -1 downto 0)(MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
    signal tx_mfb_meta_arr    : slv_array_t(MFB_REGIONS -1 downto 0)(PCIE_RQ_META_WIDTH -1 downto 0);
    signal tx_mfb_eof_pos_arr : slv_array_t(MFB_REGIONS -1 downto 0)(maximum(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
begin

    assert (TX_UPD_THRESHOLD <= 2**(TX_DATA_PTR_WIDTH-1))
        report "DMA_PTR_UPDATER: Update threshold cannot exceed the half of the buffer size."
        severity FAILURE;

    assert ((MFB_REGIONS = 1 or MFB_REGIONS = 2) and MFB_REGION_SIZE = 1 and MFB_BLOCK_SIZE = 8 and MFB_ITEM_WIDTH = 32)
        report "RX_DMA_CALYPTE_PTR_UPDATER: Unsupported MFB configuration."
        severity FAILURE;

    -- psl assert_hdr_pcie_hdr_full :
    --      assert always (fifo_full = '0') abort (RESET) @rising_edge(CLK)
    --      report "DMA_PTR_UPDATER: Complete filling of the PCIe transaction FIFO occured!";

    -- =============================================================================================
    -- Pointer update upon stop of a RX DMA channel
    -- =============================================================================================
    rx_stop_pcie_addr_len <= '1' when (DEVICE = "ULTRASCALE" or RX_STOP_REQ_BUFF_BA(64-1 downto 32) /= (32-1 downto 0 => '0')) else '0';

    rx_stop_rq_hdr_gen_i : entity work.PCIE_RQ_HDR_GEN
    generic map (
        DEVICE => DEVICE
    )
    port map (
        IN_ADDRESS    => RX_STOP_REQ_BUFF_BA(63 downto 2),
        IN_VFID       => (others => '0'),
        IN_TAG        => (others => '0'),
        IN_DW_CNT     => std_logic_vector(to_unsigned(2, 11)),
        IN_ATTRIBUTES => "00" & RX_STOP_REQ_P2P_EN,
        IN_FBE        => "1111",
        IN_LBE        => "0011",
        IN_ADDR_LEN   => rx_stop_pcie_addr_len,
        IN_REQ_TYPE   => '1',       -- only memory writes

        OUT_HEADER => rx_stop_pcie_hdr_data
    );

    fifo_din_arr(2) <= std_logic_vector(resize(unsigned(RX_STOP_REQ_HHP), 16))
                       & X"0000"
                       & std_logic_vector(resize(unsigned(RX_STOP_REQ_HDP), 16))
                       & rx_stop_pcie_hdr_data;
    fifo_wr(2)      <= RX_STOP_REQ_EN and (not fifo_full) when RX_STOP_REQ_BUFF_BA /= ADDR_NULL else '0';
    RX_STOP_REQ_ACK <= not fifo_full when RX_STOP_REQ_BUFF_BA /= ADDR_NULL else '0';

    -- =============================================================================================
    -- Pointer update upon stop of a RX DMA channel
    -- =============================================================================================
    tx_stop_pcie_addr_len <= '1' when (DEVICE = "ULTRASCALE" or TX_STOP_REQ_BUFF_BA(64-1 downto 32) /= (32-1 downto 0 => '0')) else '0';

    tx_stop_rq_hdr_gen_i : entity work.PCIE_RQ_HDR_GEN
    generic map (
        DEVICE => DEVICE
    )
    port map (
        IN_ADDRESS    => TX_STOP_REQ_BUFF_BA(63 downto 2),
        IN_VFID       => (others => '0'),
        IN_TAG        => (others => '0'),
        IN_DW_CNT     => std_logic_vector(to_unsigned(2, 11)),
        IN_ATTRIBUTES => "00" & TX_STOP_REQ_P2P_EN,
        IN_FBE        => "1111",
        IN_LBE        => "0011",
        IN_ADDR_LEN   => tx_stop_pcie_addr_len,
        IN_REQ_TYPE   => '1',       -- only memory writes

        OUT_HEADER => tx_stop_pcie_hdr_data
    );

    fifo_din_arr(1) <= std_logic_vector(resize(unsigned(TX_STOP_REQ_HHP), 16))
                       & X"0000"
                       & std_logic_vector(resize(unsigned(TX_STOP_REQ_HDP), 16))
                       & tx_stop_pcie_hdr_data;
    fifo_wr(1)      <= TX_STOP_REQ_EN and (not fifo_full) when TX_STOP_REQ_BUFF_BA /= ADDR_NULL else '0';
    TX_STOP_REQ_ACK <= not fifo_full when TX_STOP_REQ_BUFF_BA /= ADDR_NULL else '0';

    -- =============================================================================================
    -- Runtime update of pointers from TX DMA
    -- =============================================================================================
    ptr_upd_state_regs_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                hdp_ptr_reg           <= (others => (others => '0'));
                hhp_ptr_reg           <= (others => (others => '0'));
                TX_START_REQ_ACK      <= '0';
                upd_req_vld_int_reg   <= '0';
                hdp_ptr_to_wr_reg     <= (others => '0');
                hhp_ptr_to_wr_reg     <= (others => '0');
            else
                hdp_ptr_reg           <= hdp_ptr_next;
                hhp_ptr_reg           <= hhp_ptr_next;
                TX_START_REQ_ACK      <= TX_START_REQ_VLD;
                upd_req_vld_int_reg   <= upd_req_vld_int;
                hdp_ptr_to_wr_reg     <= hdp_ptr_to_wr_next;
                hhp_ptr_to_wr_reg     <= hhp_ptr_to_wr_next;
            end if;
        end if;
    end process;

    -- Channel is set immediately upon update from Packet dispatcher but data from Software manager
    -- arrive one clock cycle after setting the channel so the hhp_ptr_to_wr, upd_req_vld_int and
    -- hdp_ptr_to_wr are routed through register to count with this one-clock delay
    TX_RT_UPD_CH <= TX_PKT_DISP_CH;

    ptr_upd_disp_p : process (all) is
        variable curr_chan : integer range 0 to (TX_CHANNELS -1);
        variable distance  : unsigned(TX_DATA_PTR_WIDTH -1 downto 0);
    begin

        hdp_ptr_next       <= hdp_ptr_reg;
        hhp_ptr_next       <= hhp_ptr_reg;
        hdp_ptr_to_wr_next <= hdp_ptr_to_wr_reg;
        hhp_ptr_to_wr_next <= hhp_ptr_to_wr_reg;
        upd_req_vld_int    <= '0';

        if (TX_PKT_DISP_EN = '1') then
            curr_chan := to_integer(unsigned(TX_PKT_DISP_CH));
            distance  := unsigned(TX_PKT_DISP_HDP) - hdp_ptr_reg(curr_chan);

            -- Update internal pointer registers only if the size of an update exceeds the threshold
            -- in which case also dispatches a pointer update
            if (distance >= to_unsigned(TX_UPD_THRESHOLD, TX_DATA_PTR_WIDTH)) then
                hdp_ptr_next(curr_chan) <= unsigned(TX_PKT_DISP_HDP);
                hhp_ptr_next(curr_chan) <= unsigned(TX_PKT_DISP_HHP);
                hdp_ptr_to_wr_next      <= TX_PKT_DISP_HDP;
                hhp_ptr_to_wr_next      <= TX_PKT_DISP_HHP;
                upd_req_vld_int         <= '1';
            end if;
        end if;

        if (TX_START_REQ_VLD = '1') then
            curr_chan               := to_integer(unsigned(TX_START_REQ_CH));
            hdp_ptr_next(curr_chan) <= (others => '0');
            hhp_ptr_next(curr_chan) <= (others => '0');
        end if;
    end process;

    tx_rt_pcie_addr_len <= '1' when (DEVICE = "ULTRASCALE" or TX_RT_UPD_BUFF_BA(64-1 downto 32) /= (32-1 downto 0 => '0')) else '0';

    rt_upd_rq_hdr_gen_i : entity work.PCIE_RQ_HDR_GEN
    generic map (
        DEVICE => DEVICE
    )
    port map (
        IN_ADDRESS    => TX_RT_UPD_BUFF_BA(63 downto 2),
        IN_VFID       => (others => '0'),
        IN_TAG        => (others => '0'),
        IN_DW_CNT     => std_logic_vector(to_unsigned(2, 11)),
        IN_ATTRIBUTES => "00" & TX_RT_UPD_P2P_EN,
        IN_FBE        => "1111",
        IN_LBE        => "0011",
        IN_ADDR_LEN   => tx_rt_pcie_addr_len,
        IN_REQ_TYPE   => '1',       -- only memory writes

        OUT_HEADER => tx_rt_pcie_hdr_data
    );

    fifo_din_arr(0) <= std_logic_vector(resize(unsigned(hhp_ptr_to_wr_reg), 16))
                       & X"0000"
                       & std_logic_vector(resize(unsigned(hdp_ptr_to_wr_reg), 16))
                       & tx_rt_pcie_hdr_data;

    fifo_wr(0)      <= upd_req_vld_int_reg when TX_RT_UPD_BUFF_BA /= ADDR_NULL else '0';

    -- =============================================================================================
    -- Dispatch FIFO where all of the update requests get collected
    -- =============================================================================================
    fifo_din <= slv_array_ser(fifo_din_arr);

    fifo_i : entity work.FIFOX_MULTI(FULL)
    generic map (
        DATA_WIDTH          => FIFO_DATA_W,
        ITEMS               => FIFO_SIZE,
        WRITE_PORTS         => FIFO_WR_PORTS,
        READ_PORTS          => FIFO_RD_PORTS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 2,
        ALMOST_EMPTY_OFFSET => 2,
        ALLOW_SINGLE_FIFO   => FALSE,
        SAFE_READ_MODE      => FALSE
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        DI    => fifo_din,
        WR    => fifo_wr,
        FULL  => fifo_full,
        AFULL => open,

        DO     => fifo_do,
        RD     => fifo_rd,
        EMPTY  => fifo_empty,
        AEMPTY => open
    );

    fifo_do_arr <= slv_array_deser(fifo_do, MFB_REGIONS);

    tx_mfb_data_meta_g : for rgn in 0 to (FIFO_RD_PORTS -1) generate
        intel_dev_g : if (IS_INTEL) generate
            tx_mfb_data_arr(rgn)    <= (MFB_LENGTH/MFB_REGIONS -1 downto 3*16 => '0')
                                       & fifo_do_arr(rgn)(3*16+PCIE_META_REQ_HDR_W -1 downto PCIE_META_REQ_HDR_W);
            tx_mfb_meta_arr(rgn)    <= (PCIE_RQ_META_HEADER => fifo_do_arr(rgn)(PCIE_META_REQ_HDR_W -1 downto 0),
                                        others              => '0');
            tx_mfb_eof_pos_arr(rgn) <= std_logic_vector(to_unsigned(1, PCIE_RQ_MFB_EOF_POS'length/MFB_REGIONS));
        else generate
            tx_mfb_data_arr(rgn)    <= (MFB_LENGTH/MFB_REGIONS -1 downto PCIE_META_REQ_HDR_W + 3*16 => '0')
                                       & fifo_do_arr(rgn);
            tx_mfb_eof_pos_arr(rgn) <= std_logic_vector(to_unsigned(5, PCIE_RQ_MFB_EOF_POS'length/MFB_REGIONS));
            tx_mfb_meta_arr(rgn)    <= (PCIE_RQ_META_FBE => "1111", PCIE_RQ_META_LBE => "0011", others => '0');
        end generate;
    end generate;

    PCIE_RQ_MFB_DATA    <= slv_array_ser(tx_mfb_data_arr);
    PCIE_RQ_MFB_META    <= slv_array_ser(tx_mfb_meta_arr);
    PCIE_RQ_MFB_SOF     <= not fifo_empty;
    PCIE_RQ_MFB_EOF     <= not fifo_empty;
    PCIE_RQ_MFB_SOF_POS <= (others => '0');
    PCIE_RQ_MFB_EOF_POS <= slv_array_ser(tx_mfb_eof_pos_arr);
    PCIE_RQ_MFB_SRC_RDY <= or (not fifo_empty);
    fifo_rd             <= (not fifo_empty) and PCIE_RQ_MFB_DST_RDY;
end architecture;
