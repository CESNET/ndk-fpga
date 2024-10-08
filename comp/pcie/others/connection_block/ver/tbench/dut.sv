/* dut.sv: system verilog cover of vhdl DUT
 * Copyright (C) 2020 CESNET
 * Author: Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

`ifndef MODUL_DUT
`define MODUL_DUT

module DUT (
		input logic CLK,
        input logic RESET,
        //AVALON
        avst_tx_if.dut pce_avalon_tx,
        avst_rx_if.dut pce_avalon_rx,
        //PTC TRANSACTION MFB
        iMfbRx.dut ptc_mfb_rx,
        iMfbTx.dut ptc_mfb_tx,
        //MI MFB
        iMfbRx.dut mi_mfb_rx,
        iMfbTx.dut mi_mfb_tx
	);

   PCIE_CONNECTION_BLOCK #(
		.MFB_REGIONS           (2),
		.MFB_REGION_SIZE       (1),
		.MFB_BLOCK_SIZE        (8),
		.MFB_ITEM_WIDTH        (32),
        .MFB_UP_META_WIDTH     (32+128),
		.MFB_DOWN_META_WIDTH   (3+32+128),
		.DEVICE                ("STRATIX10"),
        .ENDPOINT_TYPE         ("P_TILE")
   )
   DUT_VHDL (
        .CLK              (CLK),
        .RESET            (RESET),

//        -- =====================================================================
//        -- TO/FROM STRATIX 10 PCIE H-TILE/P-TILE IP CORE
//        -- =====================================================================
//        -- DOWN stream
        .RX_AVST_DATA      (pce_avalon_rx.data),      //: in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .RX_AVST_HDR       (pce_avalon_rx.hdr),       //: in  std_logic_vector(MFB_REGIONS*128-1 downto 0); -- P-TILE only
        .RX_AVST_PREFIX    (pce_avalon_rx.prefix),    //: in  std_logic_vector(MFB_REGIONS*32-1 downto 0); -- P-TILE only
		.RX_AVST_SOP       (pce_avalon_rx.sop),       //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
		.RX_AVST_EOP       (pce_avalon_rx.eop),       //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
        .RX_AVST_EMPTY     (pce_avalon_rx.empty),     //: in  std_logic_vector(MFB_REGIONS*3-1 downto 0);
        .RX_AVST_BAR_RANGE (pce_avalon_rx.bar_range), //: in  std_logic_vector(MFB_REGIONS*3-1 downto 0);
        .RX_AVST_VALID     (pce_avalon_rx.valid),     //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
		.RX_AVST_READY     (pce_avalon_rx.ready),     //: out std_logic;
//        -- UP stream
        .TX_AVST_DATA      (pce_avalon_tx.data),   //: out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .TX_AVST_HDR       (pce_avalon_tx.hdr),    //: out std_logic_vector(MFB_REGIONS*128-1 downto 0); -- P-TILE only
        .TX_AVST_PREFIX    (pce_avalon_tx.prefix), //: out std_logic_vector(MFB_REGIONS*32-1 downto 0); -- P-TILE only
		.TX_AVST_SOP       (pce_avalon_tx.sop),    //: out std_logic_vector(MFB_REGIONS-1 downto 0);
		.TX_AVST_EOP       (pce_avalon_tx.eop),    //: out std_logic_vector(MFB_REGIONS-1 downto 0);
        .TX_AVST_ERROR     (pce_avalon_tx.error),  //: out std_logic_vector(MFB_REGIONS-1 downto 0);
        .TX_AVST_VALID     (pce_avalon_tx.valid),  //: out std_logic_vector(MFB_REGIONS-1 downto 0);
		.TX_AVST_READY     (pce_avalon_tx.ready),  //: in  std_logic;
//        -- =====================================================================
//        -- TO/FROM PCIE TRANSACTION CONTROLER (PTC)
//        -- =====================================================================
//        -- UP stream
        .RQ_MFB_DATA       (ptc_mfb_rx.DATA),    //: in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .RQ_MFB_META       (ptc_mfb_rx.META),    //: in  std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
        .RQ_MFB_SOF        (ptc_mfb_rx.SOF),     //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
        .RQ_MFB_EOF        (ptc_mfb_rx.EOF),     //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
        .RQ_MFB_SOF_POS    (ptc_mfb_rx.SOF_POS), //: in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        .RQ_MFB_EOF_POS    (ptc_mfb_rx.EOF_POS), //: in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .RQ_MFB_SRC_RDY    (ptc_mfb_rx.SRC_RDY), //: in  std_logic;
        .RQ_MFB_DST_RDY    (ptc_mfb_rx.DST_RDY), //: out std_logic;
//         -- DOWN stream
        .RC_MFB_DATA       (ptc_mfb_tx.DATA),    //: out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .RC_MFB_META       (ptc_mfb_tx.META),    //: out std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
        .RC_MFB_SOF        (ptc_mfb_tx.SOF),     //: out std_logic_vector(MFB_REGIONS-1 downto 0);
        .RC_MFB_EOF        (ptc_mfb_tx.EOF),     //: out std_logic_vector(MFB_REGIONS-1 downto 0);
        .RC_MFB_SOF_POS    (ptc_mfb_tx.SOF_POS), //: out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        .RC_MFB_EOF_POS    (ptc_mfb_tx.EOF_POS), //: out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .RC_MFB_SRC_RDY    (ptc_mfb_tx.SRC_RDY), //: out std_logic;
        .RC_MFB_DST_RDY    (ptc_mfb_tx.DST_RDY),  //: in  std_logic; -- always is VCC
//        -- =====================================================================
//        -- TO/FROM MI32 TRANSACTION CONTROLER (MTC)
//        -- =====================================================================
//        -- UP stream
        .CC_MFB_DATA       (mi_mfb_rx.DATA),    //: in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .CC_MFB_META       (mi_mfb_rx.META),    //: in  std_logic_vector(MFB_REGIONS*MFB_UP_META_WIDTH-1 downto 0);
        .CC_MFB_SOF        (mi_mfb_rx.SOF),     //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
        .CC_MFB_EOF        (mi_mfb_rx.EOF),     //: in  std_logic_vector(MFB_REGIONS-1 downto 0);
        .CC_MFB_SOF_POS    (mi_mfb_rx.SOF_POS), //: in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        .CC_MFB_EOF_POS    (mi_mfb_rx.EOF_POS), //: in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .CC_MFB_SRC_RDY    (mi_mfb_rx.SRC_RDY), //: in  std_logic;
        .CC_MFB_DST_RDY    (mi_mfb_rx.DST_RDY), //: out std_logic;
//      .  -- DOWN stream
        .CQ_MFB_DATA       (mi_mfb_tx.DATA),    //: out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        .CQ_MFB_META       (mi_mfb_tx.META),    //: out std_logic_vector(MFB_REGIONS*MFB_DOWN_META_WIDTH-1 downto 0);
        .CQ_MFB_SOF        (mi_mfb_tx.SOF),     //: out std_logic_vector(MFB_REGIONS-1 downto 0);
        .CQ_MFB_EOF        (mi_mfb_tx.EOF),     //: out std_logic_vector(MFB_REGIONS-1 downto 0);
        .CQ_MFB_SOF_POS    (mi_mfb_tx.SOF_POS), //: out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        .CQ_MFB_EOF_POS    (mi_mfb_tx.EOF_POS), //: out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        .CQ_MFB_SRC_RDY    (mi_mfb_tx.SRC_RDY), //: out std_logic;
        .CQ_MFB_DST_RDY    (mi_mfb_tx.DST_RDY)  //: in  std_logic
   );

endmodule

`endif
