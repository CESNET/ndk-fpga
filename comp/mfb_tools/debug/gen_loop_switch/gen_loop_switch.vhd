-- gen_loop_switch.vhd: Generator/Loopback switching unit
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

-- -----------------------------------------------------------------------------
-- Description
-- -----------------------------------------------------------------------------

-- This unit contains MI32-configurable switch plane for connection between
-- DMA Module and Ethernet side in both RX and TX stream.
-- By default the connection is ETH_RX->DMA_RX and DMA_TX->ETH_TX.
-- It allows for loopback between ETH_RX->ETH_TX and DMA_TX->DMA_RX as well as
-- connection of MFB generators on DMA_RX and ETH_TX.
-- These generators have their own part of MI32 address space.
--
-- **Connection diagram:**
--
-- .. code-block::
--
--                         +--------+  +---\
--                         | RX Gen +--+ 1  \             +---\
--   ETH_RX                +--------+  |MUX_C+------------+ 0  \   +------+ DMA_RX
--   >--------------------------+------+ 0  /             |MUX_A+--+ FIFO +------>
--                              |      +---/          +---+ 1  /   +------+
--                              |                     |   +---/
--                              |                     |
--                              |                     |
--                              |                     |
--                      /---+   |                     |
--          +------+   /  1 +---+          /---+      |
--   <------+ FIFO +--+MUX_B|             /  0 +------+--------------------------<
--   ETH_TX +------+   \  0 +------------+MUX_D|  +-----------------+       DMA_TX
--                      \---+             \  1 +--+ TX Gen / Player |
--                                         \---+  +-----------------+
--
-- **MI address offsets:**
--
-- .. code-block::
--
--   0x000      -- RX loopback MUX_A  (0 -> RX stream, 1 -> TX stream loopback)
--   0x004      -- TX loopback MUX_B  (0 -> TX stream, 1 -> RX stream loopback)
--   0x008      -- RX generator MUX_C (0 -> RX stream, 1 -> RX generator)
--   0x00C      -- TX generator MUX_D (0 -> TX stream, 1 -> TX generator, 2 -> TX Frame Player)
--   0x040-0x04C -- DMA RX MFB speed meter (0x0 - tics, 0x4 - status, 0x8 - items, 0xC - clear)
--   0x050-0x05C -- DMA TX MFB speed meter (0x0 - tics, 0x4 - status, 0x8 - items, 0xC - clear)
--   0x060-0x06C -- ETH RX MFB speed meter (0x0 - tics, 0x4 - status, 0x8 - items, 0xC - clear)
--   0x070-0x07C -- ETH TX MFB speed meter (0x0 - tics, 0x4 - status, 0x8 - items, 0xC - clear)
--   0x080-0x0BF -- RX generator address space
--   0x0C0-0x0FF -- TX generator address space
--   free address space from 0x100-0x17F
--   0x180-0x1BF -- RX Frame Player address space
--   0x1C0-0x1FF -- TX Frame Player address space
--
--   Notes:
--   - Only the lowest 8 bits of address considered.
--   - Generator address offsets -> see entity of subcomponent MFB_GENERATOR_MI32
--
-- .. warning::
--
--   Only switch mux selection registers when there is no data on the input!
--
entity GEN_LOOP_SWITCH is
    Generic (
        -- number of regions in a data word
        REGIONS           : natural := 2;
        -- number of blocks in a region
        REGION_SIZE       : natural := 8;
        -- number of items in a block
        BLOCK_SIZE        : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH        : natural := 8;
        -- maximum supported packet MTU in bytes
        PKT_MTU           : natural := 16383;
        -- number of supported DMA channels on RX
        RX_DMA_CHANNELS   : natural := 32;
        -- size of NPP Header (in bytes)
        -- must not be greater than BLOCK_SIZE*ITEM_WIDTH/8
        NPP_HDR_SIZE      : natural := 4;
        -- number of supported DMA channels on TX
        TX_DMA_CHANNELS   : natural := 32;
        -- Width of User Header Metadata information
        HDR_META_WIDTH    : natural := 12;
        -- Depth of FIFO memory in MFB FRAME PLAYERs
        PLAYER_FIFO_DEPTH : natural := 512;
        -- enable inserting generated NPP Header
        -- at the start of each MFB frame in RX generator
        RX_HDR_INS_EN     : boolean := false;
        -- MI_CLK and CLK are the same
        -- set this to True to remove MI asynch conversion
        SAME_CLK          : boolean := false;
        -- MI PIPE enable
        MI_PIPE_EN        : boolean := true;
        -- Setting this to True will disable the component and create direct
        -- connection from DMA interfaces to ETH interfaces
        FAKE_SWITCH       : boolean := false;
        -- FPGA device string
        DEVICE            : string  := "STRATIX10"
    );
    Port (
        -- ---------------------------------------------------------------------
        -- MI32 interface
        -- ---------------------------------------------------------------------

        MI_CLK   : in  std_logic;
        MI_RESET : in  std_logic;
        MI_DWR   : in  std_logic_vector(32-1 downto 0);
        MI_ADDR  : in  std_logic_vector(32-1 downto 0);
        MI_BE    : in  std_logic_vector(32/8-1 downto 0); -- Not supported!
        MI_RD    : in  std_logic;
        MI_WR    : in  std_logic;
        MI_ARDY  : out std_logic;
        MI_DRD   : out std_logic_vector(32-1 downto 0);
        MI_DRDY  : out std_logic;

        -- ---------------------------------------------------------------------

        -- Internal clock and reset for all interfaces besides MI32
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        -- ---------------------------------------------------------------------
        -- RX MFB+MVB interface from Ethernet
        -- ---------------------------------------------------------------------

        -- MVB interface with DMA instructions
        ETH_RX_MVB_LEN      : in  std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
        ETH_RX_MVB_CHANNEL  : in  std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
        ETH_RX_MVB_HDR_META : in  std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
        ETH_RX_MVB_DISCARD  : in  std_logic_vector(REGIONS*1-1 downto 0);
        ETH_RX_MVB_VLD      : in  std_logic_vector(REGIONS-1 downto 0);
        ETH_RX_MVB_SRC_RDY  : in  std_logic;
        ETH_RX_MVB_DST_RDY  : out std_logic;
        -- MFB interface with data packets
        ETH_RX_MFB_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        ETH_RX_MFB_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        ETH_RX_MFB_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        ETH_RX_MFB_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        ETH_RX_MFB_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        ETH_RX_MFB_SRC_RDY  : in  std_logic;
        ETH_RX_MFB_DST_RDY  : out std_logic;

        -- ---------------------------------------------------------------------

        -- ---------------------------------------------------------------------
        -- TX MFB+MVB interface to Ethernet
        -- ---------------------------------------------------------------------

        -- MVB interface with DMA instructions
        ETH_TX_MVB_LEN      : out std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
        ETH_TX_MVB_CHANNEL  : out std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
        ETH_TX_MVB_HDR_META : out std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
        ETH_TX_MVB_VLD      : out std_logic_vector(REGIONS-1 downto 0);
        ETH_TX_MVB_SRC_RDY  : out std_logic;
        ETH_TX_MVB_DST_RDY  : in  std_logic;
        -- MFB interface with data packets
        ETH_TX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        ETH_TX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        ETH_TX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        ETH_TX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        ETH_TX_MFB_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        ETH_TX_MFB_SRC_RDY  : out std_logic;
        ETH_TX_MFB_DST_RDY  : in  std_logic;

        -- ---------------------------------------------------------------------

        -- ---------------------------------------------------------------------
        -- RX MFB+MVB interface to DMA module
        -- ---------------------------------------------------------------------

        -- MVB interface with DMA instructions
        DMA_RX_MVB_LEN      : out std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
        DMA_RX_MVB_CHANNEL  : out std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
        DMA_RX_MVB_HDR_META : out std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
        DMA_RX_MVB_DISCARD  : out std_logic_vector(REGIONS*1-1 downto 0);
        DMA_RX_MVB_VLD      : out std_logic_vector(REGIONS-1 downto 0);
        DMA_RX_MVB_SRC_RDY  : out std_logic;
        DMA_RX_MVB_DST_RDY  : in  std_logic;
        -- MFB interface with data packets
        DMA_RX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        DMA_RX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        DMA_RX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        DMA_RX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        DMA_RX_MFB_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        DMA_RX_MFB_SRC_RDY  : out std_logic;
        DMA_RX_MFB_DST_RDY  : in  std_logic;

        -- ---------------------------------------------------------------------

        -- ---------------------------------------------------------------------
        -- TX MFB+MVB interface from DMA module
        -- ---------------------------------------------------------------------

        -- MVB interface with DMA instructions
        DMA_TX_MVB_LEN      : in  std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
        DMA_TX_MVB_CHANNEL  : in  std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
        DMA_TX_MVB_HDR_META : in  std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
        DMA_TX_MVB_VLD      : in  std_logic_vector(REGIONS-1 downto 0);
        DMA_TX_MVB_SRC_RDY  : in  std_logic;
        DMA_TX_MVB_DST_RDY  : out std_logic;
        -- MFB interface with data packets
        DMA_TX_MFB_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        DMA_TX_MFB_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        DMA_TX_MFB_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        DMA_TX_MFB_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        DMA_TX_MFB_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        DMA_TX_MFB_SRC_RDY  : in  std_logic;
        DMA_TX_MFB_DST_RDY  : out std_logic

        -- ---------------------------------------------------------------------
    );
end entity;

architecture FULL of GEN_LOOP_SWITCH is

    constant LENGTH_WIDTH       : natural := log2(PKT_MTU+1);

    constant BLOCK_WIDTH  : natural := BLOCK_SIZE*ITEM_WIDTH;
    constant REGION_WIDTH : natural := REGION_SIZE*BLOCK_WIDTH;

    -- local registers + speed meter + RX Generator + TX Generator + RX Frame Player + TX Frame Player
    constant MI_SPLIT_PORTS : natural := 6;

    constant MI_SPLIT_ADDR_BASE : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0) := (X"000001C0",
                                                                                            X"00000180",
                                                                                            X"000000C0",
                                                                                            X"00000080",
                                                                                            X"00000040",
                                                                                            X"00000000");

    signal mi_sync_dwr      : std_logic_vector(32-1 downto 0);
    signal mi_sync_addr     : std_logic_vector(32-1 downto 0);
    signal mi_sync_be       : std_logic_vector(4-1 downto 0);
    signal mi_sync_rd       : std_logic;
    signal mi_sync_wr       : std_logic;
    signal mi_sync_ardy     : std_logic;
    signal mi_sync_drd      : std_logic_vector(32-1 downto 0);
    signal mi_sync_drdy     : std_logic;

    signal mi_pipe_dwr      : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_pipe_addr     : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_pipe_be       : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(4-1 downto 0);
    signal mi_pipe_rd       : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_pipe_wr       : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_pipe_ardy     : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_pipe_drd      : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_pipe_drdy     : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);

    signal mi_pipe_addr_local : unsigned(6-1 downto 0);
    signal mi_pipe_addr_sm    : unsigned(6-1 downto 0);

    signal rx_gen_mux_sel_reg  : std_logic_vector(2-1 downto 0); -- direct connection ("00"), generator ("01"), Frame Player ("10")
    signal tx_gen_mux_sel_reg  : std_logic_vector(2-1 downto 0); -- direct connection ("00"), generator ("01"), Frame Player ("10")
    signal rx_loop_mux_sel_reg : std_logic;
    signal tx_loop_mux_sel_reg : std_logic;

    signal DMA_TX_MVB_C_CH     : std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
    signal ETH_RX_MVB_C_CH     : std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);

    signal rx_gen_instr_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal rx_gen_instr_mvb_channel  : std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
    signal rx_gen_instr_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal rx_gen_instr_mvb_discard  : std_logic_vector(REGIONS*1-1 downto 0);
    signal rx_gen_instr_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal rx_gen_instr_mvb_src_rdy  : std_logic;
    signal rx_gen_instr_mvb_dst_rdy  : std_logic;

    signal rx_gen_eth_mfb_data      : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal rx_gen_eth_mfb_sof       : std_logic_vector(REGIONS-1 downto 0);
    signal rx_gen_eth_mfb_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal rx_gen_eth_mfb_sof_pos   : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal rx_gen_eth_mfb_eof_pos   : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal rx_gen_eth_mfb_src_rdy   : std_logic;
    signal rx_gen_eth_mfb_dst_rdy   : std_logic;

    signal rx_plr_instr_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal rx_plr_instr_mvb_channel  : std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
    signal rx_plr_instr_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal rx_plr_instr_mvb_discard  : std_logic_vector(REGIONS*1-1 downto 0);
    signal rx_plr_instr_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal rx_plr_instr_mvb_src_rdy  : std_logic;
    signal rx_plr_instr_mvb_dst_rdy  : std_logic;

    signal rx_plr_eth_mfb_data      : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal rx_plr_eth_mfb_sof       : std_logic_vector(REGIONS-1 downto 0);
    signal rx_plr_eth_mfb_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal rx_plr_eth_mfb_sof_pos   : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal rx_plr_eth_mfb_eof_pos   : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal rx_plr_eth_mfb_src_rdy   : std_logic;
    signal rx_plr_eth_mfb_dst_rdy   : std_logic;

    signal tx_gen_instr_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal tx_gen_instr_mvb_channel  : std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
    signal tx_gen_instr_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal tx_gen_instr_mvb_discard  : std_logic_vector(REGIONS*1-1 downto 0);
    signal tx_gen_instr_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal tx_gen_instr_mvb_src_rdy  : std_logic;
    signal tx_gen_instr_mvb_dst_rdy  : std_logic;

    signal tx_gen_eth_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx_gen_eth_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_gen_eth_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_gen_eth_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx_gen_eth_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx_gen_eth_mfb_src_rdy : std_logic;
    signal tx_gen_eth_mfb_dst_rdy : std_logic;

    signal tx_plr_instr_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal tx_plr_instr_mvb_channel  : std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
    signal tx_plr_instr_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal tx_plr_instr_mvb_discard  : std_logic_vector(REGIONS*1-1 downto 0);
    signal tx_plr_instr_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal tx_plr_instr_mvb_src_rdy  : std_logic;
    signal tx_plr_instr_mvb_dst_rdy  : std_logic;

    signal tx_plr_eth_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx_plr_eth_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_plr_eth_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_plr_eth_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx_plr_eth_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx_plr_eth_mfb_src_rdy : std_logic;
    signal tx_plr_eth_mfb_dst_rdy : std_logic;

    signal rx_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal rx_mvb_channel  : std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
    signal rx_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal rx_mvb_discard  : std_logic_vector(REGIONS*1-1 downto 0);
    signal rx_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal rx_mvb_src_rdy  : std_logic;
    signal rx_mvb_dst_rdy  : std_logic;

    signal rx_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal rx_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal rx_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal rx_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal rx_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal rx_mfb_src_rdy : std_logic;
    signal rx_mfb_dst_rdy : std_logic;

    signal tx_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal tx_mvb_channel  : std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
    signal tx_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal tx_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal tx_mvb_src_rdy  : std_logic;
    signal tx_mvb_dst_rdy  : std_logic;

    signal tx_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx_mfb_src_rdy : std_logic;
    signal tx_mfb_dst_rdy : std_logic;

    signal rx_loop_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal rx_loop_mvb_channel  : std_logic_vector(REGIONS*log2(RX_DMA_CHANNELS)-1 downto 0);
    signal rx_loop_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal rx_loop_mvb_discard  : std_logic_vector(REGIONS*1-1 downto 0);
    signal rx_loop_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal rx_loop_mvb_src_rdy  : std_logic;
    signal rx_loop_mvb_dst_rdy  : std_logic;

    signal rx_loop_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal rx_loop_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal rx_loop_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal rx_loop_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal rx_loop_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal rx_loop_mfb_src_rdy : std_logic;
    signal rx_loop_mfb_dst_rdy : std_logic;

    signal tx_loop_mvb_len      : std_logic_vector(REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal tx_loop_mvb_channel  : std_logic_vector(REGIONS*log2(TX_DMA_CHANNELS)-1 downto 0);
    signal tx_loop_mvb_hdr_meta : std_logic_vector(REGIONS*HDR_META_WIDTH-1 downto 0);
    signal tx_loop_mvb_vld      : std_logic_vector(REGIONS-1 downto 0);
    signal tx_loop_mvb_src_rdy  : std_logic;
    signal tx_loop_mvb_dst_rdy  : std_logic;

    signal tx_loop_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal tx_loop_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_loop_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal tx_loop_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal tx_loop_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal tx_loop_mfb_src_rdy : std_logic;
    signal tx_loop_mfb_dst_rdy : std_logic;

    signal DMA_TX_MVB_DST_RDY_0 : std_logic;
    signal DMA_TX_MVB_DST_RDY_1 : std_logic;
    signal ETH_RX_MVB_DST_RDY_0 : std_logic;
    signal ETH_RX_MVB_DST_RDY_1 : std_logic;

    signal DMA_TX_MFB_DST_RDY_0 : std_logic;
    signal DMA_TX_MFB_DST_RDY_1 : std_logic;
    signal ETH_RX_MFB_DST_RDY_0 : std_logic;
    signal ETH_RX_MFB_DST_RDY_1 : std_logic;

    signal rx_loop_mvb_len_arr      : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal rx_loop_mvb_channel_arr  : slv_array_t     (REGIONS-1 downto 0)(log2(RX_DMA_CHANNELS)-1 downto 0);
    signal rx_loop_mvb_hdr_meta_arr : slv_array_t     (REGIONS-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    signal rx_loop_mvb_discard_arr  : slv_array_t     (REGIONS-1 downto 0)(1-1 downto 0);
    signal rx_loop_mvb_data_arr     : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1 downto 0);
    signal rx_loop_mvb_data         : std_logic_vector(REGIONS*(log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1)-1 downto 0);

    signal DMA_RX_MVB_LEN_arr      : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal DMA_RX_MVB_CHANNEL_arr  : slv_array_t     (REGIONS-1 downto 0)(log2(RX_DMA_CHANNELS)-1 downto 0);
    signal DMA_RX_MVB_HDR_META_arr : slv_array_t     (REGIONS-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    signal DMA_RX_MVB_DISCARD_arr  : slv_array_t     (REGIONS-1 downto 0)(1-1 downto 0);
    signal DMA_RX_MVB_DATA_arr     : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1 downto 0);
    signal DMA_RX_MVB_DATA         : std_logic_vector(REGIONS*(log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1)-1 downto 0);

    signal tx_loop_mvb_len_arr      : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal tx_loop_mvb_channel_arr  : slv_array_t     (REGIONS-1 downto 0)(log2(TX_DMA_CHANNELS)-1 downto 0);
    signal tx_loop_mvb_hdr_meta_arr : slv_array_t     (REGIONS-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    signal tx_loop_mvb_data_arr     : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1 downto 0);
    signal tx_loop_mvb_data         : std_logic_vector(REGIONS*(log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH)-1 downto 0);

    signal ETH_TX_MVB_LEN_arr      : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal ETH_TX_MVB_CHANNEL_arr  : slv_array_t     (REGIONS-1 downto 0)(log2(TX_DMA_CHANNELS)-1 downto 0);
    signal ETH_TX_MVB_HDR_META_arr : slv_array_t     (REGIONS-1 downto 0)(HDR_META_WIDTH-1 downto 0);
    signal ETH_TX_MVB_DATA_arr     : slv_array_t     (REGIONS-1 downto 0)(log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1 downto 0);
    signal ETH_TX_MVB_DATA         : std_logic_vector(REGIONS*(log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH)-1 downto 0);

    signal rx_cnt_ticks     : std_logic_vector(24-1 downto 0);
    signal rx_cnt_ticks_max : std_logic;
    signal rx_cnt_bytes     : std_logic_vector(32-1 downto 0);
    signal rx_cnt_clear     : std_logic;

    signal tx_cnt_ticks     : std_logic_vector(24-1 downto 0);
    signal tx_cnt_ticks_max : std_logic;
    signal tx_cnt_bytes     : std_logic_vector(32-1 downto 0);
    signal tx_cnt_clear     : std_logic;

    signal eth_rx_cnt_ticks     : std_logic_vector(24-1 downto 0);
    signal eth_rx_cnt_ticks_max : std_logic;
    signal eth_rx_cnt_bytes     : std_logic_vector(32-1 downto 0);
    signal eth_rx_cnt_clear     : std_logic;

    signal eth_tx_cnt_ticks     : std_logic_vector(24-1 downto 0);
    signal eth_tx_cnt_ticks_max : std_logic;
    signal eth_tx_cnt_bytes     : std_logic_vector(32-1 downto 0);
    signal eth_tx_cnt_clear     : std_logic;

    -- Quartus
    attribute maxfan : integer;
    attribute maxfan of rx_gen_mux_sel_reg  : signal is 32;
    attribute maxfan of tx_gen_mux_sel_reg  : signal is 32;
    attribute maxfan of rx_loop_mux_sel_reg : signal is 32;
    attribute maxfan of tx_loop_mux_sel_reg : signal is 32;
    -- Vivado
    attribute max_fanout : integer;
    attribute max_fanout of rx_gen_mux_sel_reg  : signal is 32;
    attribute max_fanout of tx_gen_mux_sel_reg  : signal is 32;
    attribute max_fanout of rx_loop_mux_sel_reg : signal is 32;
    attribute max_fanout of tx_loop_mux_sel_reg : signal is 32;

begin

fake_switch_gen : if (FAKE_SWITCH) generate

    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;
    MI_DRD  <= (others => '0');

    ETH_TX_MVB_LEN      <= DMA_TX_MVB_LEN;
    ETH_TX_MVB_CHANNEL  <= DMA_TX_MVB_CHANNEL;
    ETH_TX_MVB_HDR_META <= DMA_TX_MVB_HDR_META;
    ETH_TX_MVB_VLD      <= DMA_TX_MVB_VLD;
    ETH_TX_MVB_SRC_RDY  <= DMA_TX_MVB_SRC_RDY;
    DMA_TX_MVB_DST_RDY  <= ETH_TX_MVB_DST_RDY;

    ETH_TX_MFB_DATA     <= DMA_TX_MFB_DATA;
    ETH_TX_MFB_SOF      <= DMA_TX_MFB_SOF;
    ETH_TX_MFB_EOF      <= DMA_TX_MFB_EOF;
    ETH_TX_MFB_SOF_POS  <= DMA_TX_MFB_SOF_POS;
    ETH_TX_MFB_EOF_POS  <= DMA_TX_MFB_EOF_POS;
    ETH_TX_MFB_SRC_RDY  <= DMA_TX_MFB_SRC_RDY;
    DMA_TX_MFB_DST_RDY  <= ETH_TX_MFB_DST_RDY;

    DMA_RX_MVB_LEN      <= ETH_RX_MVB_LEN;
    DMA_RX_MVB_CHANNEL  <= ETH_RX_MVB_CHANNEL;
    DMA_RX_MVB_HDR_META <= ETH_RX_MVB_HDR_META;
    DMA_RX_MVB_DISCARD  <= ETH_RX_MVB_DISCARD;
    DMA_RX_MVB_VLD      <= ETH_RX_MVB_VLD;
    DMA_RX_MVB_SRC_RDY  <= ETH_RX_MVB_SRC_RDY;
    ETH_RX_MVB_DST_RDY  <= DMA_RX_MVB_DST_RDY;

    DMA_RX_MFB_DATA     <= ETH_RX_MFB_DATA;
    DMA_RX_MFB_SOF      <= ETH_RX_MFB_SOF;
    DMA_RX_MFB_EOF      <= ETH_RX_MFB_EOF;
    DMA_RX_MFB_SOF_POS  <= ETH_RX_MFB_SOF_POS;
    DMA_RX_MFB_EOF_POS  <= ETH_RX_MFB_EOF_POS;
    DMA_RX_MFB_SRC_RDY  <= ETH_RX_MFB_SRC_RDY;
    ETH_RX_MFB_DST_RDY  <= DMA_RX_MFB_DST_RDY;

end generate;

not_fake_switch_gen : if (not FAKE_SWITCH) generate

    -- -------------------------------------------------------------------------
    -- MI32 Asynch
    -- -------------------------------------------------------------------------

    mi_clk_diff_g : if (not SAME_CLK) generate

        mi_async_i : entity work.MI_ASYNC
        generic map(
            DEVICE => DEVICE
        )
        port map(
            -- Master interface
            CLK_M     => MI_CLK,
            RESET_M   => MI_RESET,
            MI_M_DWR  => MI_DWR,
            MI_M_ADDR => MI_ADDR,
            MI_M_RD   => MI_RD,
            MI_M_WR   => MI_WR,
            MI_M_BE   => MI_BE,
            MI_M_DRD  => MI_DRD,
            MI_M_ARDY => MI_ARDY,
            MI_M_DRDY => MI_DRDY,

            -- Slave interface
            CLK_S     => CLK,
            RESET_S   => RESET,
            MI_S_DWR  => mi_sync_dwr,
            MI_S_ADDR => mi_sync_addr,
            MI_S_RD   => mi_sync_rd,
            MI_S_WR   => mi_sync_wr,
            MI_S_BE   => mi_sync_be,
            MI_S_DRD  => mi_sync_drd,
            MI_S_ARDY => mi_sync_ardy,
            MI_S_DRDY => mi_sync_drdy
        );

    else generate

        mi_sync_dwr  <= MI_DWR;
        mi_sync_addr <= MI_ADDR;
        mi_sync_rd   <= MI_RD;
        mi_sync_wr   <= MI_WR;
        mi_sync_be   <= MI_BE;

        MI_DRD       <= mi_sync_drd;
        MI_ARDY      <= mi_sync_ardy;
        MI_DRDY      <= mi_sync_drdy;

    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MI splitting
    -- -------------------------------------------------------------------------

    mi_split_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH => 32,
        DATA_WIDTH => 32,
        PORTS      => MI_SPLIT_PORTS,
        --            TX player, RX player, TX gen, RX gen, speed meter, local MUXes
        ADDR_BASE  => MI_SPLIT_ADDR_BASE,
        PIPE_OUT   => (MI_SPLIT_PORTS-1 downto 0 => MI_PIPE_EN),
        DEVICE     => DEVICE
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DWR     => mi_sync_dwr,
        RX_ADDR    => mi_sync_addr,
        RX_RD      => mi_sync_rd,
        RX_WR      => mi_sync_wr,
        RX_BE      => mi_sync_be,
        RX_DRD     => mi_sync_drd,
        RX_ARDY    => mi_sync_ardy,
        RX_DRDY    => mi_sync_drdy,

        TX_DWR     => mi_pipe_dwr,
        TX_ADDR    => mi_pipe_addr,
        TX_RD      => mi_pipe_rd,
        TX_WR      => mi_pipe_wr,
        TX_BE      => mi_pipe_be,
        TX_DRD     => mi_pipe_drd,
        TX_ARDY    => mi_pipe_ardy,
        TX_DRDY    => mi_pipe_drdy
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Local MI connection
    -- -------------------------------------------------------------------------

    mi_pipe_addr_local <= unsigned(mi_pipe_addr(0)(mi_pipe_addr_local'high downto 0));

    mi_rd_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            case to_integer(mi_pipe_addr_local) is
                -- MUX Selects
                when 16#00# => mi_pipe_drd(0) <= (0 => rx_loop_mux_sel_reg, others => '0');
                when 16#04# => mi_pipe_drd(0) <= (0 => tx_loop_mux_sel_reg, others => '0');
                when 16#08# => mi_pipe_drd(0) <= (1 downto 0 => rx_gen_mux_sel_reg , others => '0');
                when 16#0C# => mi_pipe_drd(0) <= (1 downto 0 => tx_gen_mux_sel_reg , others => '0');
                -- Others
                when others => mi_pipe_drd(0) <= X"DEAD1440";
            end case;
            mi_pipe_drdy(0) <= mi_pipe_rd(0);
            if (RESET='1') then
                mi_pipe_drdy(0) <= '0';
            end if;
        end if;
    end process;

    mi_pipe_ardy(0) <= mi_pipe_rd(0) or mi_pipe_wr(0);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MFB Speed Meters
    -- -------------------------------------------------------------------------

    mi_pipe_addr_sm <= unsigned(mi_pipe_addr(1)(mi_pipe_addr_sm'high downto 0));

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            case to_integer(mi_pipe_addr_sm) is
                -- MFB Speed Meters
                when 16#00# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(rx_cnt_ticks),32));
                when 16#04# => mi_pipe_drd(1) <= (0 => rx_cnt_ticks_max, others => '0');
                when 16#08# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(rx_cnt_bytes),32));
                when 16#10# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(tx_cnt_ticks),32));
                when 16#14# => mi_pipe_drd(1) <= (0 => tx_cnt_ticks_max, others => '0');
                when 16#18# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(tx_cnt_bytes),32));
                when 16#20# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(eth_rx_cnt_ticks),32));
                when 16#24# => mi_pipe_drd(1) <= (0 => eth_rx_cnt_ticks_max, others => '0');
                when 16#28# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(eth_rx_cnt_bytes),32));
                when 16#30# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(eth_tx_cnt_ticks),32));
                when 16#34# => mi_pipe_drd(1) <= (0 => eth_tx_cnt_ticks_max, others => '0');
                when 16#38# => mi_pipe_drd(1) <= std_logic_vector(resize(unsigned(eth_tx_cnt_bytes),32));
                -- Others
                when others => mi_pipe_drd(1) <= X"DEAD1441";
            end case;
            mi_pipe_drdy(1) <= mi_pipe_rd(1);
            if (RESET='1') then
                mi_pipe_drdy(1) <= '0';
            end if;
        end if;
    end process;

    mi_pipe_ardy(1) <= mi_pipe_rd(1) or mi_pipe_wr(1);

    rx_cnt_clear <= '1' when mi_pipe_wr(1)='1' and mi_pipe_addr_sm=16#0C# else '0';
    tx_cnt_clear <= '1' when mi_pipe_wr(1)='1' and mi_pipe_addr_sm=16#1C# else '0';
    eth_rx_cnt_clear <= '1' when mi_pipe_wr(1)='1' and mi_pipe_addr_sm=16#2C# else '0';
    eth_tx_cnt_clear <= '1' when mi_pipe_wr(1)='1' and mi_pipe_addr_sm=16#3C# else '0';

    dma_rx_mfb_speed_i : entity work.MFB_SPEED_METER
    generic map(
        REGIONS         => REGIONS    ,
        REGION_SIZE     => REGION_SIZE,
        BLOCK_SIZE      => BLOCK_SIZE ,
        ITEM_WIDTH      => ITEM_WIDTH ,
        CNT_TICKS_WIDTH => 24         ,
        CNT_BYTES_WIDTH => 32
    )
    port map(
        CLK           => CLK  ,
        RST           => RESET,

        RX_SOF        => DMA_RX_MFB_SOF    ,
        RX_EOF        => DMA_RX_MFB_EOF    ,
        RX_SOF_POS    => DMA_RX_MFB_SOF_POS,
        RX_EOF_POS    => DMA_RX_MFB_EOF_POS,
        RX_SRC_RDY    => DMA_RX_MFB_SRC_RDY,
        RX_DST_RDY    => DMA_RX_MFB_DST_RDY,

        CNT_TICKS     => rx_cnt_ticks    ,
        CNT_TICKS_MAX => rx_cnt_ticks_max,
        CNT_BYTES     => rx_cnt_bytes    ,
        CNT_CLEAR     => rx_cnt_clear
    );

    dma_tx_mfb_speed_i : entity work.MFB_SPEED_METER
    generic map(
        REGIONS         => REGIONS    ,
        REGION_SIZE     => REGION_SIZE,
        BLOCK_SIZE      => BLOCK_SIZE ,
        ITEM_WIDTH      => ITEM_WIDTH ,
        CNT_TICKS_WIDTH => 24         ,
        CNT_BYTES_WIDTH => 32
    )
    port map(
        CLK           => CLK  ,
        RST           => RESET,

        RX_SOF        => DMA_TX_MFB_SOF    ,
        RX_EOF        => DMA_TX_MFB_EOF    ,
        RX_SOF_POS    => DMA_TX_MFB_SOF_POS,
        RX_EOF_POS    => DMA_TX_MFB_EOF_POS,
        RX_SRC_RDY    => DMA_TX_MFB_SRC_RDY,
        RX_DST_RDY    => DMA_TX_MFB_DST_RDY,

        CNT_TICKS     => tx_cnt_ticks    ,
        CNT_TICKS_MAX => tx_cnt_ticks_max,
        CNT_BYTES     => tx_cnt_bytes    ,
        CNT_CLEAR     => tx_cnt_clear
    );

    eth_rx_mfb_speed_i : entity work.MFB_SPEED_METER
    generic map(
        REGIONS         => REGIONS    ,
        REGION_SIZE     => REGION_SIZE,
        BLOCK_SIZE      => BLOCK_SIZE ,
        ITEM_WIDTH      => ITEM_WIDTH ,
        CNT_TICKS_WIDTH => 24         ,
        CNT_BYTES_WIDTH => 32
    )
    port map(
        CLK           => CLK  ,
        RST           => RESET,

        RX_SOF        => ETH_RX_MFB_SOF    ,
        RX_EOF        => ETH_RX_MFB_EOF    ,
        RX_SOF_POS    => ETH_RX_MFB_SOF_POS,
        RX_EOF_POS    => ETH_RX_MFB_EOF_POS,
        RX_SRC_RDY    => ETH_RX_MFB_SRC_RDY,
        RX_DST_RDY    => ETH_RX_MFB_DST_RDY,

        CNT_TICKS     => eth_rx_cnt_ticks    ,
        CNT_TICKS_MAX => eth_rx_cnt_ticks_max,
        CNT_BYTES     => eth_rx_cnt_bytes    ,
        CNT_CLEAR     => eth_rx_cnt_clear
    );

    eth_tx_mfb_speed_i : entity work.MFB_SPEED_METER
    generic map(
        REGIONS         => REGIONS    ,
        REGION_SIZE     => REGION_SIZE,
        BLOCK_SIZE      => BLOCK_SIZE ,
        ITEM_WIDTH      => ITEM_WIDTH ,
        CNT_TICKS_WIDTH => 24         ,
        CNT_BYTES_WIDTH => 32
    )
    port map(
        CLK           => CLK  ,
        RST           => RESET,

        RX_SOF        => ETH_TX_MFB_SOF    ,
        RX_EOF        => ETH_TX_MFB_EOF    ,
        RX_SOF_POS    => ETH_TX_MFB_SOF_POS,
        RX_EOF_POS    => ETH_TX_MFB_EOF_POS,
        RX_SRC_RDY    => ETH_TX_MFB_SRC_RDY,
        RX_DST_RDY    => ETH_TX_MFB_DST_RDY,

        CNT_TICKS     => eth_tx_cnt_ticks    ,
        CNT_TICKS_MAX => eth_tx_cnt_ticks_max,
        CNT_BYTES     => eth_tx_cnt_bytes    ,
        CNT_CLEAR     => eth_tx_cnt_clear
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MUX SEL registers
    -- -------------------------------------------------------------------------

    mux_sel_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (mi_pipe_wr(0)='1') then

                if (mi_pipe_addr_local=16#00#) then
                    rx_loop_mux_sel_reg <= mi_pipe_dwr(0)(0);
                end if;

                if (mi_pipe_addr_local=16#04#) then
                    tx_loop_mux_sel_reg <= mi_pipe_dwr(0)(0);
                end if;

                if (mi_pipe_addr_local=16#08#) then
                    rx_gen_mux_sel_reg <= mi_pipe_dwr(0)(1 downto 0);
                end if;

                if (mi_pipe_addr_local=16#0C#) then
                    tx_gen_mux_sel_reg <= mi_pipe_dwr(0)(1 downto 0);
                end if;

            end if;

            if (RESET='1') then
                rx_gen_mux_sel_reg  <= (others => '0');
                tx_gen_mux_sel_reg  <= (others => '0');
                rx_loop_mux_sel_reg <= '0';
                tx_loop_mux_sel_reg <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RX Generator
    -- -------------------------------------------------------------------------

    rx_dma_gen_i : entity work.DMA_MFB_GENERATOR
    generic map(
        REGIONS        => REGIONS        ,
        REGION_SIZE    => REGION_SIZE    ,
        BLOCK_SIZE     => BLOCK_SIZE     ,
        ITEM_WIDTH     => ITEM_WIDTH     ,
        PKT_MTU        => PKT_MTU        ,
        DMA_CHANNELS   => RX_DMA_CHANNELS,
        NPP_HDR_SIZE   => NPP_HDR_SIZE   ,
        HDR_META_WIDTH => HDR_META_WIDTH ,
        HDR_INS_EN     => RX_HDR_INS_EN  ,
        SAME_CLK       => true           ,
        MI_PIPE_EN     => false          ,
        DEVICE         => DEVICE
    )
    port map(
        MI_CLK   => CLK            ,
        MI_RESET => RESET          ,
        MI_DWR   => mi_pipe_dwr (2),
        MI_ADDR  => mi_pipe_addr(2),
        MI_BE    => mi_pipe_be  (2),
        MI_RD    => mi_pipe_rd  (2),
        MI_WR    => mi_pipe_wr  (2),
        MI_ARDY  => mi_pipe_ardy(2),
        MI_DRD   => mi_pipe_drd (2),
        MI_DRDY  => mi_pipe_drdy(2),

        CLK               => CLK  ,
        RESET             => RESET,

        INSTR_MVB_LEN      => rx_gen_instr_mvb_len     ,
        INSTR_MVB_CHANNEL  => rx_gen_instr_mvb_channel ,
        INSTR_MVB_HDR_META => rx_gen_instr_mvb_hdr_meta,
        INSTR_MVB_DISCARD  => rx_gen_instr_mvb_discard ,
        INSTR_MVB_VLD      => rx_gen_instr_mvb_vld     ,
        INSTR_MVB_SRC_RDY  => rx_gen_instr_mvb_src_rdy ,
        INSTR_MVB_DST_RDY  => rx_gen_instr_mvb_dst_rdy ,
        ETH_MFB_DATA       => rx_gen_eth_mfb_data      ,
        ETH_MFB_SOF        => rx_gen_eth_mfb_sof       ,
        ETH_MFB_EOF        => rx_gen_eth_mfb_eof       ,
        ETH_MFB_SOF_POS    => rx_gen_eth_mfb_sof_pos   ,
        ETH_MFB_EOF_POS    => rx_gen_eth_mfb_eof_pos   ,
        ETH_MFB_SRC_RDY    => rx_gen_eth_mfb_src_rdy   ,
        ETH_MFB_DST_RDY    => rx_gen_eth_mfb_dst_rdy
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX Generator
    -- -------------------------------------------------------------------------

    tx_dma_gen_i : entity work.DMA_MFB_GENERATOR
    generic map(
        REGIONS        => REGIONS        ,
        REGION_SIZE    => REGION_SIZE    ,
        BLOCK_SIZE     => BLOCK_SIZE     ,
        ITEM_WIDTH     => ITEM_WIDTH     ,
        PKT_MTU        => PKT_MTU        ,
        DMA_CHANNELS   => TX_DMA_CHANNELS,
        NPP_HDR_SIZE   => NPP_HDR_SIZE   ,
        HDR_META_WIDTH => HDR_META_WIDTH ,
        HDR_INS_EN     => false          ,
        SAME_CLK       => true           ,
        MI_PIPE_EN     => false          ,
        DEVICE         => DEVICE
    )
    port map(
        MI_CLK   => CLK            ,
        MI_RESET => RESET          ,
        MI_DWR   => mi_pipe_dwr (3),
        MI_ADDR  => mi_pipe_addr(3),
        MI_BE    => mi_pipe_be  (3),
        MI_RD    => mi_pipe_rd  (3),
        MI_WR    => mi_pipe_wr  (3),
        MI_ARDY  => mi_pipe_ardy(3),
        MI_DRD   => mi_pipe_drd (3),
        MI_DRDY  => mi_pipe_drdy(3),

        CLK                => CLK  ,
        RESET              => RESET,

        INSTR_MVB_LEN      => tx_gen_instr_mvb_len     ,
        INSTR_MVB_CHANNEL  => tx_gen_instr_mvb_channel ,
        INSTR_MVB_HDR_META => tx_gen_instr_mvb_hdr_meta,
        INSTR_MVB_DISCARD  => tx_gen_instr_mvb_discard ,
        INSTR_MVB_VLD      => tx_gen_instr_mvb_vld     ,
        INSTR_MVB_SRC_RDY  => tx_gen_instr_mvb_src_rdy ,
        INSTR_MVB_DST_RDY  => tx_gen_instr_mvb_dst_rdy ,
        ETH_MFB_DATA       => tx_gen_eth_mfb_data      ,
        ETH_MFB_SOF        => tx_gen_eth_mfb_sof       ,
        ETH_MFB_EOF        => tx_gen_eth_mfb_eof       ,
        ETH_MFB_SOF_POS    => tx_gen_eth_mfb_sof_pos   ,
        ETH_MFB_EOF_POS    => tx_gen_eth_mfb_eof_pos   ,
        ETH_MFB_SRC_RDY    => tx_gen_eth_mfb_src_rdy   ,
        ETH_MFB_DST_RDY    => tx_gen_eth_mfb_dst_rdy
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RX Frame Player
    -- -------------------------------------------------------------------------

    rx_dma_plr_i : entity work.MFB_FRAME_PLAYER
    generic map(
        REGIONS        => REGIONS    ,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE ,
        ITEM_WIDTH     => ITEM_WIDTH ,
        FIFO_DEPTH     => PLAYER_FIFO_DEPTH
    )
    port map(
        CLK        => CLK  ,
        RST        => RESET,

        MI_DWR     => mi_pipe_dwr (4),
        MI_ADDR    => mi_pipe_addr(4),
        MI_BE      => mi_pipe_be  (4),
        MI_RD      => mi_pipe_rd  (4),
        MI_WR      => mi_pipe_wr  (4),
        MI_ARDY    => mi_pipe_ardy(4),
        MI_DRD     => mi_pipe_drd (4),
        MI_DRDY    => mi_pipe_drdy(4),

        TX_DATA    => rx_plr_eth_mfb_data   ,
        TX_SOF     => rx_plr_eth_mfb_sof    ,
        TX_EOF     => rx_plr_eth_mfb_eof    ,
        TX_SOF_POS => rx_plr_eth_mfb_sof_pos,
        TX_EOF_POS => rx_plr_eth_mfb_eof_pos,
        TX_SRC_RDY => rx_plr_eth_mfb_src_rdy,
        TX_DST_RDY => rx_plr_eth_mfb_dst_rdy
    );

    -- TODO: RX Frame Player won't work without realistic Instructions!!
    rx_plr_instr_mvb_len      <= (others => '0');
    rx_plr_instr_mvb_channel  <= (others => '0');
    rx_plr_instr_mvb_hdr_meta <= (others => '0');
    rx_plr_instr_mvb_discard  <= (others => '0');
    rx_plr_instr_mvb_vld      <= rx_plr_eth_mfb_sof;
    rx_plr_instr_mvb_src_rdy  <= or rx_plr_instr_mvb_vld;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX Frame Player
    -- -------------------------------------------------------------------------

    tx_dma_plr_i : entity work.MFB_FRAME_PLAYER
    generic map(
        REGIONS        => REGIONS    ,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => BLOCK_SIZE ,
        ITEM_WIDTH     => ITEM_WIDTH ,
        FIFO_DEPTH     => PLAYER_FIFO_DEPTH
    )
    port map(
        CLK        => CLK  ,
        RST        => RESET,

        MI_DWR     => mi_pipe_dwr (5),
        MI_ADDR    => mi_pipe_addr(5),
        MI_BE      => mi_pipe_be  (5),
        MI_RD      => mi_pipe_rd  (5),
        MI_WR      => mi_pipe_wr  (5),
        MI_ARDY    => mi_pipe_ardy(5),
        MI_DRD     => mi_pipe_drd (5),
        MI_DRDY    => mi_pipe_drdy(5),

        TX_DATA    => tx_plr_eth_mfb_data   ,
        TX_SOF     => tx_plr_eth_mfb_sof    ,
        TX_EOF     => tx_plr_eth_mfb_eof    ,
        TX_SOF_POS => tx_plr_eth_mfb_sof_pos,
        TX_EOF_POS => tx_plr_eth_mfb_eof_pos,
        TX_SRC_RDY => tx_plr_eth_mfb_src_rdy,
        TX_DST_RDY => tx_plr_eth_mfb_dst_rdy
    );

    tx_plr_instr_mvb_len      <= (others => '0');
    tx_plr_instr_mvb_channel  <= (others => '0');
    tx_plr_instr_mvb_hdr_meta <= (others => '0');
    tx_plr_instr_mvb_discard  <= (others => '0');
    tx_plr_instr_mvb_vld      <= tx_plr_eth_mfb_sof;
    tx_plr_instr_mvb_src_rdy  <= or tx_plr_instr_mvb_vld;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RX_DMA_CHANNELS/TX_DMA_CHANNELS conversion
    -- -------------------------------------------------------------------------

    chan_conv_gen : for i in 0 to REGIONS-1 generate
        -- resize_right() is used, so that the packet are evenly distributed on all DMA Endpoints when RX_DMA_CHANNELS>TX_DMA_CHANNELS
        DMA_TX_MVB_C_CH((i+1)*log2(RX_DMA_CHANNELS)-1 downto i*log2(RX_DMA_CHANNELS)) <= std_logic_vector(resize_right(unsigned(DMA_TX_MVB_CHANNEL((i+1)*log2(TX_DMA_CHANNELS)-1 downto i*log2(TX_DMA_CHANNELS))),log2(RX_DMA_CHANNELS)));
        ETH_RX_MVB_C_CH((i+1)*log2(TX_DMA_CHANNELS)-1 downto i*log2(TX_DMA_CHANNELS)) <= std_logic_vector(resize_right(unsigned(ETH_RX_MVB_CHANNEL((i+1)*log2(RX_DMA_CHANNELS)-1 downto i*log2(RX_DMA_CHANNELS))),log2(TX_DMA_CHANNELS)));
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RX Generator/Frame Player MUX
    -- Frame Player not ready! (TODO: DMA headers)
    -- -------------------------------------------------------------------------

    -- MVB Instructions
    rx_mvb_len      <= ETH_RX_MVB_LEN       when rx_gen_mux_sel_reg="00" else
                       rx_gen_instr_mvb_len when rx_gen_mux_sel_reg="01" else
                       rx_plr_instr_mvb_len;

    rx_mvb_channel  <= ETH_RX_MVB_CHANNEL       when rx_gen_mux_sel_reg="00" else
                       rx_gen_instr_mvb_channel when rx_gen_mux_sel_reg="01" else
                       rx_plr_instr_mvb_channel;

    rx_mvb_hdr_meta <= ETH_RX_MVB_HDR_META       when rx_gen_mux_sel_reg="00" else
                       rx_gen_instr_mvb_hdr_meta when rx_gen_mux_sel_reg="01" else
                       rx_plr_instr_mvb_hdr_meta;

    rx_mvb_discard  <= ETH_RX_MVB_DISCARD       when rx_gen_mux_sel_reg="00" else
                       rx_gen_instr_mvb_discard when rx_gen_mux_sel_reg="01" else
                       rx_plr_instr_mvb_discard;

    rx_mvb_vld      <= ETH_RX_MVB_VLD       when rx_gen_mux_sel_reg="00" else
                       rx_gen_instr_mvb_vld when rx_gen_mux_sel_reg="01" else
                       rx_plr_instr_mvb_vld;

    rx_mvb_src_rdy  <= ETH_RX_MVB_SRC_RDY and ETH_RX_MVB_DST_RDY_1 when rx_gen_mux_sel_reg="00" else
                       rx_gen_instr_mvb_src_rdy                    when rx_gen_mux_sel_reg="01" else
                       rx_plr_instr_mvb_src_rdy;

    ETH_RX_MVB_DST_RDY_0     <= rx_mvb_dst_rdy when rx_gen_mux_sel_reg="00" else '1';
    rx_gen_instr_mvb_dst_rdy <= rx_mvb_dst_rdy when rx_gen_mux_sel_reg="01" else '1';

    -- MFB Eth frames
    rx_mfb_data    <= ETH_RX_MFB_DATA     when rx_gen_mux_sel_reg="00" else
                      rx_gen_eth_mfb_data when rx_gen_mux_sel_reg="01" else
                      rx_plr_eth_mfb_data;

    rx_mfb_sof     <= ETH_RX_MFB_SOF     when rx_gen_mux_sel_reg="00" else
                      rx_gen_eth_mfb_sof when rx_gen_mux_sel_reg="01" else
                      rx_plr_eth_mfb_sof;

    rx_mfb_eof     <= ETH_RX_MFB_EOF     when rx_gen_mux_sel_reg="00" else
                      rx_gen_eth_mfb_eof when rx_gen_mux_sel_reg="01" else
                      rx_plr_eth_mfb_eof;

    rx_mfb_sof_pos <= ETH_RX_MFB_SOF_POS     when rx_gen_mux_sel_reg="00" else
                      rx_gen_eth_mfb_sof_pos when rx_gen_mux_sel_reg="01" else
                      rx_plr_eth_mfb_sof_pos;

    rx_mfb_eof_pos <= ETH_RX_MFB_EOF_POS     when rx_gen_mux_sel_reg="00" else
                      rx_gen_eth_mfb_eof_pos when rx_gen_mux_sel_reg="01" else
                      rx_plr_eth_mfb_eof_pos;

    rx_mfb_src_rdy <= ETH_RX_MFB_SRC_RDY and ETH_RX_MFB_DST_RDY_1 when rx_gen_mux_sel_reg="00" else
                      rx_gen_eth_mfb_src_rdy                      when rx_gen_mux_sel_reg="01" else
                      rx_plr_eth_mfb_src_rdy;

    ETH_RX_MFB_DST_RDY_0   <= rx_mfb_dst_rdy when rx_gen_mux_sel_reg="00" else '1';
    rx_gen_eth_mfb_dst_rdy <= rx_mfb_dst_rdy when rx_gen_mux_sel_reg="01" else '1';
    rx_plr_eth_mfb_dst_rdy <= rx_mfb_dst_rdy when rx_gen_mux_sel_reg="10" else '1';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX Generator/Frame Player MUX
    -- -------------------------------------------------------------------------

    -- MVB Instructions
    tx_mvb_len      <= DMA_TX_MVB_LEN       when tx_gen_mux_sel_reg="00" else
                       tx_gen_instr_mvb_len when tx_gen_mux_sel_reg="01" else
                       tx_plr_instr_mvb_len;

    tx_mvb_channel  <= DMA_TX_MVB_CHANNEL       when tx_gen_mux_sel_reg="00" else
                       tx_gen_instr_mvb_channel when tx_gen_mux_sel_reg="01" else
                       tx_plr_instr_mvb_channel;

    tx_mvb_hdr_meta <= DMA_TX_MVB_HDR_META       when tx_gen_mux_sel_reg="00" else
                       tx_gen_instr_mvb_hdr_meta when tx_gen_mux_sel_reg="01" else
                       tx_plr_instr_mvb_hdr_meta;

    tx_mvb_vld      <= DMA_TX_MVB_VLD       when tx_gen_mux_sel_reg="00" else
                       tx_gen_instr_mvb_vld when tx_gen_mux_sel_reg="01" else
                       tx_plr_instr_mvb_vld;

    tx_mvb_src_rdy  <= DMA_TX_MVB_SRC_RDY and DMA_TX_MVB_DST_RDY_1 when tx_gen_mux_sel_reg="00" else
                       tx_gen_instr_mvb_src_rdy                    when tx_gen_mux_sel_reg="01" else
                       tx_plr_instr_mvb_src_rdy;

    DMA_TX_MVB_DST_RDY_0     <= tx_mvb_dst_rdy when tx_gen_mux_sel_reg="00" else '1';
    tx_gen_instr_mvb_dst_rdy <= tx_mvb_dst_rdy when tx_gen_mux_sel_reg="01" else '1';

    -- MFB Eth frames
    tx_mfb_data    <= DMA_TX_MFB_DATA     when tx_gen_mux_sel_reg="00" else
                      tx_gen_eth_mfb_data when tx_gen_mux_sel_reg="01" else
                      tx_plr_eth_mfb_data;

    tx_mfb_sof     <= DMA_TX_MFB_SOF     when tx_gen_mux_sel_reg="00" else
                      tx_gen_eth_mfb_sof when tx_gen_mux_sel_reg="01" else
                      tx_plr_eth_mfb_sof;

    tx_mfb_eof     <= DMA_TX_MFB_EOF     when tx_gen_mux_sel_reg="00" else
                      tx_gen_eth_mfb_eof when tx_gen_mux_sel_reg="01" else
                      tx_plr_eth_mfb_eof;

    tx_mfb_sof_pos <= DMA_TX_MFB_SOF_POS     when tx_gen_mux_sel_reg="00" else
                      tx_gen_eth_mfb_sof_pos when tx_gen_mux_sel_reg="01" else
                      tx_plr_eth_mfb_sof_pos;

    tx_mfb_eof_pos <= DMA_TX_MFB_EOF_POS     when tx_gen_mux_sel_reg="00" else
                      tx_gen_eth_mfb_eof_pos when tx_gen_mux_sel_reg="01" else
                      tx_plr_eth_mfb_eof_pos;

    tx_mfb_src_rdy <= DMA_TX_MFB_SRC_RDY and DMA_TX_MFB_DST_RDY_1 when tx_gen_mux_sel_reg="00" else
                      tx_gen_eth_mfb_src_rdy                      when tx_gen_mux_sel_reg="01" else
                      tx_plr_eth_mfb_src_rdy;

    DMA_TX_MFB_DST_RDY_0   <= tx_mfb_dst_rdy when tx_gen_mux_sel_reg="00" else '1';
    tx_gen_eth_mfb_dst_rdy <= tx_mfb_dst_rdy when tx_gen_mux_sel_reg="01" else '1';
    tx_plr_eth_mfb_dst_rdy <= tx_mfb_dst_rdy when tx_gen_mux_sel_reg="10" else '1';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RX Loopback MUX
    -- -------------------------------------------------------------------------

    rx_loop_mvb_len      <= rx_mvb_len      when rx_loop_mux_sel_reg='0' else DMA_TX_MVB_LEN;
    rx_loop_mvb_channel  <= rx_mvb_channel  when rx_loop_mux_sel_reg='0' else DMA_TX_MVB_C_CH;
    rx_loop_mvb_hdr_meta <= rx_mvb_hdr_meta when rx_loop_mux_sel_reg='0' else DMA_TX_MVB_HDR_META;
    rx_loop_mvb_discard  <= rx_mvb_discard  when rx_loop_mux_sel_reg='0' else (others => '0');
    rx_loop_mvb_vld      <= rx_mvb_vld      when rx_loop_mux_sel_reg='0' else DMA_TX_MVB_VLD;
    rx_loop_mvb_src_rdy  <= rx_mvb_src_rdy  when rx_loop_mux_sel_reg='0' else DMA_TX_MVB_SRC_RDY and DMA_TX_MVB_DST_RDY_0;

    rx_mvb_dst_rdy       <= rx_loop_mvb_dst_rdy when rx_loop_mux_sel_reg='0' else '1';
    DMA_TX_MVB_DST_RDY_1 <= rx_loop_mvb_dst_rdy when rx_loop_mux_sel_reg='1' else '1';

    rx_loop_mfb_data    <= rx_mfb_data    when rx_loop_mux_sel_reg='0' else DMA_TX_MFB_DATA;
    rx_loop_mfb_sof     <= rx_mfb_sof     when rx_loop_mux_sel_reg='0' else DMA_TX_MFB_SOF;
    rx_loop_mfb_eof     <= rx_mfb_eof     when rx_loop_mux_sel_reg='0' else DMA_TX_MFB_EOF;
    rx_loop_mfb_sof_pos <= rx_mfb_sof_pos when rx_loop_mux_sel_reg='0' else DMA_TX_MFB_SOF_POS;
    rx_loop_mfb_eof_pos <= rx_mfb_eof_pos when rx_loop_mux_sel_reg='0' else DMA_TX_MFB_EOF_POS;
    rx_loop_mfb_src_rdy <= rx_mfb_src_rdy when rx_loop_mux_sel_reg='0' else DMA_TX_MFB_SRC_RDY and DMA_TX_MFB_DST_RDY_0;

    rx_mfb_dst_rdy       <= rx_loop_mfb_dst_rdy when rx_loop_mux_sel_reg='0' else '1';
    DMA_TX_MFB_DST_RDY_1 <= rx_loop_mfb_dst_rdy when rx_loop_mux_sel_reg='1' else '1';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX Loopback MUX
    -- -------------------------------------------------------------------------

    tx_loop_mvb_len      <= tx_mvb_len      when tx_loop_mux_sel_reg='0' else ETH_RX_MVB_LEN;
    tx_loop_mvb_channel  <= tx_mvb_channel  when tx_loop_mux_sel_reg='0' else ETH_RX_MVB_C_CH;
    tx_loop_mvb_hdr_meta <= tx_mvb_hdr_meta when tx_loop_mux_sel_reg='0' else ETH_RX_MVB_HDR_META;
    tx_loop_mvb_vld      <= tx_mvb_vld      when tx_loop_mux_sel_reg='0' else ETH_RX_MVB_VLD;
    tx_loop_mvb_src_rdy  <= tx_mvb_src_rdy  when tx_loop_mux_sel_reg='0' else ETH_RX_MVB_SRC_RDY and ETH_RX_MVB_DST_RDY_0;

    tx_mvb_dst_rdy       <= tx_loop_mvb_dst_rdy when tx_loop_mux_sel_reg='0' else '1';
    ETH_RX_MVB_DST_RDY_1 <= tx_loop_mvb_dst_rdy when tx_loop_mux_sel_reg='1' else '1';

    tx_loop_mfb_data    <= tx_mfb_data    when tx_loop_mux_sel_reg='0' else ETH_RX_MFB_DATA;
    tx_loop_mfb_sof     <= tx_mfb_sof     when tx_loop_mux_sel_reg='0' else ETH_RX_MFB_SOF;
    tx_loop_mfb_eof     <= tx_mfb_eof     when tx_loop_mux_sel_reg='0' else ETH_RX_MFB_EOF;
    tx_loop_mfb_sof_pos <= tx_mfb_sof_pos when tx_loop_mux_sel_reg='0' else ETH_RX_MFB_SOF_POS;
    tx_loop_mfb_eof_pos <= tx_mfb_eof_pos when tx_loop_mux_sel_reg='0' else ETH_RX_MFB_EOF_POS;
    tx_loop_mfb_src_rdy <= tx_mfb_src_rdy when tx_loop_mux_sel_reg='0' else ETH_RX_MFB_SRC_RDY and ETH_RX_MFB_DST_RDY_0;

    tx_mfb_dst_rdy       <= tx_loop_mfb_dst_rdy when tx_loop_mux_sel_reg='0' else '1';
    ETH_RX_MFB_DST_RDY_1 <= tx_loop_mfb_dst_rdy when tx_loop_mux_sel_reg='1' else '1';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Output DST_RDY
    -- -------------------------------------------------------------------------

    DMA_TX_MVB_DST_RDY <= DMA_TX_MVB_DST_RDY_0 and DMA_TX_MVB_DST_RDY_1;
    DMA_TX_MFB_DST_RDY <= DMA_TX_MFB_DST_RDY_0 and DMA_TX_MFB_DST_RDY_1;
    ETH_RX_MVB_DST_RDY <= ETH_RX_MVB_DST_RDY_0 and ETH_RX_MVB_DST_RDY_1;
    ETH_RX_MFB_DST_RDY <= ETH_RX_MFB_DST_RDY_0 and ETH_RX_MFB_DST_RDY_1;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- RX FIFO
    -- -------------------------------------------------------------------------

    rx_mvb_fifo_i : entity work.MVB_FIFOX
    generic map(
        ITEMS               => REGIONS,
        ITEM_WIDTH          => log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1,
        FIFO_DEPTH          => 512    ,
        RAM_TYPE            => "AUTO" ,
        DEVICE              => DEVICE ,
        ALMOST_FULL_OFFSET  => 0      ,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DATA    => rx_loop_mvb_data   ,
        RX_VLD     => rx_loop_mvb_vld    ,
        RX_SRC_RDY => rx_loop_mvb_src_rdy,
        RX_DST_RDY => rx_loop_mvb_dst_rdy,

        TX_DATA    => DMA_RX_MVB_DATA    ,
        TX_VLD     => DMA_RX_MVB_VLD     ,
        TX_SRC_RDY => DMA_RX_MVB_SRC_RDY ,
        TX_DST_RDY => DMA_RX_MVB_DST_RDY ,

        STATUS     => open               ,
        AFULL      => open               ,
        AEMPTY     => open
    );

    -- RX MVB FIFO input ----
    rx_loop_mvb_len_arr      <= slv_array_deser(rx_loop_mvb_len     ,REGIONS);
    rx_loop_mvb_channel_arr  <= slv_array_deser(rx_loop_mvb_channel ,REGIONS);
    rx_loop_mvb_hdr_meta_arr <= slv_array_deser(rx_loop_mvb_hdr_meta,REGIONS);
    rx_loop_mvb_discard_arr  <= slv_array_deser(rx_loop_mvb_discard ,REGIONS);

    rx_loop_mvb_data_gen : for i in 0 to REGIONS-1 generate
        rx_loop_mvb_data_arr(i) <= rx_loop_mvb_len_arr     (i)
                                  &rx_loop_mvb_channel_arr (i)
                                  &rx_loop_mvb_hdr_meta_arr(i)
                                  &rx_loop_mvb_discard_arr (i);
    end generate;

    rx_loop_mvb_data <= slv_array_ser(rx_loop_mvb_data_arr);
    -------------------------

    -- RX MVB FIFO output ---
    DMA_RX_MVB_DATA_arr <= slv_array_deser(DMA_RX_MVB_DATA,REGIONS);

    dma_rx_mvb_data_gen : for i in 0 to REGIONS-1 generate
    begin
        DMA_RX_MVB_LEN_arr     (i) <= DMA_RX_MVB_DATA_arr(i)(log2(PKT_MTU+1)+log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1 downto log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1);
        DMA_RX_MVB_CHANNEL_arr (i) <= DMA_RX_MVB_DATA_arr(i)(                log2(RX_DMA_CHANNELS)+HDR_META_WIDTH+1-1 downto                       HDR_META_WIDTH+1);
        DMA_RX_MVB_HDR_META_arr(i) <= DMA_RX_MVB_DATA_arr(i)(                                      HDR_META_WIDTH+1-1 downto                                      1);
        DMA_RX_MVB_DISCARD     (i) <= DMA_RX_MVB_DATA_arr(i)(0);
    end generate;

    DMA_RX_MVB_LEN      <= slv_array_ser(DMA_RX_MVB_LEN_arr     );
    DMA_RX_MVB_CHANNEL  <= slv_array_ser(DMA_RX_MVB_CHANNEL_arr );
    DMA_RX_MVB_HDR_META <= slv_array_ser(DMA_RX_MVB_HDR_META_arr);
    -------------------------

    rx_mfb_fifo_i : entity work.MFB_FIFOX
    generic map(
        REGIONS             => REGIONS    ,
        REGION_SIZE         => REGION_SIZE,
        BLOCK_SIZE          => BLOCK_SIZE ,
        ITEM_WIDTH          => ITEM_WIDTH ,
        FIFO_DEPTH          => 512        ,
        RAM_TYPE            => "AUTO"     ,
        DEVICE              => DEVICE     ,
        ALMOST_FULL_OFFSET  => 0          ,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        CLK         => CLK  ,
        RST         => RESET,

        RX_DATA     => rx_loop_mfb_data   ,
        RX_SOF      => rx_loop_mfb_sof    ,
        RX_EOF      => rx_loop_mfb_eof    ,
        RX_SOF_POS  => rx_loop_mfb_sof_pos,
        RX_EOF_POS  => rx_loop_mfb_eof_pos,
        RX_SRC_RDY  => rx_loop_mfb_src_rdy,
        RX_DST_RDY  => rx_loop_mfb_dst_rdy,

        TX_DATA     => DMA_RX_MFB_DATA    ,
        TX_SOF      => DMA_RX_MFB_SOF     ,
        TX_EOF      => DMA_RX_MFB_EOF     ,
        TX_SOF_POS  => DMA_RX_MFB_SOF_POS ,
        TX_EOF_POS  => DMA_RX_MFB_EOF_POS ,
        TX_SRC_RDY  => DMA_RX_MFB_SRC_RDY ,
        TX_DST_RDY  => DMA_RX_MFB_DST_RDY ,

        FIFO_STATUS => open               ,
        FIFO_AFULL  => open               ,
        FIFO_AEMPTY => open
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX FIFO
    -- -------------------------------------------------------------------------

    tx_mvb_fifo_i : entity work.MVB_FIFOX
    generic map(
        ITEMS               => REGIONS,
        ITEM_WIDTH          => log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH,
        FIFO_DEPTH          => 512    ,
        RAM_TYPE            => "AUTO" ,
        DEVICE              => DEVICE ,
        ALMOST_FULL_OFFSET  => 0      ,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DATA    => tx_loop_mvb_data   ,
        RX_VLD     => tx_loop_mvb_vld    ,
        RX_SRC_RDY => tx_loop_mvb_src_rdy,
        RX_DST_RDY => tx_loop_mvb_dst_rdy,

        TX_DATA    => ETH_TX_MVB_DATA    ,
        TX_VLD     => ETH_TX_MVB_VLD     ,
        TX_SRC_RDY => ETH_TX_MVB_SRC_RDY ,
        TX_DST_RDY => ETH_TX_MVB_DST_RDY ,

        STATUS     => open               ,
        AFULL      => open               ,
        AEMPTY     => open
    );

    -- TX MVB FIFO input ----
    tx_loop_mvb_len_arr      <= slv_array_deser(tx_loop_mvb_len     ,REGIONS);
    tx_loop_mvb_channel_arr  <= slv_array_deser(tx_loop_mvb_channel ,REGIONS);
    tx_loop_mvb_hdr_meta_arr <= slv_array_deser(tx_loop_mvb_hdr_meta,REGIONS);

    tx_loop_mvb_data_gen : for i in 0 to REGIONS-1 generate
        tx_loop_mvb_data_arr(i) <= tx_loop_mvb_len_arr     (i)
                                  &tx_loop_mvb_channel_arr (i)
                                  &tx_loop_mvb_hdr_meta_arr(i);
    end generate;

    tx_loop_mvb_data <= slv_array_ser(tx_loop_mvb_data_arr);
    -------------------------

    -- TX MVB FIFO output ---
    ETH_TX_MVB_DATA_arr <= slv_array_deser(ETH_TX_MVB_DATA,REGIONS);

    dma_tx_mvb_data_gen : for i in 0 to REGIONS-1 generate
    begin
        ETH_TX_MVB_LEN_arr     (i) <= ETH_TX_MVB_DATA_arr(i)(log2(PKT_MTU+1)+log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1 downto log2(TX_DMA_CHANNELS)+HDR_META_WIDTH);
        ETH_TX_MVB_CHANNEL_arr (i) <= ETH_TX_MVB_DATA_arr(i)(                log2(TX_DMA_CHANNELS)+HDR_META_WIDTH-1 downto                       HDR_META_WIDTH);
        ETH_TX_MVB_HDR_META_arr(i) <= ETH_TX_MVB_DATA_arr(i)(                                      HDR_META_WIDTH-1 downto                                    0);
    end generate;

    ETH_TX_MVB_LEN      <= slv_array_ser(ETH_TX_MVB_LEN_arr     );
    ETH_TX_MVB_CHANNEL  <= slv_array_ser(ETH_TX_MVB_CHANNEL_arr );
    ETH_TX_MVB_HDR_META <= slv_array_ser(ETH_TX_MVB_HDR_META_arr);
    -------------------------

    tx_mfb_fifo_i : entity work.MFB_FIFOX
    generic map(
        REGIONS             => REGIONS    ,
        REGION_SIZE         => REGION_SIZE,
        BLOCK_SIZE          => BLOCK_SIZE ,
        ITEM_WIDTH          => ITEM_WIDTH ,
        FIFO_DEPTH          => 512        ,
        RAM_TYPE            => "AUTO"     ,
        DEVICE              => DEVICE     ,
        ALMOST_FULL_OFFSET  => 0          ,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map(
        CLK         => CLK  ,
        RST         => RESET,

        RX_DATA     => tx_loop_mfb_data   ,
        RX_SOF      => tx_loop_mfb_sof    ,
        RX_EOF      => tx_loop_mfb_eof    ,
        RX_SOF_POS  => tx_loop_mfb_sof_pos,
        RX_EOF_POS  => tx_loop_mfb_eof_pos,
        RX_SRC_RDY  => tx_loop_mfb_src_rdy,
        RX_DST_RDY  => tx_loop_mfb_dst_rdy,

        TX_DATA     => ETH_TX_MFB_DATA    ,
        TX_SOF      => ETH_TX_MFB_SOF     ,
        TX_EOF      => ETH_TX_MFB_EOF     ,
        TX_SOF_POS  => ETH_TX_MFB_SOF_POS ,
        TX_EOF_POS  => ETH_TX_MFB_EOF_POS ,
        TX_SRC_RDY  => ETH_TX_MFB_SRC_RDY ,
        TX_DST_RDY  => ETH_TX_MFB_DST_RDY ,

        FIFO_STATUS => open               ,
        FIFO_AFULL  => open               ,
        FIFO_AEMPTY => open
    );

    -- -------------------------------------------------------------------------

end generate;

end architecture;
