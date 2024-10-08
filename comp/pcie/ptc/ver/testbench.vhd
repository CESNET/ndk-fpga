-- testbench.vhd: Testbench
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields
use work.basics_test_pkg.all;
use work.test_pkg.all;
use std.env.stop;
use STD.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

   -- Synchronization
   signal clk                                : std_logic;
   signal clk_dma                            : std_logic;
   signal reset                              : std_logic := '1';

   signal new_dma_clk : std_logic := '0';
   signal dma_clk_used : std_logic := '0';

   -- uut I/O

   signal s_up_mvb_data    : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0) := (others => (others => '0')); -- MVB items
   signal s_up_mvb_vld     : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS                -1 downto 0) := (others => (others => '0')); -- MVB item valid
   signal s_up_mvb_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');
   signal s_up_mvb_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');

   signal s_up_mfb_data    : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0) := (others => (others => '0')); -- MFB data word
   signal s_up_mfb_sof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0) := (others => (others => '0'));                                                     -- MFB region contains start of frame
   signal s_up_mfb_eof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0) := (others => (others => '0'));                                                     -- MFB region contains end of frame
   signal s_up_mfb_sof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0) := (others => (others => '0'));                        -- address of block of region's SOF
   signal s_up_mfb_eof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0) := (others => (others => '0'));      -- address of item of region's EOF
   signal s_up_mfb_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');
   signal s_up_mfb_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');

   signal s_rq_tdata     : std_logic_vector(MFB_UP_DATA_WIDTH-1 downto 0) := (others => '0');

   signal s_rq_tuser     : std_logic_vector(RQ_TUSER_WIDTH-1 downto 0) := (others => '0');
   signal s_rq_tlast     : std_logic := '0';
   signal s_rq_tkeep     : std_logic_vector(MFB_UP_DATA_WIDTH/32-1 downto 0) := (others => '0');
   signal s_rq_tready    : std_logic := '1';
   signal s_rq_tvalid    : std_logic := '0';

   signal s_rq_mvb_hdr_data    : std_logic_vector(MFB_UP_REGIONS*PCIE_UPHDR_WIDTH-1 downto 0);
   signal s_rq_mvb_prefix_data : std_logic_vector(MFB_UP_REGIONS*PCIE_PREFIX_WIDTH-1 downto 0); -- valid together with HDR_DATA
   signal s_rq_mvb_vld         : std_logic_vector(MFB_UP_REGIONS-1 downto 0);

   signal s_rq_mfb_data    : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0) := (others => '0'); -- MFB data word
   signal s_rq_mfb_sof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0) := (others => '0');                                                     -- MFB region contains start of frame
   signal s_rq_mfb_eof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0) := (others => '0');                                                     -- MFB region contains end of frame
   signal s_rq_mfb_sof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0) := (others => '0');                        -- address of block of region's SOF
   signal s_rq_mfb_eof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0) := (others => '0');      -- address of item of region's EOF
   signal s_rq_mfb_src_rdy : std_logic := '0';
   signal s_rq_mfb_dst_rdy : std_logic := '0';

   signal s_rc_mvb_hdr_data    : std_logic_vector(MFB_DOWN_REGIONS*PCIE_DOWNHDR_WIDTH-1 downto 0);
   signal s_rc_mvb_prefix_data : std_logic_vector(MFB_DOWN_REGIONS*PCIE_PREFIX_WIDTH-1 downto 0); -- valid together with HDR_DATA
   signal s_rc_mvb_vld         : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);

   signal s_rc_mfb_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0) := (others => '0'); -- MFB data word
   signal s_rc_mfb_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0) := (others => '0');                                                           -- MFB region contains start of frame
   signal s_rc_mfb_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0) := (others => '0');                                                           -- MFB region contains end of frame
   signal s_rc_mfb_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0) := (others => '0');                            -- address of block of region's SOF
   signal s_rc_mfb_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0) := (others => '0');        -- address of item of region's EOF
   signal s_rc_mfb_src_rdy : std_logic := '0';
   signal s_rc_mfb_dst_rdy : std_logic := '0';

   signal s_rc_tdata     : std_logic_vector(MFB_DOWN_DATA_WIDTH-1 downto 0) := (others => '0');

   signal s_rc_tuser     : std_logic_vector(RC_TUSER_WIDTH-1 downto 0);

   signal s_rc_tlast         : std_logic := '0';
   signal s_rc_tkeep         : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH/32-1 downto 0) := (others => '0');
   signal s_rc_tvalid        : std_logic := '0';
   signal s_rc_tready        : std_logic := '0';

   signal s_down_mvb_data    : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0) := (others => (others => '0')); -- MVB items
   signal s_down_mvb_vld     : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS                  -1 downto 0) := (others => (others => '0')); -- MVB item valid
   signal s_down_mvb_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');
   signal s_down_mvb_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');

   signal s_down_mfb_data    : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0) := (others => (others => '0')); -- MFB data word
   signal s_down_mfb_sof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0) := (others => (others => '0'));                                                           -- MFB region contains start of frame
   signal s_down_mfb_eof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0) := (others => (others => '0'));                                                           -- MFB region contains end of frame
   signal s_down_mfb_sof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0) := (others => (others => '0'));                            -- address of block of region's SOF
   signal s_down_mfb_eof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0) := (others => (others => '0'));        -- address of item of region's EOF
   signal s_down_mfb_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');
   signal s_down_mfb_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0) := (others => '0');

   signal s_rcb_size         : std_logic := '0';
   signal s_tag_assign       : std_logic_vector(MVB_UP_ITEMS*PCIE_TAG_WIDTH-1 downto 0) := (others => '0');
   signal s_tag_assign_vld   : std_logic_vector(MVB_UP_ITEMS               -1 downto 0) := (others => '0');

   -- uut I/O converted

   signal up_mvb_i_hdr           : slv_array_2d_t(DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);
   signal up_mvb_i_hdr_type      : str_array_2d_t(DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0)(2 downto 1);
   signal up_mvb_i_hdr_length    : i_array_2d_t  (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0);
   signal up_mvb_i_hdr_address   : slv_array_2d_t(DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0);
   signal up_mvb_i_hdr_tag       : i_array_2d_t  (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0);
   signal up_mvb_i_hdr_id        : i_array_2d_t  (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0);

   signal up_mfb_i_data          : slv_array_2d_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0)(DMA_MFB_UP_DATA_WIDTH/DMA_MFB_UP_REGIONS-1 downto 0);
   signal up_mfb_i_sof_pos       : i_array_2d_t  (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0);
   signal up_mfb_i_eof_pos       : i_array_2d_t  (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0);

   signal down_mvb_i_hdr           : slv_array_2d_t(DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS-1 downto 0)(DMA_DOWNHDR_WIDTH-1 downto 0);
   signal down_mvb_i_hdr_length    : i_array_2d_t  (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS-1 downto 0);
   signal down_mvb_i_hdr_completed : slv_array_t   (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS-1 downto 0);
   signal down_mvb_i_hdr_tag       : i_array_2d_t  (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS-1 downto 0);
   signal down_mvb_i_hdr_id        : i_array_2d_t  (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS-1 downto 0);

   signal down_mfb_i_data        : slv_array_2d_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0)(DMA_MFB_DOWN_DATA_WIDTH/DMA_MFB_DOWN_REGIONS-1 downto 0);
   signal down_mfb_i_sof_pos     : i_array_2d_t  (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0);
   signal down_mfb_i_eof_pos     : i_array_2d_t  (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0);

   signal rq_i_tdata          : slv_array_t     (MFB_UP_REGIONS-1 downto 0)(MFB_UP_DATA_WIDTH/MFB_UP_REGIONS-1 downto 0);
   signal rq_i_tuser_sop      : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
   signal rq_i_tuser_sop_pos  : i_array_t       (MFB_UP_REGIONS-1 downto 0);
   signal rq_i_tuser_eop      : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
   signal rq_i_tuser_eop_pos  : i_array_t       (MFB_UP_REGIONS-1 downto 0);
   signal rq_i_tuser_first_be : slv_array_t     (MFB_UP_REGIONS-1 downto 0)(4-1 downto 0);
   signal rq_i_tuser_last_be  : slv_array_t     (MFB_UP_REGIONS-1 downto 0)(4-1 downto 0);

   signal rc_i_tdata          : slv_array_t     (MFB_DOWN_REGIONS-1 downto 0)(MFB_DOWN_DATA_WIDTH/MFB_DOWN_REGIONS-1 downto 0);
   signal rc_i_tuser_sop      : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
   signal rc_i_tuser_sop_pos  : i_array_t       (MFB_DOWN_REGIONS-1 downto 0);
   signal rc_i_tuser_eop      : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
   signal rc_i_tuser_eop_pos  : i_array_t       (MFB_DOWN_REGIONS-1 downto 0);
   signal rc_i_tuser_be       : slv_array_t     (MFB_DOWN_REGIONS-1 downto 0)(MFB_DOWN_DATA_WIDTH/8/MFB_DOWN_REGIONS-1 downto 0);

   signal tag_ass_i_tag : i_array_t(MVB_UP_ITEMS-1 downto 0);

   -- test signals

   -- print line
   shared variable l : line;

   -- FIFO for generated UP MVB+MFB transactions
   shared variable up_mvb_mfb_gen_fifo : slv_fifo_array_t(DMA_PORTS-1 downto 0)
                             (fifo (max(MVB_UP_ITEMS,MFB_UP_REGIONS)*2-1 downto 0)(MVB_MFB_TRANS_WIDTH-1 downto 0)) := (others =>
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0));

   -- DMA ID and Tag free mask
   shared variable dma_idtag_free : slv_array_t(DMA_PORTS-1 downto 0)(2**(DMA_ID_WIDTH+DMA_PORT_TAG_WIDTH)-1 downto 0) := (others => (others => '1'));

   -- generated UP transactions counter
   shared variable up_trans_cntr : integer := 0;

   -- UP MVB interface
   shared variable up_mvb_i : mvb_i_arr_t(DMA_PORTS-1 downto 0)
                             (data (MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0), vld (MVB_UP_ITEMS-1 downto 0)) := (others =>
                             (data    => (others => '0'),
                              vld     => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0'));

   -- UP MFB interface
   shared variable up_mfb_i : mfb_i_arr_t(DMA_PORTS-1 downto 0)
                             (data    (DMA_MFB_UP_DATA_WIDTH-1 downto 0),
                              sof     (DMA_MFB_UP_REGIONS-1 downto 0),
                              eof     (DMA_MFB_UP_REGIONS-1 downto 0),
                              sof_pos (DMA_MFB_UP_REGIONS*MFB_UP_SOF_POS_WIDTH-1 downto 0),
                              eof_pos (DMA_MFB_UP_REGIONS*MFB_UP_EOF_POS_WIDTH-1 downto 0)) := (others =>
                             (data    => (others => '0'),
                              sof     => (others => '0'),
                              eof     => (others => '0'),
                              sof_pos => (others => '0'),
                              eof_pos => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0'));

   -- FIFO of MVB+MFB transaction send to UP
   shared variable up_send_trans_fifo : slv_fifo_array_t(DMA_PORTS-1 downto 0)
                             (fifo (VER_FIFO_SIZE*2-1 downto 0)(MVB_MFB_TRANS_WIDTH-1 downto 0)) := (others =>
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0));

   -- FIFO of ID+TAG pairs of read transactions send to UP MVB
   shared variable up_idtag_fifo : slv_fifo_array_t(DMA_PORTS-1 downto 0)
                             (fifo (VER_FIFO_SIZE*2-1 downto 0)(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto 0)) := (others =>
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0));

   -- PCIe Tag free mask
   function pcie_tag_free_init return std_logic_vector is
      variable pcie_tag_free : std_logic_vector(2**PCIE_TAG_WIDTH-1 downto 0) := (others => '1');
   begin
      if (PCIE_TAG_WIDTH=10) then -- not all Tags can be used in 10-bit configuration
          pcie_tag_free(256-1 downto 0)      := (others => '0');
          pcie_tag_free(1024-1 downto 3*256) := (others => '0');
      end if;
      return pcie_tag_free;
   end function;
   shared variable pcie_tag_free : std_logic_vector(2**PCIE_TAG_WIDTH-1 downto 0) := pcie_tag_free_init;

   -- PCIe Tag to DMA Tag mapping
   shared variable pcie_tag_to_dma_tag_map : i_array_t(2**(DMA_ID_WIDTH+DMA_TAG_WIDTH)-1 downto 0) := (others => 0);
   -- PCIe Tag to DMA ID mapping
   shared variable pcie_tag_to_dma_id_map  : i_array_t(2**(DMA_ID_WIDTH+DMA_TAG_WIDTH)-1 downto 0) := (others => 0);
   -- DIDO of correct DMA ID+TAG of transaction send DOWN
   shared variable down_idtag_fifo : slv_fifo_array_t(DMA_PORTS-1 downto 0)
                             (fifo (VER_FIFO_SIZE-1 downto 0)(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto 0)) := (others =>
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0));

   -- UP RQ AXI interface
   shared variable rq_i : rq_i_t;

   -- UP RQ MVB interface
   shared variable rq_mvb_i : mvb_i_t(data (MFB_UP_REGIONS*PCIE_UPHDR_WIDTH-1 downto 0), vld (MFB_UP_REGIONS-1 downto 0)) :=
                             (data    => (others => '0'),
                              vld     => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0');

   -- UP RQ MFB interface
   shared variable rq_mfb_i : mfb_i_t
                             (data    (MFB_UP_DATA_WIDTH-1 downto 0),
                              sof     (MFB_UP_REGIONS-1 downto 0),
                              eof     (MFB_UP_REGIONS-1 downto 0),
                              sof_pos (MFB_UP_REGIONS*MFB_UP_SOF_POS_WIDTH-1 downto 0),
                              eof_pos (MFB_UP_REGIONS*MFB_UP_EOF_POS_WIDTH-1 downto 0)) :=
                             (data    => (others => '0'),
                              sof     => (others => '0'),
                              eof     => (others => '0'),
                              sof_pos => (others => '0'),
                              eof_pos => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0');

   -- response delay FIFO before queuing to up_acc_trans_fifo
   shared variable up_acc_trans_delay_fifo : slv_array_2d_t(DOWN_RESPONSE_DELAY_MIN-1 downto 0)(MVB_UP_ITEMS-1 downto 0)(MVB_MFB_TRANS_WIDTH-1 downto 0);
   shared variable up_acc_trans_delay_vld  : slv_array_t   (DOWN_RESPONSE_DELAY_MIN-1 downto 0)(MVB_UP_ITEMS-1 downto 0) := (others => (others => '0'));
   -- FIFO of MVB+MFB read transaction accepted on UP RQ AXI
   shared variable up_acc_trans_fifo : slv_fifo_t(fifo (VER_FIFO_SIZE-1 downto 0)(MVB_MFB_TRANS_WIDTH-1 downto 0)) :=
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0);

   -- FIFO of PCIe Tags assigned on UP RQ AXI (for tag assign)
   shared variable pcie_tag_ass_fifo : slv_fifo_t(fifo (VER_FIFO_SIZE*4-1 downto 0)(PCIE_TAG_WIDTH-1 downto 0)) :=
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0);

   -- FIFO of PCIe Tags assigned on UP RQ AXI (for tag mapping)
   shared variable pcie_tag_map_fifo : slv_fifo_t(fifo (MVB_UP_ITEMS*4-1 downto 0)(PCIE_TAG_WIDTH-1 downto 0)) :=
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0);

   -- mask of responses currently being generated
   shared variable response_gen : std_logic_vector(2**PCIE_TAG_WIDTH-1 downto 0) := (others => '0');
   -- remainning length of each generated response
   shared variable response_rem_length : i_array_t(2**PCIE_TAG_WIDTH-1 downto 0) := (others => 0);
   -- address of each generated response
   shared variable response_rem_addr   : u_array_t(2**PCIE_TAG_WIDTH-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));

   -- UP RC MVB interface
   shared variable rc_mvb_i : mvb_i_t(data (MFB_DOWN_REGIONS*PCIE_DOWNHDR_WIDTH-1 downto 0), vld (MFB_DOWN_REGIONS-1 downto 0)) :=
                             (data    => (others => '0'),
                              vld     => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0');

   -- DOWN RC MFB interface
   shared variable rc_mfb_i : mfb_i_t
                             (data    (MFB_DOWN_DATA_WIDTH-1 downto 0),
                              sof     (MFB_DOWN_REGIONS-1 downto 0),
                              eof     (MFB_DOWN_REGIONS-1 downto 0),
                              sof_pos (MFB_DOWN_REGIONS*MFB_DOWN_SOF_POS_WIDTH-1 downto 0),
                              eof_pos (MFB_DOWN_REGIONS*MFB_DOWN_EOF_POS_WIDTH-1 downto 0)) :=
                             (data    => (others => '0'),
                              sof     => (others => '0'),
                              eof     => (others => '0'),
                              sof_pos => (others => '0'),
                              eof_pos => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0');

   -- DOWN RC AXI interface
   shared variable rc_i : rc_i_t;

   -- FIFO of send DOWN responses
   shared variable down_send_trans_fifo : slv_fifo_array_t(DMA_PORTS-1 downto 0)
                             (fifo (VER_FIFO_SIZE-1 downto 0)(MVB_MFB_TRANS_WIDTH-1 downto 0)) := (others =>
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0));

   -- DOWN MVB interface
   shared variable down_mvb_i : mvb_i_arr_t(DMA_PORTS-1 downto 0)
                             (data (MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0), vld (MVB_DOWN_ITEMS-1 downto 0)) := (others =>
                             (data    => (others => '0'),
                              vld     => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0'));

   -- DOWN MFB interface
   shared variable down_mfb_i : mfb_i_arr_t(DMA_PORTS-1 downto 0)
                             (data    (DMA_MFB_DOWN_DATA_WIDTH-1 downto 0),
                              sof     (DMA_MFB_DOWN_REGIONS-1 downto 0),
                              eof     (DMA_MFB_DOWN_REGIONS-1 downto 0),
                              sof_pos (DMA_MFB_DOWN_REGIONS*MFB_DOWN_SOF_POS_WIDTH-1 downto 0),
                              eof_pos (DMA_MFB_DOWN_REGIONS*MFB_DOWN_EOF_POS_WIDTH-1 downto 0)) := (others =>
                             (data    => (others => '0'),
                              sof     => (others => '0'),
                              eof     => (others => '0'),
                              sof_pos => (others => '0'),
                              eof_pos => (others => '0'),
                              src_rdy => '0',
                              dst_rdy => '0'));

   -- FIFO tag manager reserving wait for assign
   shared variable tag_reserve_fifo : slv_fifo_t(fifo (VER_FIFO_SIZE-1 downto 0)(32-1 downto 0)) :=
                             (fifo  => (others => (others => 'U')),
                              fill  => 0,
                              full  => '0',
                              empty => '1',
                              fill_max => 0,
                              fill_sum => 0,
                              fill_num => 0);

   -- NUmber of words reserved for each tag in Tag Manager
   shared variable tag_reserve     : i_array_t       (2**PCIE_TAG_WIDTH-1 downto 0) := (others => 0);
   shared variable tag_reserve_vld : std_logic_vector(2**PCIE_TAG_WIDTH-1 downto 0) := (others => '0');

   -- Transaction counters
   shared variable trans_up_send_cntr   : natural := 0;
   shared variable trans_up_recv_cntr   : natural := 0;
   shared variable trans_down_send_cntr : natural := 0;
   shared variable trans_down_recv_cntr : natural := 0;
   shared variable trans_processed_cntr : natural := 0;
   shared variable next_print_cntr      : natural := GEN_PRINT_INTERVAL;

   -- Verification statistics variables
   shared variable stat_up_trans_rd_cntr    : integer := 0;
   shared variable stat_up_trans_rd_len_min : integer := -1;
   shared variable stat_up_trans_rd_len_max : integer := 0;
   shared variable stat_up_trans_rd_len_sum : integer := 0;
   shared variable stat_up_trans_rd_len_num : integer := 0;
   shared variable stat_up_trans_rd_len_avg : integer := 0;

   shared variable stat_up_trans_wr_cntr    : integer := 0;
   shared variable stat_up_trans_wr_len_min : integer := -1;
   shared variable stat_up_trans_wr_len_max : integer := 0;
   shared variable stat_up_trans_wr_len_sum : integer := 0;
   shared variable stat_up_trans_wr_len_num : integer := 0;
   shared variable stat_up_trans_wr_len_avg : integer := 0;

   --shared variable stat_down_response_parts_min : integer := -1;
   --shared variable stat_down_response_parts_max : integer := 0;
   --shared variable stat_down_response_parts_sum : integer := 0;
   --shared variable stat_down_response_parts_num : integer := 0;
   --shared variable stat_down_response_parts_avg : integer := 0;

   --shared variable stat_down_response_delay_min : integer := -1; -- delay between read on RQ and first part of response on RC
   --shared variable stat_down_response_delay_max : integer := 0;
   --shared variable stat_down_response_delay_sum : integer := 0;
   --shared variable stat_down_response_delay_num : integer := 0;
   --shared variable stat_down_response_delay_avg : integer := 0;

   --shared variable stat_down_response_spread_min : integer := -1; -- delay between first and last part of response on RC
   --shared variable stat_down_response_spread_max : integer := 0;
   --shared variable stat_down_response_spread_sum : integer := 0;
   --shared variable stat_down_response_spread_num : integer := 0;
   --shared variable stat_down_response_spread_avg : integer := 0;

   shared variable stat_down_trans_cntr    : integer := 0;
   shared variable stat_down_trans_len_min : integer := -1;
   shared variable stat_down_trans_len_max : integer := 0;
   shared variable stat_down_trans_len_sum : integer := 0;
   shared variable stat_down_trans_len_num : integer := 0;
   shared variable stat_down_trans_len_avg : integer := 0;

   shared variable stat_pcie_tags_used_min : integer := 0;
   shared variable stat_pcie_tags_used_max : integer := 0;
   shared variable stat_pcie_tags_used_sum : integer := 0;
   shared variable stat_pcie_tags_used_num : integer := 0;
   shared variable stat_pcie_tags_used_avg : integer := 0;

   procedure write_stat is
   begin
      write(l,string'(""));writeline(output,l);
      write(l,string'("----:: Verification Statistics ::----"));writeline(output,l);
      write(l,string'("stat_up_trans_rd_cntr : " & integer'image(stat_up_trans_rd_cntr)));writeline(output,l);
      write(l,string'("stat_up_trans_rd_len_min : " & integer'image(stat_up_trans_rd_len_min) & " dwords"));writeline(output,l);
      write(l,string'("stat_up_trans_rd_len_max : " & integer'image(stat_up_trans_rd_len_max) & " dwords"));writeline(output,l);
      if (stat_up_trans_rd_len_num=0) then
         write(l,string'("stat_up_trans_rd_len_avg : " & integer'image(0) & " dwords"));writeline(output,l);
      else
         write(l,string'("stat_up_trans_rd_len_avg : " & integer'image(stat_up_trans_rd_len_sum/stat_up_trans_rd_len_num) & " dwords"));writeline(output,l);
      end if;
      write(l,string'(""));writeline(output,l);
      write(l,string'("stat_up_trans_wr_cntr : " & integer'image(stat_up_trans_wr_cntr)));writeline(output,l);
      write(l,string'("stat_up_trans_wr_len_min : " & integer'image(stat_up_trans_wr_len_min) & " dwords"));writeline(output,l);
      write(l,string'("stat_up_trans_wr_len_max : " & integer'image(stat_up_trans_wr_len_max) & " dwords"));writeline(output,l);
      if (stat_up_trans_wr_len_num=0) then
         write(l,string'("stat_up_trans_wr_len_avg : " & integer'image(0) & " dwords"));writeline(output,l);
      else
         write(l,string'("stat_up_trans_wr_len_avg : " & integer'image(stat_up_trans_wr_len_sum/stat_up_trans_wr_len_num) & " dwords"));writeline(output,l);
      end if;
      write(l,string'(""));writeline(output,l);
      write(l,string'("stat_down_trans_cntr : " & integer'image(stat_down_trans_cntr)));writeline(output,l);
      write(l,string'("stat_down_trans_len_min : " & integer'image(stat_down_trans_len_min) & " dwords"));writeline(output,l);
      write(l,string'("stat_down_trans_len_max : " & integer'image(stat_down_trans_len_max) & " dwords"));writeline(output,l);
      if (stat_down_trans_len_num=0) then
         write(l,string'("stat_down_trans_len_avg : " & integer'image(0) & " dwords"));writeline(output,l);
      else
         write(l,string'("stat_down_trans_len_avg : " & integer'image(stat_down_trans_len_sum/stat_down_trans_len_num) & " dwords"));writeline(output,l);
      end if;
      write(l,string'(""));writeline(output,l);
      write(l,string'("stat_pcie_tags_used_min : " & integer'image(stat_pcie_tags_used_min)));writeline(output,l);
      write(l,string'("stat_pcie_tags_used_max : " & integer'image(stat_pcie_tags_used_max)));writeline(output,l);
      if (stat_pcie_tags_used_num=0) then
         write(l,string'("stat_pcie_tags_used_avg : " & integer'image(0)));writeline(output,l);
      else
         write(l,string'("stat_pcie_tags_used_avg : " & integer'image(stat_pcie_tags_used_sum/stat_pcie_tags_used_num)));writeline(output,l);
      end if;

      write(l,string'(""));writeline(output,l);
   end procedure;

   procedure success_end is
   begin
      write_stat;
      write(l,string'("FIFOs statistics:"));writeline(output,l);
      write(l,string'(""));writeline(output,l);
      for d in 0 to DMA_PORTS-1 loop
         fifo_print_stats(up_mvb_mfb_gen_fifo(d),"up_mvb_mfb_gen_fifo "&to_string(d));
         fifo_print_stats(up_send_trans_fifo (d),"up_send_trans_fifo "&to_string(d));
         fifo_print_stats(up_idtag_fifo      (d),"up_idtag_fifo "&to_string(d));
         fifo_print_stats(down_idtag_fifo    (d),"down_idtag_fifo "&to_string(d));
      end loop;
      fifo_print_stats(up_acc_trans_fifo      ,"up_acc_trans_fifo");
      fifo_print_stats(pcie_tag_ass_fifo      ,"pcie_tag_ass_fifo");
      fifo_print_stats(pcie_tag_map_fifo      ,"pcie_tag_map_fifo");
      for d in 0 to DMA_PORTS-1 loop
         fifo_print_stats(down_send_trans_fifo(d),"down_send_trans_fifo "&to_string(d));
      end loop;
      write(l,string'("Test completed successfully."));writeline(output,l);
      stop;
   end procedure;

    -- TAG MANAGER compatibility
    -- When using 10-bit PCIe Tag, only 512 values from 256 to 3*256-1 can be used, so only 9 bits are actually needed.
    constant INTERNAL_PCIE_TAG_WIDTH : integer := tsel((PCIE_TAG_WIDTH=10),9,PCIE_TAG_WIDTH);
    -- PCIe Tag can be converted from PCIE_TAG_WIDTH to INTERNAL_PCIE_TAG_WIDTH and back using these functions
    function pcie_tag_int_to_ext(int_tag : std_logic_vector(INTERNAL_PCIE_TAG_WIDTH-1 downto 0)) return std_logic_vector is
        variable ext_tag : std_logic_vector(PCIE_TAG_WIDTH-1 downto 0);
    begin
        if (PCIE_TAG_WIDTH=10) then
            ext_tag := std_logic_vector(resize_left(unsigned(int_tag),PCIE_TAG_WIDTH)+256);
        else
            ext_tag := int_tag;
        end if;
        return ext_tag;
    end function;
    function pcie_tag_ext_to_int(ext_tag : std_logic_vector(PCIE_TAG_WIDTH-1 downto 0)) return std_logic_vector is
        variable int_tag : std_logic_vector(INTERNAL_PCIE_TAG_WIDTH-1 downto 0);
    begin
        if (PCIE_TAG_WIDTH=10) then
            int_tag := std_logic_vector(resize_left(unsigned(ext_tag)-256,INTERNAL_PCIE_TAG_WIDTH));
        else
            int_tag := ext_tag;
        end if;
        return int_tag;
    end function;

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- UUT
   -- -------------------------------------------------------------------------

   uut: entity work.PCIE_TRANSACTION_CTRL
   generic map(
      DMA_PORTS            => DMA_PORTS,
      ENDPOINT_TYPE        => ENDPOINT_TYPE,
      DEVICE               => DEVICE,
      MVB_UP_ITEMS         => MVB_UP_ITEMS,
      MFB_UP_REGIONS       => MFB_UP_REGIONS,
      MFB_UP_REG_SIZE      => MFB_UP_REG_SIZE,
      MFB_UP_BLOCK_SIZE    => MFB_UP_BLOCK_SIZE,
      MFB_UP_ITEM_WIDTH    => MFB_UP_ITEM_WIDTH,
      DMA_MFB_UP_REGIONS   => DMA_MFB_UP_REGIONS,
      MVB_DOWN_ITEMS       => MVB_DOWN_ITEMS,
      MFB_DOWN_REGIONS     => MFB_DOWN_REGIONS,
      MFB_DOWN_REG_SIZE    => MFB_DOWN_REG_SIZE,
      MFB_DOWN_BLOCK_SIZE  => MFB_DOWN_BLOCK_SIZE,
      MFB_DOWN_ITEM_WIDTH  => MFB_DOWN_ITEM_WIDTH,
      DMA_MFB_DOWN_REGIONS => DMA_MFB_DOWN_REGIONS,
      PCIE_UPHDR_WIDTH     => PCIE_UPHDR_WIDTH,
      PCIE_DOWNHDR_WIDTH   => PCIE_DOWNHDR_WIDTH,
      PCIE_PREFIX_WIDTH    => PCIE_PREFIX_WIDTH,
      DMA_TAG_WIDTH        => DMA_TAG_WIDTH,
      DMA_ID_WIDTH         => DMA_ID_WIDTH,
      PCIE_TAG_WIDTH       => PCIE_TAG_WIDTH,
      MPS                  => UP_WRITE_LEN_MAX,
      MRRS                 => UP_READ_LEN_MAX,
      UP_ASFIFO_ITEMS      => UP_ASFIFO_ITEMS,
      DOWN_ASFIFO_ITEMS    => DOWN_ASFIFO_ITEMS,
      DOWN_FIFO_ITEMS      => DOWN_FIFO_ITEMS,
      RQ_TUSER_WIDTH       => RQ_TUSER_WIDTH,
      RC_TUSER_WIDTH       => RC_TUSER_WIDTH,
      AUTO_ASSIGN_TAGS     => AUTO_ASSIGN_TAGS
   )
   port map(
      CLK       => clk,
      RESET     => reset,
      CLK_DMA   => clk_dma,
      RESET_DMA => reset,

      UP_MVB_DATA       => s_up_mvb_data,
      UP_MVB_VLD        => s_up_mvb_vld,
      UP_MVB_SRC_RDY    => s_up_mvb_src_rdy,
      UP_MVB_DST_RDY    => s_up_mvb_dst_rdy,
      UP_MFB_DATA       => s_up_mfb_data,
      UP_MFB_SOF        => s_up_mfb_sof,
      UP_MFB_EOF        => s_up_mfb_eof,
      UP_MFB_SOF_POS    => s_up_mfb_sof_pos,
      UP_MFB_EOF_POS    => s_up_mfb_eof_pos,
      UP_MFB_SRC_RDY    => s_up_mfb_src_rdy,
      UP_MFB_DST_RDY    => s_up_mfb_dst_rdy,
      RQ_TDATA     => s_rq_tdata,
      RQ_TUSER     => s_rq_tuser,
      RQ_TLAST     => s_rq_tlast,
      RQ_TKEEP     => s_rq_tkeep,
      RQ_TREADY    => s_rq_tready,
      RQ_TVALID    => s_rq_tvalid,
      RQ_MVB_HDR_DATA    => s_rq_mvb_hdr_data   ,
      RQ_MVB_PREFIX_DATA => s_rq_mvb_prefix_data,
      RQ_MVB_VLD         => s_rq_mvb_vld        ,
      RQ_MFB_DATA    => s_rq_mfb_data,
      RQ_MFB_SOF     => s_rq_mfb_sof,
      RQ_MFB_EOF     => s_rq_mfb_eof,
      RQ_MFB_SOF_POS => s_rq_mfb_sof_pos,
      RQ_MFB_EOF_POS => s_rq_mfb_eof_pos,
      RQ_MFB_SRC_RDY => s_rq_mfb_src_rdy,
      RQ_MFB_DST_RDY => s_rq_mfb_dst_rdy,
      RC_MVB_HDR_DATA    => s_rc_mvb_hdr_data   ,
      RC_MVB_PREFIX_DATA => s_rc_mvb_prefix_data,
      RC_MVB_VLD         => s_rc_mvb_vld        ,
      RC_MFB_DATA    => s_rc_mfb_data,
      RC_MFB_SOF     => s_rc_mfb_sof,
      RC_MFB_EOF     => s_rc_mfb_eof,
      RC_MFB_SOF_POS => s_rc_mfb_sof_pos,
      RC_MFB_EOF_POS => s_rc_mfb_eof_pos,
      RC_MFB_SRC_RDY => s_rc_mfb_src_rdy,
      RC_MFB_DST_RDY => s_rc_mfb_dst_rdy,
      RC_TDATA     => s_rc_tdata,
      RC_TUSER     => s_rc_tuser,
      RC_TLAST     => s_rc_tlast,
      RC_TKEEP     => s_rc_tkeep,
      RC_TVALID    => s_rc_tvalid,
      RC_TREADY    => s_rc_tready,
      DOWN_MVB_DATA       => s_down_mvb_data,
      DOWN_MVB_VLD        => s_down_mvb_vld,
      DOWN_MVB_SRC_RDY    => s_down_mvb_src_rdy,
      DOWN_MVB_DST_RDY    => s_down_mvb_dst_rdy,
      DOWN_MFB_DATA       => s_down_mfb_data,
      DOWN_MFB_SOF        => s_down_mfb_sof,
      DOWN_MFB_EOF        => s_down_mfb_eof,
      DOWN_MFB_SOF_POS    => s_down_mfb_sof_pos,
      DOWN_MFB_EOF_POS    => s_down_mfb_eof_pos,
      DOWN_MFB_SRC_RDY    => s_down_mfb_src_rdy,
      DOWN_MFB_DST_RDY    => s_down_mfb_dst_rdy,
      RCB_SIZE       => s_rcb_size,
      TAG_ASSIGN     => s_tag_assign,
      TAG_ASSIGN_VLD => s_tag_assign_vld
   );

   -- -------------------------------------------------------------------------
   --                     internal signal organizer unit
   -- -------------------------------------------------------------------------

   s_org : entity work.signal_organizer;

   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating clk
   clk_gen: process
   begin
      clk <= '1';
      wait for C_CLK_PER / 2;
      clk <= '0';
      wait for C_CLK_PER / 2;
   end process clk_gen;

   -- generating clk
   clk_dma_gen: process
   begin
      clk_dma <= '1';
      wait for C_CLK_DMA_PER / 2;
      clk_dma <= '0';
      wait for C_CLK_DMA_PER / 2;
   end process clk_dma_gen;

   -- generating reset
   rst_gen: process
   begin
      reset <= '1';
      wait for C_RST_TIME;
      reset <= '0';
      wait;
   end process rst_gen;

   -- detect new DMA clk period
   dma_clk_status: process (clk_dma,dma_clk_used)
   begin
      if (dma_clk_used'event) then
         new_dma_clk <= '0';
      end if;

      if (clk_dma'event and clk_dma='1') then
         new_dma_clk <= '1';
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- I/O conversion
   -- -------------------------------------------------------------------------

   dma_port_conv_gen : for p in 0 to DMA_PORTS-1 generate
      up_mvb_conv : for i in 0 to MVB_UP_ITEMS-1 generate
         up_mvb_i_hdr(p)(i)           <= s_up_mvb_data(p)(DMA_UPHDR_WIDTH*(i+1)-1 downto DMA_UPHDR_WIDTH*i);

         up_mvb_i_hdr_type(p)(i)      <= "RD" when up_mvb_i_hdr(p)(i)(DMA_REQUEST_TYPE)=DMA_TYPE_READ else "WR";
         up_mvb_i_hdr_length(p)(i)    <= to_integer(unsigned(up_mvb_i_hdr(p)(i)(DMA_REQUEST_LENGTH)));
         up_mvb_i_hdr_address(p)(i)   <= up_mvb_i_hdr(p)(i)(DMA_REQUEST_GLOBAL);
         up_mvb_i_hdr_tag(p)(i)       <= to_integer(unsigned(up_mvb_i_hdr(p)(i)(DMA_REQUEST_TAG)));
         up_mvb_i_hdr_id(p)(i)        <= to_integer(unsigned(up_mvb_i_hdr(p)(i)(DMA_REQUEST_UNITID)));
      end generate;

      up_mfb_conv : for i in 0 to MFB_UP_REGIONS-1 generate
         up_mfb_i_data(p)(i)    <= s_up_mfb_data(p)(DMA_MFB_UP_DATA_WIDTH/DMA_MFB_UP_REGIONS*(i+1)-1 downto DMA_MFB_UP_DATA_WIDTH/DMA_MFB_UP_REGIONS*i);

         up_mfb_i_sof_pos(p)(i) <= to_integer(unsigned(s_up_mfb_sof_pos(p)(MFB_UP_SOF_POS_WIDTH*(i+1)-1 downto MFB_UP_SOF_POS_WIDTH*i)))*MFB_UP_BLOCK_SIZE/2;
         up_mfb_i_eof_pos(p)(i) <= to_integer(unsigned(s_up_mfb_eof_pos(p)(MFB_UP_EOF_POS_WIDTH*(i+1)-1 downto MFB_UP_EOF_POS_WIDTH*i)));
      end generate;

      down_mvb_conv : for i in 0 to MVB_DOWN_ITEMS-1 generate
         down_mvb_i_hdr(p)(i)           <= s_down_mvb_data(p)(DMA_DOWNHDR_WIDTH*(i+1)-1 downto DMA_DOWNHDR_WIDTH*i);

         down_mvb_i_hdr_length(p)(i)    <= to_integer(unsigned(down_mvb_i_hdr(p)(i)(DMA_COMPLETION_LENGTH)));
         down_mvb_i_hdr_completed(p)(i) <= down_mvb_i_hdr(p)(i)(DMA_COMPLETION_COMPLETED'low);
         down_mvb_i_hdr_tag(p)(i)       <= to_integer(unsigned(down_mvb_i_hdr(p)(i)(DMA_COMPLETION_TAG)));
         down_mvb_i_hdr_id(p)(i)        <= to_integer(unsigned(down_mvb_i_hdr(p)(i)(DMA_COMPLETION_UNITID)));
      end generate;

      down_mfb_conv : for i in 0 to MFB_DOWN_REGIONS-1 generate
         down_mfb_i_data(p)(i)    <= s_down_mfb_data(p)(DMA_MFB_DOWN_DATA_WIDTH/DMA_MFB_DOWN_REGIONS*(i+1)-1 downto DMA_MFB_DOWN_DATA_WIDTH/DMA_MFB_DOWN_REGIONS*i);

         down_mfb_i_sof_pos(p)(i) <= to_integer(unsigned(s_down_mfb_sof_pos(p)(MFB_DOWN_SOF_POS_WIDTH*(i+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*i)))*MFB_DOWN_BLOCK_SIZE/2;
         down_mfb_i_eof_pos(p)(i) <= to_integer(unsigned(s_down_mfb_eof_pos(p)(MFB_DOWN_EOF_POS_WIDTH*(i+1)-1 downto MFB_DOWN_EOF_POS_WIDTH*i)));
      end generate;
   end generate;

   tag_ass_conv : for i in 0 to MVB_UP_ITEMS-1 generate
      tag_ass_i_tag(i) <= to_integer(unsigned(s_tag_assign(PCIE_TAG_WIDTH*(i+1)-1 downto PCIE_TAG_WIDTH*i)));
   end generate;

   s_rcb_size <= '1' when RCB_SIZE=128 else '0';

   -- -------------------------------------------------------------------------
   -- test process
   -- -------------------------------------------------------------------------

   -- UP generator generates new UP transactions in up_mvb_mfb_gen_fifo
   up_mvb_mfb_trans_generator_pr : process
      variable seed1 : positive := RAND_SEED+4;
      variable seed2 : positive := RAND_SEED+88;
      variable X     : integer;

      variable trans : mvb_mfb_trans_t;
      variable trans_ser : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);

      variable p : integer := GEN_PRINT_INTERVAL;
      variable d : integer;
   begin
      X := -1;
      while (X<UP_NOT_SRC_RDY_CHANCE) loop
         wait until clk_dma'event and clk_dma='0';
         randint(seed1,seed2,0,99,X);
      end loop;

      -- choose random DMA Port
      for d in 0 to DMA_PORTS-1 loop
         while (up_mvb_mfb_gen_fifo(d).full='0') loop
            if ((or dma_idtag_free(d))='0') then
               next; -- don't generate when there are no free Tags
            end if;
            randint(seed1,seed2,0,99,X);
            if (X<UP_READ_CHANCE) then
               mvb_mfb_trans_new_rand(trans,seed1,seed2,d,dma_idtag_free(d),UP_READ_LEN_MIN,UP_READ_LEN_MAX,'1',0,0,0,'0');
            else
               mvb_mfb_trans_new_rand(trans,seed1,seed2,d,dma_idtag_free(d),UP_WRITE_LEN_MIN,UP_WRITE_LEN_MAX,'0',UP_GAP_CHANCE,UP_GAP_LEN_MIN,UP_GAP_LEN_MAX,'0');
            end if;

      --      write(l,string'("New generated transaction:"));writeline(output,l);
      --      mvb_mfb_trans_print(trans);

            -- Set top bits of address to DMA_PORT, so that the port can by deduced from the transaction's header
            trans.address := to_unsigned(d,log2(DMA_PORTS)) & enlarge_left(trans.address,-log2(DMA_PORTS));

            trans_ser := mvb_mfb_trans_ser(trans);

            slv_fifo_put(up_mvb_mfb_gen_fifo(d),trans_ser);

            up_trans_cntr := up_trans_cntr+1;
            if (up_trans_cntr=UP_TRANSACTIONS) then
               wait; -- Stop generating
            end if;
         end loop;
      end loop;
   end process;
   ----

   -- UP MVB+MFB interface transaction insertion
   up_mvb_mfb_trans_post_pr : process
      variable seed1 : positive := RAND_SEED+48;
      variable seed2 : positive := RAND_SEED+1;
      variable X     : integer;

      variable new_trans_send     : mvb_mfb_trans_array_t(MVB_UP_ITEMS-1 downto 0);
      variable new_trans_send_vld : std_logic_vector(MVB_UP_ITEMS-1 downto 0);

      variable id_vec    : std_logic_vector(DMA_ID_WIDTH-1 downto 0);
      variable tag_vec   : std_logic_vector(DMA_TAG_WIDTH-1 downto 0);
      variable idtag_vec : std_logic_vector(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto 0);
   begin
      if (reset='1') then
         wait until reset='0';
      end if;

      wait until clk_dma'event and clk_dma='1';

      for p in 0 to DMA_PORTS-1 loop
         -- sample MVB interface
         up_mvb_i(p).data    := s_up_mvb_data   (p);
         up_mvb_i(p).vld     := s_up_mvb_vld    (p);
         up_mvb_i(p).src_rdy := s_up_mvb_src_rdy(p);
         up_mvb_i(p).dst_rdy := s_up_mvb_dst_rdy(p);
         -- sample MFB interface
         up_mfb_i(p).data    := s_up_mfb_data   (p);
         up_mfb_i(p).sof     := s_up_mfb_sof    (p);
         up_mfb_i(p).eof     := s_up_mfb_eof    (p);
         up_mfb_i(p).sof_pos := s_up_mfb_sof_pos(p);
         up_mfb_i(p).eof_pos := s_up_mfb_eof_pos(p);
         up_mfb_i(p).src_rdy := s_up_mfb_src_rdy(p);
         up_mfb_i(p).dst_rdy := s_up_mfb_dst_rdy(p);

         new_trans_send_vld := (others => '0');

         post_new_up_mvb_mfb_word(up_mvb_mfb_gen_fifo(p),up_mvb_i(p),up_mfb_i(p),new_trans_send,new_trans_send_vld);

         for i in 0 to MVB_UP_ITEMS-1 loop
            exit when (new_trans_send_vld(i)='0');

            if (FULL_PRINT) then
               write(l,string'("------------------------------"));writeline(output,l);
               write(l,now);write(l,string'(" : "));
               write(l,string'("DMA Port "));write_dec(l,p);write(l,string'(" : "));
               write(l,string'("Send UP T "));write_dec(l,trans_up_send_cntr);writeline(output,l);
               write(l,string'("------------------------------"));writeline(output,l);
               trans_up_send_cntr := trans_up_send_cntr+1;
               mvb_mfb_trans_print(new_trans_send(i));
            end if;

            -- add to statistics
            if (new_trans_send(i).payload='1') then
               stat_up_trans_wr_cntr := stat_up_trans_wr_cntr+1;
               stat_up_trans_wr_len_sum := stat_up_trans_wr_len_sum+new_trans_send(i).length;
               stat_up_trans_wr_len_num := stat_up_trans_wr_len_num+1;
               if (new_trans_send(i).length<stat_up_trans_wr_len_min or stat_up_trans_wr_len_min=-1) then
                  stat_up_trans_wr_len_min := new_trans_send(i).length;
               end if;
               if (new_trans_send(i).length>stat_up_trans_wr_len_max) then
                  stat_up_trans_wr_len_max := new_trans_send(i).length;
               end if;
            else
               stat_up_trans_rd_cntr := stat_up_trans_rd_cntr+1;
               stat_up_trans_rd_len_sum := stat_up_trans_rd_len_sum+new_trans_send(i).length;
               stat_up_trans_rd_len_num := stat_up_trans_rd_len_num+1;
               if (new_trans_send(i).length<stat_up_trans_rd_len_min or stat_up_trans_rd_len_min=-1) then
                  stat_up_trans_rd_len_min := new_trans_send(i).length;
               end if;
               if (new_trans_send(i).length>stat_up_trans_rd_len_max) then
                  stat_up_trans_rd_len_max := new_trans_send(i).length;
               end if;
            end if;

            if (up_send_trans_fifo(p).full='1') then
               report "Full UP send transaction FIFO!" severity failure; -- FIFO full situation will be fixed, if it arises in the future
            else
               slv_fifo_put(up_send_trans_fifo(p),mvb_mfb_trans_ser(new_trans_send(i)));
            end if;

            if (new_trans_send(i).payload='0') then
               id_vec  := std_logic_vector(to_unsigned(new_trans_send(i).id ,DMA_ID_WIDTH));
               tag_vec := std_logic_vector(to_unsigned(new_trans_send(i).tag,DMA_TAG_WIDTH));

               idtag_vec := id_vec & tag_vec;

               if (up_idtag_fifo(p).full='1') then
                  report "Full ID Tag FIFO!" severity failure; -- FIFO full situation will be fixed, if it arises in the future
               else
                  slv_fifo_put(up_idtag_fifo(p),idtag_vec);
               end if;
            end if;
         end loop;

         -- set MVB interface
         s_up_mvb_data   (p) <= up_mvb_i(p).data   ;
         s_up_mvb_vld    (p) <= up_mvb_i(p).vld    ;
         s_up_mvb_src_rdy(p) <= up_mvb_i(p).src_rdy;
         -- set MFB interface
         s_up_mfb_data   (p) <= up_mfb_i(p).data   ;
         s_up_mfb_sof    (p) <= up_mfb_i(p).sof    ;
         s_up_mfb_eof    (p) <= up_mfb_i(p).eof    ;
         s_up_mfb_sof_pos(p) <= up_mfb_i(p).sof_pos;
         s_up_mfb_eof_pos(p) <= up_mfb_i(p).eof_pos;
         s_up_mfb_src_rdy(p) <= up_mfb_i(p).src_rdy;
      end loop;
   end process;
   ----

   -- accepting UP AXI words to PCIe endpoint
   up_axi_trans_acc_pr : process
      variable seed1 : positive := RAND_SEED+2;
      variable seed2 : positive := RAND_SEED+222;
      variable rand  : real;
      variable X     : integer;

      variable n : integer;

      variable unfinished              : mvb_mfb_trans_t;
      variable unfinished_expected_len : integer := 2;
      variable unfinished_vld          : std_logic := '0';

      variable accepted     : mvb_mfb_trans_array_t(MVB_UP_ITEMS-1 downto 0);
      variable accepted_vld : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
      variable new_tags     : i_array_t(MVB_UP_ITEMS-1 downto 0);
      variable new_tags_vld : std_logic_vector(MVB_UP_ITEMS-1 downto 0);

      variable trans_ser : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);
      variable trans     : mvb_mfb_trans_t;
      variable d         : integer;

      variable idtag_vec : std_logic_vector(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto 0);
      variable pcie_tag_ser : std_logic_vector(PCIE_TAG_WIDTH-1 downto 0);
      variable pcie_tag  : integer;
      variable dma_tag   : integer;
      variable dma_id    : integer;

   begin
      if (reset='1') then
         wait until reset='0';
      end if;

      wait until clk'event and clk='1';

      -- pop from up_acc_trans_delay_fifo and put to up_acc_trans_fifo
      for i in 0 to MVB_UP_ITEMS-1 loop
         if (up_acc_trans_delay_vld(0)(i)='1') then
            if (up_acc_trans_fifo.full='1') then
               report "Full PCIe accept FIFO!" severity failure; -- FIFO full situation will be fixed, if it arises in the future
            else
               slv_fifo_put(up_acc_trans_fifo,up_acc_trans_delay_fifo(0)(i));
            end if;
         end if;
      end loop;
      -- shift up_acc_trans_delay_fifo
      up_acc_trans_delay_fifo(DOWN_RESPONSE_DELAY_MIN-1-1 downto 0) := up_acc_trans_delay_fifo(DOWN_RESPONSE_DELAY_MIN-1 downto 1);
      up_acc_trans_delay_vld (DOWN_RESPONSE_DELAY_MIN-1-1 downto 0) := up_acc_trans_delay_vld (DOWN_RESPONSE_DELAY_MIN-1 downto 1);
      up_acc_trans_delay_vld (DOWN_RESPONSE_DELAY_MIN-1) := (others => '0');

      -- sample RQ interface
      rq_i.tuser  := rq_tuser_deser(s_rq_tuser);
      rq_i.tdata  := s_rq_tdata;
      rq_i.tlast  := s_rq_tlast;
      rq_i.tkeep  := s_rq_tkeep;
      rq_i.tready := s_rq_tready;
      rq_i.tvalid := s_rq_tvalid;
      -- sample RQ MFB interface
      rq_mvb_i.data    := s_rq_mvb_hdr_data;
      rq_mvb_i.vld     := s_rq_mvb_vld;
      rq_mvb_i.src_rdy := s_rq_mfb_src_rdy;
      rq_mvb_i.dst_rdy := s_rq_mfb_dst_rdy;
      -- sample RQ MFB interface
      rq_mfb_i.data    := s_rq_mfb_data;
      rq_mfb_i.sof     := s_rq_mfb_sof;
      rq_mfb_i.eof     := s_rq_mfb_eof;
      rq_mfb_i.sof_pos := s_rq_mfb_sof_pos;
      rq_mfb_i.eof_pos := s_rq_mfb_eof_pos;
      rq_mfb_i.src_rdy := s_rq_mfb_src_rdy;
      rq_mfb_i.dst_rdy := s_rq_mfb_dst_rdy;

      if (DEVICE="STRATIX10") then
         -- fake AXI RQ interface on Intel FPGA
         rq_i := mfb2rq_conv(rq_mfb_i);
      end if;

--      write(l,now);write(l,string'("AAAAAAA"));writeline(output,l);
--      write(l,string'("sop: "));write_hex(l,rq_i.tuser.sop);writeline(output,l);
--      write(l,string'("eop: "));write_hex(l,rq_i.tuser.eop);writeline(output,l);
--      write(l,string'("sop_pos: "));
--      for i in MFB_UP_REGIONS-1 downto 0 loop
--         write(l,string'(" "));write_hex(l,rq_i.tuser.sop_pos(i));
--      end loop;
--      writeline(output,l);
--      write(l,string'("eop_pos: "));
--      for i in MFB_UP_REGIONS-1 downto 0 loop
--         write(l,string'(" "));write_hex(l,rq_i.tuser.eop_pos(i));
--      end loop;
--      writeline(output,l);

      -- accept new RQ word
      accept_rq_word(rq_i,rq_mvb_i,unfinished,unfinished_expected_len,unfinished_vld,accepted,accepted_vld,pcie_tag_free,new_tags,new_tags_vld,seed1,seed2);

      -- add to statistics
      if ((or new_tags_vld)='1') then
         n := count_val(pcie_tag_free,'0');
         stat_pcie_tags_used_sum := stat_pcie_tags_used_sum+n;
         stat_pcie_tags_used_num := stat_pcie_tags_used_num+1;
         if (n<stat_pcie_tags_used_min or stat_pcie_tags_used_min=-1) then
            stat_pcie_tags_used_min := n;
         end if;
         if (n>stat_pcie_tags_used_max) then
            stat_pcie_tags_used_max := n;
         end if;
      end if;

      for i in 0 to MVB_UP_ITEMS-1 loop
         exit when (new_tags_vld(i)='0');

         if (FULL_PRINT) then
            write(l,string'("PCIe Tag " & integer'image(new_tags(i)) & " assigned"));writeline(output,l);
         end if;

         if (pcie_tag_ass_fifo.full='1') then
            report "Full PCIe Tag assign FIFO!" severity failure; -- FIFO full situation will be fixed, if it arises in the future
         else
            slv_fifo_put(pcie_tag_ass_fifo,std_logic_vector(to_unsigned(new_tags(i),PCIE_TAG_WIDTH)));
            slv_fifo_put(pcie_tag_map_fifo,std_logic_vector(to_unsigned(new_tags(i),PCIE_TAG_WIDTH)));
         end if;
      end loop;

      for i in 0 to MVB_UP_ITEMS-1 loop
         exit when (accepted_vld(i)='0');

         -- deduce transaction's original DMA_PORT from top bits of address
         d := to_integer(resize_right(accepted(i).address,log2(DMA_PORTS)));

         if (FULL_PRINT) then
            write(l,string'("------------------------------"));writeline(output,l);
            write(l,now);write(l,string'(" : "));
            write(l,string'("DMA Port "));write_dec(l,d);write(l,string'(" : "));
            write(l,string'("Recv UP T "));write_dec(l,trans_up_recv_cntr);
            if (accepted(i).payload='0') then
               write(l,string'(" (with assigned PCIe Tag)"));
            end if;
            writeline(output,l);
            write(l,string'("------------------------------"));writeline(output,l);
            trans_up_recv_cntr := trans_up_recv_cntr+1;
            mvb_mfb_trans_print(accepted(i));
         end if;

         if (NO_CHECKING=false and up_send_trans_fifo(d).empty='1') then
            write(l,string'("Unexpected UP transaction received!"));writeline(output,l);
            mvb_mfb_trans_print(accepted(i));

            write(l,string'("No transactions expected on DMA Port "&to_string(d)&"!"));writeline(output,l);

            for pp in 0 to DMA_PORTS-1 loop
               write(l,string'("Other expected transactions on DMA Port "&to_string(pp)&":"));writeline(output,l);
               mvb_mfb_trans_fifo_print(up_send_trans_fifo(pp));
            end loop;
            report "" severity failure;
         end if;

         slv_fifo_pop(up_send_trans_fifo(d),trans_ser);
         trans := mvb_mfb_trans_deser(trans_ser);

         if (NO_CHECKING=false and mvb_mfb_trans_cmp(trans,accepted(i))=false) then
            write(l,string'("Unexpected UP transaction received!"));writeline(output,l);
            mvb_mfb_trans_print(accepted(i));

            write(l,string'("Expected transaction:"));writeline(output,l);
            mvb_mfb_trans_print(trans);

            for pp in 0 to DMA_PORTS-1 loop
               write(l,string'("Other expected transactions on DMA Port "&to_string(pp)&":"));writeline(output,l);
               mvb_mfb_trans_fifo_print(up_send_trans_fifo(pp));
            end loop;
            report "" severity failure;
         end if;

         if (accepted(i).payload='0') then
            -- map transaction's PCIe Tag
            if (pcie_tag_map_fifo.empty='1') then
               report "Empty PCIe Tag mapping FIFO!" severity failure; -- verification error
            end if;
            if (up_idtag_fifo(d).empty='1') then
               report "Empty DMA UP ID+Tag FIFO!" severity failure; -- verification error
            end if;
            slv_fifo_pop(up_idtag_fifo(d),idtag_vec);
            dma_tag := to_integer(unsigned(idtag_vec(DMA_TAG_WIDTH-1 downto 0)));
            dma_id  := to_integer(unsigned(idtag_vec(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto DMA_TAG_WIDTH)));

            slv_fifo_pop(pcie_tag_map_fifo,pcie_tag_ser);
            pcie_tag := to_integer(unsigned(pcie_tag_ser));

            pcie_tag_to_dma_tag_map(pcie_tag) := dma_tag;
            pcie_tag_to_dma_id_map(pcie_tag)  := dma_id;

            if (FULL_PRINT) then
               write(l,string'("PCIe Tag "));write_dec(l,pcie_tag);
               write(l,string'(" mapped to DMA Tag "));write_dec(l,dma_tag);
               write(l,string'(" ID "));write_dec(l,dma_id);
               writeline(output,l);
            end if;

            -- add transaction to wait for response generation
            up_acc_trans_delay_fifo(DOWN_RESPONSE_DELAY_MIN-1)(i) := mvb_mfb_trans_ser(accepted(i));
            up_acc_trans_delay_vld (DOWN_RESPONSE_DELAY_MIN-1)(i) := '1';
         end if;

         if (accepted(i).payload='1') then
            trans_processed_cntr := trans_processed_cntr+1;
            if (trans_processed_cntr=UP_TRANSACTIONS) then

               write(l,string'("                                             transactions processed: " & integer'image(trans_processed_cntr) & " / " & integer'image(UP_TRANSACTIONS)));writeline(output,l);
               success_end;
            end if;
            if (trans_processed_cntr=next_print_cntr) then
               write(l,string'("                                             transactions processed: " & integer'image(trans_processed_cntr) & " / " & integer'image(UP_TRANSACTIONS)));writeline(output,l);
               next_print_cntr := next_print_cntr+GEN_PRINT_INTERVAL;
            end if;
         end if;
      end loop;

      -- set RQ dst_rdy
      if (rq_i.tvalid='1' or rq_i.tready='0') then
         rq_i.tready := '0';

         randint(seed1,seed2,0,99,X);
         if (X<RQ_TREADY_CHANCE) then
            rq_i.tready := '1';
         end if;
      end if;

      -- check enough free PCIe tags free for next word
      n := 0;
      for i in 0 to 2**PCIE_TAG_WIDTH-1 loop
         if (pcie_tag_free(i)='1') then
            n := n+1;
            exit when (n=MVB_UP_ITEMS); -- need at least MVB_UP_ITEMS free tags to surely accept next word
         end if;
      end loop;
      if (n<MVB_UP_ITEMS) then
         rq_i.tready := '0';
      end if;

      -- set RQ interface
      if (DEVICE="STRATIX10") then
         s_rq_tready <= 'U';
         s_rq_mfb_dst_rdy <= rq_i.tready;
      else
         s_rq_tready <= rq_i.tready;
         s_rq_mfb_dst_rdy <= 'U';
      end if;
   end process;
   ----

   -- Sending Tag assign info to Tag manager
   tag_ass_pr : process
      variable seed1 : positive := RAND_SEED+2454;
      variable seed2 : positive := RAND_SEED+14;
      variable X     : integer;

      variable tag : std_logic_vector(PCIE_TAG_WIDTH-1 downto 0);
   begin
      if (reset='1') then
         wait until reset='0';
      end if;

      wait until clk'event and clk='0';

      s_tag_assign_vld <= (others => '0');

      for i in 0 to MVB_UP_ITEMS-1 loop
         exit when (pcie_tag_ass_fifo.empty='1');

         randint(seed1,seed2,0,99,X);
         exit when (X>TAG_ASS_SEND_CHANCE); -- don't send any more tags on this clk

         slv_fifo_pop(pcie_tag_ass_fifo,tag);
         s_tag_assign(PCIE_TAG_WIDTH*(i+1)-1 downto PCIE_TAG_WIDTH*i) <= tag;
         s_tag_assign_vld(i) <= '1';
      end loop;

      if (AUTO_ASSIGN_TAGS) then
         s_tag_assign     <= (others => 'U');
         s_tag_assign_vld <= (others => 'U');
      end if;

   end process;
   ----

   -- Sending DOWN AXI responses
   down_axi_trans_generator_pr : process
      variable seed1 : positive := RAND_SEED+655;
      variable seed2 : positive := RAND_SEED+65;
      variable rand  : real;
      variable X     : integer;

      variable unfinished           : mvb_mfb_trans_t;
      variable unfinished_vld       : std_logic := '0';

      variable trans_ser : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);
      variable trans     : mvb_mfb_trans_t;
      variable d         : integer;

      variable new_trans_send     : mvb_mfb_trans_array_t(MVB_DOWN_ITEMS-1 downto 0);
      variable new_trans_send_vld : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0) := (others => '0');

      variable tag : integer;
      variable completed : std_logic;
      variable idtag_vec : std_logic_vector(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto 0);
   begin
      if (reset='1') then
         wait until reset='0';
      end if;

      wait until clk'event and clk='1';

      -- sample RC interface
      rc_i.tuser  := rc_tuser_deser(s_rc_tuser);
      rc_i.tdata  := s_rc_tdata;
      rc_i.tlast  := s_rc_tlast;
      rc_i.tkeep  := s_rc_tkeep;
      rc_i.tvalid := s_rc_tvalid;
      rc_i.tready := s_rc_tready;
      -- sample RC MVB interface
      rc_mvb_i.data    := s_rc_mvb_hdr_data;
      rc_mvb_i.vld     := s_rc_mvb_vld;
      rc_mvb_i.src_rdy := s_rc_mfb_src_rdy;
      rc_mvb_i.dst_rdy := s_rc_mfb_dst_rdy;
      -- sample RC MFB interface
      rc_mfb_i.data    := s_rc_mfb_data;
      rc_mfb_i.sof     := s_rc_mfb_sof;
      rc_mfb_i.eof     := s_rc_mfb_eof;
      rc_mfb_i.sof_pos := s_rc_mfb_sof_pos;
      rc_mfb_i.eof_pos := s_rc_mfb_eof_pos;
      rc_mfb_i.src_rdy := s_rc_mfb_src_rdy;
      rc_mfb_i.dst_rdy := s_rc_mfb_dst_rdy;

      if (DEVICE="STRATIX10") then
         -- fake AXI RC interface on Intel FPGA
         rc_i.tready := rc_mfb_i.dst_rdy;
      end if;

      -- generate new word
      post_new_rc_word(rc_i,rc_mvb_i,response_rem_addr,response_rem_length,response_gen,unfinished,unfinished_vld,new_trans_send,new_trans_send_vld,seed1,seed2);

      -- add new transactions to down FIFO
      for i in 0 to MVB_DOWN_ITEMS-1 loop
         exit when (new_trans_send_vld(i)='0');

         -- deduce transaction's original DMA_PORT from top bits of address
         d := to_integer(resize_right(new_trans_send(i).address,log2(DMA_PORTS)));

         if (FULL_PRINT) then
            write(l,string'("------------------------------"));writeline(output,l);
            write(l,now);write(l,string'(" : "));
            write(l,string'("DMA Port "));write_dec(l,d);write(l,string'(" : "));
            write(l,string'("Send DOWN T "));write_dec(l,trans_down_send_cntr);writeline(output,l);
            write(l,string'("------------------------------"));writeline(output,l);
            trans_down_send_cntr := trans_down_send_cntr+1;
            mvb_mfb_trans_print(new_trans_send(i));
         end if;

         -- add to statistics
         stat_down_trans_cntr := stat_down_trans_cntr+1;
         stat_down_trans_len_sum := stat_down_trans_len_sum+new_trans_send(i).length;
         stat_down_trans_len_num := stat_down_trans_len_num+1;
         if (new_trans_send(i).length<stat_down_trans_len_min or stat_down_trans_len_min=-1) then
            stat_down_trans_len_min := new_trans_send(i).length;
         end if;
         if (new_trans_send(i).length>stat_down_trans_len_max) then
            stat_down_trans_len_max := new_trans_send(i).length;
         end if;

         if (down_send_trans_fifo(d).full='1') then
            report "Full down trans send FIFO!" severity failure; -- FIFO full situation will be fixed, if it arises in the future
         else
            slv_fifo_put(down_send_trans_fifo(d),mvb_mfb_trans_ser(new_trans_send(i)));
         end if;

         tag := new_trans_send(i).tag;
         completed := new_trans_send(i).completed;
         idtag_vec(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto DMA_TAG_WIDTH) := std_logic_vector(to_unsigned(pcie_tag_to_dma_id_map (tag),DMA_ID_WIDTH));
         idtag_vec(DMA_TAG_WIDTH-1 downto 0)                          := std_logic_vector(to_unsigned(pcie_tag_to_dma_tag_map(tag),DMA_TAG_WIDTH));

         if (down_idtag_fifo(d).full='1') then
            report "Full down ID+Tag FIFO!" severity failure; -- FIFO full situation will be fixed, if it arises in the future
         else
            slv_fifo_put(down_idtag_fifo(d),idtag_vec);
         end if;

         if (completed='1' and response_gen(tag)='0') then -- response completed
            if (FULL_PRINT) then
               write(l,string'("PCIe Tag "));
               write_dec(l,tag);
               write(l,string'(" freed"));
               writeline(output,l);
            end if;
            -- free this pcie tag for new assign
            if (pcie_tag_free(tag)='1') then
               write(l,string'("PCIe Tag freed twice!"));writeline(output,l);
               write(l,string'("Transaction send to down:"));writeline(output,l);
               mvb_mfb_trans_print(new_trans_send(i));
               report "" severity failure;
            end if;

            pcie_tag_free(tag) := '1';
         end if;
      end loop;

      -- start generating new responses
      for i in 0 to MVB_DOWN_ITEMS-1 loop
         exit when (up_acc_trans_fifo.empty='1'); -- no more requests waiting

         randint(seed1,seed2,0,99,X);
         if (X<DOWN_RESPONSE_START_CHANCE) then
            slv_fifo_pop(up_acc_trans_fifo,trans_ser);
            trans := mvb_mfb_trans_deser(trans_ser);

            if (response_gen(trans.tag)='1') then
               write(l,string'("Response with tag "));
               write_dec(l,trans.tag);
               write(l,string'(" already being generated!"));
               writeline(output,l);
               write(l,string'("Transaction wanting to start generating response:"));
               mvb_mfb_trans_print(trans);
               write(l,string'("Other accepted UP transaction waiting for response:"));
               mvb_mfb_trans_fifo_print(up_acc_trans_fifo);
               report "" severity failure;
            end if;

            response_gen(trans.tag)        := '1';
            response_rem_addr(trans.tag)   := trans.address;
            response_rem_length(trans.tag) := trans.length;
         end if;
      end loop;

      -- set RC interface
      if (DEVICE="STRATIX10") then
         s_rc_tuser  <= (others => 'U');
         s_rc_tdata  <= (others => 'U');
         s_rc_tlast  <= 'U';
         s_rc_tkeep  <= (others => 'U');
         s_rc_tvalid <= 'U';

         s_rc_mvb_hdr_data <= rc_mvb_i.data  ;
         s_rc_mvb_vld      <= rc_mvb_i.vld   ;

         if (rc_i.tready='1') then
             rc_mfb_i := rc2mfb_conv(rc_i);
             s_rc_mfb_data    <= rc_mfb_i.data   ;
             s_rc_mfb_sof     <= rc_mfb_i.sof    ;
             s_rc_mfb_eof     <= rc_mfb_i.eof    ;
             s_rc_mfb_sof_pos <= rc_mfb_i.sof_pos;
             s_rc_mfb_eof_pos <= rc_mfb_i.eof_pos;
             s_rc_mfb_src_rdy <= rc_mfb_i.src_rdy;
         end if;
      else
         s_rc_tuser  <= rc_tuser_ser(rc_i.tuser);
         s_rc_tdata  <= rc_i.tdata;
         s_rc_tlast  <= rc_i.tlast;
         s_rc_tkeep  <= rc_i.tkeep;
         s_rc_tvalid <= rc_i.tvalid;

         s_rc_mfb_data    <= (others => 'U');
         s_rc_mfb_sof     <= (others => 'U');
         s_rc_mfb_eof     <= (others => 'U');
         s_rc_mfb_sof_pos <= (others => 'U');
         s_rc_mfb_eof_pos <= (others => 'U');
         s_rc_mfb_src_rdy <= 'U';
      end if;

   end process;
   ----

   -- accepting DOWN MVB+MFB words in DMA
   down_mvb_mfb_trans_acc_pr : process
      variable seed1 : positive := RAND_SEED+11;
      variable seed2 : positive := RAND_SEED+1221;
      variable rand  : real;
      variable X     : integer;

      variable unfinished              : mvb_mfb_trans_array_t(DMA_PORTS-1 downto 0);
      variable unfinished_vld          : std_logic_vector     (DMA_PORTS-1 downto 0) := (others => '0');
      variable unfinished_expected_len : i_array_t            (DMA_PORTS-1 downto 0);

      variable trans_ser : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);
      variable trans     : mvb_mfb_trans_t;

      variable tag       : integer;
      variable id        : integer;
      variable completed : std_logic;
      variable idtag     : integer;

      variable idtag_vec : std_logic_vector(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto 0);

      variable expected_tag  : integer;
      variable expected_id   : integer;

      variable mvb_i_ptr : i_array_t(DMA_PORTS-1 downto 0) := (others => 0);
      variable mfb_i_ptr : i_array_t(DMA_PORTS-1 downto 0) := (others => 0);

      variable accepted           : mvb_mfb_trans_array_t(DMA_MFB_DOWN_REGIONS-1 downto 0);
      variable accepted_vld       : std_logic_vector(DMA_MFB_DOWN_REGIONS-1 downto 0) := (others => '0');
   begin
      if (reset='1') then
         wait until reset='0';
      end if;

      wait until clk_dma'event and clk_dma='0';

      for p in 0 to DMA_PORTS-1 loop
         -- sample MVB interface
         down_mvb_i(p).data    := s_down_mvb_data   (p);
         down_mvb_i(p).vld     := s_down_mvb_vld    (p);
         down_mvb_i(p).src_rdy := s_down_mvb_src_rdy(p);
         down_mvb_i(p).dst_rdy := s_down_mvb_dst_rdy(p);
         -- sample MFB interface
         down_mfb_i(p).data    := s_down_mfb_data   (p);
         down_mfb_i(p).sof     := s_down_mfb_sof    (p);
         down_mfb_i(p).eof     := s_down_mfb_eof    (p);
         down_mfb_i(p).sof_pos := s_down_mfb_sof_pos(p);
         down_mfb_i(p).eof_pos := s_down_mfb_eof_pos(p);
         down_mfb_i(p).src_rdy := s_down_mfb_src_rdy(p);
         down_mfb_i(p).dst_rdy := s_down_mfb_dst_rdy(p);

         randint(seed1,seed2,0,99,X);
         if (X<DOWN_NOT_DST_RDY_CHANCE) then
            -- don't accept anything
            down_mvb_i(p).dst_rdy := '0';
            down_mfb_i(p).dst_rdy := '0';
         else
            -- accept new word (if can be accepted)
            accept_mvb_mfb_word(down_mvb_i(p),down_mfb_i(p),mvb_i_ptr(p),mfb_i_ptr(p),unfinished(p),unfinished_expected_len(p),unfinished_vld(p),accepted,accepted_vld,seed1,seed2);

            for i in 0 to DMA_MFB_DOWN_REGIONS-1 loop
               exit when (accepted_vld(i)='0');

               accepted(i).address := to_unsigned(p,log2(DMA_PORTS)) & enlarge_left(accepted(i).address,-log2(DMA_PORTS));

               if (FULL_PRINT) then
                  write(l,string'("------------------------------"));writeline(output,l);
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("DMA Port "));write_dec(l,p);write(l,string'(" : "));
                  write(l,string'("Recv DOWN T "));write_dec(l,trans_down_recv_cntr);writeline(output,l);
                  write(l,string'("------------------------------"));writeline(output,l);
                  trans_down_recv_cntr := trans_down_recv_cntr+1;
                  mvb_mfb_trans_print(accepted(i));
               end if;

               if (NO_CHECKING=false and down_send_trans_fifo(p).empty='1') then
                  write(l,string'("Unexpected DOWN transaction received!"));writeline(output,l);
                  mvb_mfb_trans_print(accepted(i));

                  write(l,string'("No transactions expected on DMA Port "&to_string(p)&"!"));writeline(output,l);
                  for pp in 0 to DMA_PORTS-1 loop
                     write(l,string'("Other expected transactions on DMA Port "&to_string(pp)&":"));writeline(output,l);
                     mvb_mfb_trans_fifo_print(down_send_trans_fifo(pp));
                  end loop;
                  report "" severity failure;
               end if;

               slv_fifo_pop(down_send_trans_fifo(p),trans_ser);
               trans := mvb_mfb_trans_deser(trans_ser);

               if (NO_CHECKING=false and mvb_mfb_trans_cmp(trans,accepted(i))=false) then
                  write(l,string'("Unexpected DOWN transaction received!"));writeline(output,l);
                  mvb_mfb_trans_print(accepted(i));

                  write(l,string'("Expected transaction:"));writeline(output,l);
                  mvb_mfb_trans_print(trans);

                  for pp in 0 to DMA_PORTS-1 loop
                     write(l,string'("Other expected transactions on DMA Port "&to_string(pp)&":"));writeline(output,l);
                     mvb_mfb_trans_fifo_print(down_send_trans_fifo(pp));
                  end loop;
                  report "" severity failure;
               end if;

               -- check ID and Tag
               tag       := accepted(i).tag;
               id        := accepted(i).id;
               completed := accepted(i).completed;
               idtag     := id*2**DMA_PORT_TAG_WIDTH+(tag mod (2**DMA_PORT_TAG_WIDTH));

               if (down_idtag_fifo(p).empty='1') then
                  report "Empty DOWN ID+Tag FIFO!" severity failure;
               else
                  slv_fifo_pop(down_idtag_fifo(p),idtag_vec);
                  expected_id  := to_integer(unsigned(idtag_vec(DMA_ID_WIDTH+DMA_TAG_WIDTH-1 downto DMA_TAG_WIDTH)));
                  expected_tag := to_integer(unsigned(idtag_vec(DMA_TAG_WIDTH-1 downto 0)));
               end if;

               if (NO_CHECKING=false and dma_idtag_free(p)(idtag)='1') then
                  write(l,string'("Already freed DMA ID+Tag pair response received!"));writeline(output,l);
                  write(l,string'("    PCIe Tag: "));
                  write_dec(l,trans.tag);
                  writeline(output,l);
                  write(l,string'("         Tag: "));
                  write_dec(l,tag);
                  write(l,string'("          ID: "));
                  write_dec(l,id);
                  writeline(output,l);
                  write(l,string'("expected Tag: "));
                  write_dec(l,expected_tag);
                  write(l,string'(" expected ID: "));
                  write_dec(l,expected_id);
                  writeline(output,l);
                  report "" severity failure;
               end if;

               if (NO_CHECKING=false and (tag/=expected_tag or id/=expected_id)) then
                  write(l,string'("Incorrect DMA ID+Tag pair response received!"));writeline(output,l);
                  write(l,string'("    PCIe Tag: "));
                  write_dec(l,trans.tag);
                  writeline(output,l);
                  write(l,string'("         Tag: "));
                  write_dec(l,tag);
                  write(l,string'("          ID: "));
                  write_dec(l,id);
                  writeline(output,l);
                  write(l,string'("expected Tag: "));
                  write_dec(l,expected_tag);
                  write(l,string'(" expected ID: "));
                  write_dec(l,expected_id);
                  writeline(output,l);
                  report "" severity failure;
               end if;

               if (completed='1') then
                  -- free ID+Tag pair
                  dma_idtag_free(p)(idtag) := '1';

                  trans_processed_cntr := trans_processed_cntr+1;
                  if (trans_processed_cntr=UP_TRANSACTIONS) then

                     write(l,string'("                                             transactions processed: " & integer'image(trans_processed_cntr) & " / " & integer'image(UP_TRANSACTIONS)));writeline(output,l);
                     success_end;
                  end if;
                  if (trans_processed_cntr=next_print_cntr) then
                     write(l,string'("                                             transactions processed: " & integer'image(trans_processed_cntr) & " / " & integer'image(UP_TRANSACTIONS)));writeline(output,l);
                     next_print_cntr := next_print_cntr+GEN_PRINT_INTERVAL;
                  end if;
               end if;
            end loop;
         end if;

         -- set MVB interface
         s_down_mvb_dst_rdy(p) <= down_mvb_i(p).dst_rdy;
         -- set MFB interface
         s_down_mfb_dst_rdy(p) <= down_mfb_i(p).dst_rdy;
      end loop;
   end process;
   ----

   ---- Tag Manager reservation / dereservation checking
   tag_reserve_release_check_pr : process
      variable seed1 : positive := RAND_SEED+1881;
      variable seed2 : positive := RAND_SEED+1421;
      variable rand  : real;
      variable X     : integer;

      variable res_words : i_array_t(MVB_UP_ITEMS-1 downto 0);
      variable res_vld   : std_logic_vector(MVB_UP_ITEMS-1 downto 0);

      variable res_fifo_di : std_logic_vector(32-1 downto 0);
      variable res_fifo_do : std_logic_vector(32-1 downto 0);

      variable ass_tag : i_array_t(MVB_UP_ITEMS-1 downto 0);
      variable ass_vld : std_logic_vector(MVB_UP_ITEMS-1 downto 0);

      variable rel_tag  : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      variable rel_len  : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      variable rel_comp : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
      variable rel_vld  : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
   begin
      -- Deactivate checking for everything except Virtex7
      if (DEVICE/="7SERIES") then
          wait;
      end if;

      if (reset='1') then
         wait until reset='0';
      end if;

      wait until clk'event and clk='1';

      -- signals assign
      for i in 0 to MVB_UP_ITEMS-1 loop
         res_words(i) := to_integer(<<signal uut.tag_manager_i.s_words_u : u_array_t(MVB_UP_ITEMS-1 downto 0)(WORDS_COUNT_WIDTH-1 downto 0)>>(i));
         res_vld(i)   := <<signal uut.tag_manager_i.s1_reg_vld  : std_logic_vector(MVB_UP_ITEMS-1 downto 0)>>(i)
                     and <<signal uut.tag_manager_i.s1_read_reg : std_logic_vector(MVB_UP_ITEMS-1 downto 0)>>(i)
                     and <<signal uut.tag_manager_i.s2_reg_en : std_logic>>;

         ass_tag(i)   := to_integer(unsigned(pcie_tag_int_to_ext(<<signal uut.tag_manager_i.tag_ass_tag : slv_array_t(MVB_UP_ITEMS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0)>>(i))));
         ass_vld(i)   := <<signal uut.tag_manager_i.tag_ass_vld : std_logic_vector(MVB_UP_ITEMS-1 downto 0)>>(i);
      end loop;

      for i in 0 to MVB_DOWN_ITEMS-1 loop
         rel_tag(i)  := to_integer(unsigned(pcie_tag_int_to_ext(<<signal uut.tag_manager_i.tag_map_read_tag_reg : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(INTERNAL_PCIE_TAG_WIDTH-1 downto 0)>>(i))));
         rel_len(i)  := to_integer(unsigned(<<signal uut.tag_manager_i.pta_in_data_arr : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(A_WORDS_WIDTH-1 downto 0)>>(i)));
         rel_comp(i) := <<signal uut.tag_manager_i.tag_map_read_rel_reg : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0)>>(i);
         rel_vld(i)  := <<signal uut.tag_manager_i.tag_map_read_reg_vld : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0)>>(i);
      end loop;

      -- detect new reservation
      for i in 0 to MVB_UP_ITEMS-1 loop
         if (res_vld(i)='1') then
            res_fifo_di := std_logic_vector(to_unsigned(res_words(i),32));
            slv_fifo_put(tag_reserve_fifo,res_fifo_di);

            if (FULL_PRINT) then
               write(l,string'("                "));
               write(l,now);
               write(l,string'(" : reserve check : Preparing reserve "));
               write_dec(l,res_words(i));
               write(l,string'(" words for yet unknown tag"));
               writeline(output,l);
            end if;
         end if;
      end loop;

      -- detect new release
      for i in 0 to MVB_DOWN_ITEMS-1 loop
         if (rel_vld(i)='1') then
            if (tag_reserve_vld(rel_tag(i))='0') then
               write(l,string'("reserve check : Attempting to release from unassigned PCIe Tag "));
               write_dec(l,rel_tag(i));writeline(output,l);
               report "" severity failure;
            end if;

            if (rel_comp(i)='1') then -- unassign
               if (FULL_PRINT) then
                  write(l,string'("                "));
                  write(l,now);
                  write(l,string'(" : reserve check : Releasing "));
                  write_dec(l,rel_len(i));
                  write(l,string'(" words from PCIe Tag "));
                  write_dec(l,rel_tag(i));
                  write(l,string'(" (completed)"));
                  writeline(output,l);
               end if;

               if (tag_reserve(rel_tag(i))/=rel_len(i)) then
                  write(l,string'("reserve check : Premature 'completed' release for PCIe Tag "));
                  write_dec(l,rel_tag(i));writeline(output,l);
                  write(l,string'("reserve check : Reserved:  "));write_dec(l,tag_reserve(rel_tag(i)));writeline(output,l);
                  write(l,string'("reserve check : Releasing: "));write_dec(l,rel_len(i));writeline(output,l);
                  report "" severity failure;
               end if;

               tag_reserve(rel_tag(i))     := 0;
               tag_reserve_vld(rel_tag(i)) := '0';
            else -- partial release
               if (FULL_PRINT) then
                  write(l,string'("                "));
                  write(l,now);
                  write(l,string'(" : reserve check : Releasing "));
                  write_dec(l,rel_len(i));
                  write(l,string'(" words from PCIe Tag "));
                  write_dec(l,rel_tag(i));
                  write(l,string'(" (now reserved "));
                  write_dec(l,tag_reserve(rel_tag(i))-rel_len(i));
                  write(l,string'(" words)"));
                  writeline(output,l);
               end if;

               if (tag_reserve(rel_tag(i))<rel_len(i)) then
                  write(l,string'("reserve check : Releasing too much space for PCIe Tag "));
                  write_dec(l,rel_tag(i));writeline(output,l);
                  write(l,string'("reserve check : Reserved:  "));write_dec(l,tag_reserve(rel_tag(i)));writeline(output,l);
                  write(l,string'("reserve check : Releasing: "));write_dec(l,rel_len(i));writeline(output,l);
                  report "" severity failure;
               end if;

               if (tag_reserve(rel_tag(i))=rel_len(i) ) then
                  write(l,string'("reserve check : Expected 'completed' release missing for PCIe Tag "));
                  write_dec(l,rel_tag(i));writeline(output,l);
                  write(l,string'("reserve check : Reserved:  "));write_dec(l,tag_reserve(rel_tag(i)));writeline(output,l);
                  write(l,string'("reserve check : Releasing: "));write_dec(l,rel_len(i));writeline(output,l);
                  report "" severity failure;
               end if;

               tag_reserve(rel_tag(i)) := tag_reserve(rel_tag(i))-rel_len(i);
            end if;
         end if;
      end loop;

      -- detect new tag assign
      for i in 0 to MVB_UP_ITEMS-1 loop
         if (ass_vld(i)='1') then
            if (tag_reserve_vld(ass_tag(i))='1') then
               write(l,string'("reserve check : Reserving space for already reserved PCIe Tag "));
               write_dec(l,ass_tag(i));writeline(output,l);
               report "" severity failure;
            end if;

            if (tag_reserve_fifo.empty='1') then
               write(l,string'("reserve check : Reserving from empty FIFO!"));writeline(output,l);
               report "" severity failure;
            end if;

            slv_fifo_pop(tag_reserve_fifo,res_fifo_do);
            tag_reserve(ass_tag(i)) := to_integer(unsigned(res_fifo_do));
            tag_reserve_vld(ass_tag(i)) := '1';

            if (FULL_PRINT) then
               write(l,string'("                "));
               write(l,now);
               write(l,string'(" : reserve check : Reserving "));
               write_dec(l,tag_reserve(ass_tag(i)));
               write(l,string'(" words for PCIe Tag "));
               write_dec(l,ass_tag(i));
               writeline(output,l);
            end if;
         end if;
      end loop;

   end process;
   ----

end architecture behavioral;
