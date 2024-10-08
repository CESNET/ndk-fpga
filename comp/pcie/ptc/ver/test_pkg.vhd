-- test_pkg.vhd: Test Package
-- Copyright (C) 2017 CESNET z. s. p. o.
-- Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

-- ----------------------------------------------------------------------------
--                        DMA BUS package
-- ----------------------------------------------------------------------------
package test_pkg is

   constant C_CLK_PER     : time := 4.0 ns;
   constant C_CLK_DMA_PER : time := 5.0 ns;
   constant C_RST_TIME    : time := 10 * C_CLK_PER + 1 ns;

   -------------------------------
   -- 7SERIES bus configuration
   -------------------------------

   --constant DEVICE        : string  := "7SERIES";
   --constant ENDPOINT_TYPE : string  := "DUMMY"; -- ignored with this DEVICE

   --constant MVB_UP_ITEMS        : integer := 1;

   --constant MFB_UP_REGIONS      : integer := 1;
   --constant MFB_UP_REG_SIZE     : integer := 1;
   --constant MFB_UP_BLOCK_SIZE   : integer := 8;
   --constant MFB_UP_ITEM_WIDTH   : integer := 32;

   --constant DMA_MFB_UP_REGIONS  : integer := MFB_UP_REGIONS*2;

   --constant MFB_UP_ITEMS        : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;
   --constant DMA_MFB_UP_ITEMS    : integer := DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

   --constant MVB_DOWN_ITEMS      : integer := 2;

   --constant MFB_DOWN_REGIONS    : integer := 2;
   --constant MFB_DOWN_REG_SIZE   : integer := 1;
   --constant MFB_DOWN_BLOCK_SIZE : integer := 4;
   --constant MFB_DOWN_ITEM_WIDTH : integer := 32;

   --constant DMA_MFB_DOWN_REGIONS: integer := MFB_DOWN_REGIONS*2;

   --constant MFB_DOWN_ITEMS      : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;
   --constant DMA_MFB_DOWN_ITEMS  : integer := DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;

   --constant RQ_TUSER_WIDTH      : integer := 60;
   --constant RC_TUSER_WIDTH      : integer := 75;

   -------------------------------

   -------------------------------
   -- ULTRASCALE bus configuration
   -------------------------------

   constant DEVICE        : string  := "ULTRASCALE";
   constant ENDPOINT_TYPE : string  := "DUMMY"; -- ignored with this DEVICE

   constant MVB_UP_ITEMS        : integer := 2;

   constant MFB_UP_REGIONS      : integer := 2;
   constant MFB_UP_REG_SIZE     : integer := 1;
   constant MFB_UP_BLOCK_SIZE   : integer := 8;
   constant MFB_UP_ITEM_WIDTH   : integer := 32;

   constant DMA_MFB_UP_REGIONS  : integer := MFB_UP_REGIONS;

   constant MFB_UP_ITEMS        : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;
   constant DMA_MFB_UP_ITEMS    : integer := DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

   constant MVB_DOWN_ITEMS      : integer := 4;

   constant MFB_DOWN_REGIONS    : integer := 4;
   constant MFB_DOWN_REG_SIZE   : integer := 1;
   constant MFB_DOWN_BLOCK_SIZE : integer := 4;
   constant MFB_DOWN_ITEM_WIDTH : integer := 32;

   constant DMA_MFB_DOWN_REGIONS: integer := MFB_DOWN_REGIONS;

   constant MFB_DOWN_ITEMS      : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;
   constant DMA_MFB_DOWN_ITEMS  : integer := DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;

   constant RQ_TUSER_WIDTH      : integer := 137;
   constant RC_TUSER_WIDTH      : integer := 161;

   -------------------------------

   -------------------------------
   -- STRATIX10 bus configuration
   -------------------------------

   --constant DEVICE        : string  := "STRATIX10";
   --constant ENDPOINT_TYPE : string  := "H_TILE";
   ----constant ENDPOINT_TYPE : string  := "P_TILE";

   --constant MVB_UP_ITEMS        : integer := 2;

   --constant MFB_UP_REGIONS      : integer := 2;
   --constant MFB_UP_REG_SIZE     : integer := 1;
   --constant MFB_UP_BLOCK_SIZE   : integer := 8;
   --constant MFB_UP_ITEM_WIDTH   : integer := 32;

   --constant DMA_MFB_UP_REGIONS  : integer := MFB_UP_REGIONS;

   --constant MFB_UP_ITEMS        : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;
   --constant DMA_MFB_UP_ITEMS    : integer := DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

   --constant MVB_DOWN_ITEMS      : integer := 2;

   --constant MFB_DOWN_REGIONS    : integer := 2;
   --constant MFB_DOWN_REG_SIZE   : integer := 1;
   --constant MFB_DOWN_BLOCK_SIZE : integer := 8;
   --constant MFB_DOWN_ITEM_WIDTH : integer := 32;

   --constant DMA_MFB_DOWN_REGIONS: integer := MFB_DOWN_REGIONS;

   --constant MFB_DOWN_ITEMS      : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;
   --constant DMA_MFB_DOWN_ITEMS  : integer := DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;

   --constant RQ_TUSER_WIDTH      : integer := 137;
   --constant RC_TUSER_WIDTH      : integer := 161;

   -------------------------------

   constant DMA_PORTS           : integer := 2;

   constant PCIE_UPHDR_WIDTH    : integer := 128;
   constant PCIE_DOWNHDR_WIDTH  : integer := 3*4*8;
   constant PCIE_PREFIX_WIDTH   : integer := 32;

   constant DMA_TAG_WIDTH       : integer := DMA_REQUEST_TAG'high - DMA_REQUEST_TAG'low + 1;
   constant DMA_ID_WIDTH        : integer := DMA_REQUEST_UNITID'high - DMA_REQUEST_UNITID'low + 1;
   constant DMA_PORT_TAG_WIDTH  : integer := DMA_TAG_WIDTH-log2(DMA_PORTS);

   constant PCIE_TAG_WIDTH      : integer := 8;

   constant UP_ASFIFO_ITEMS     : integer := 512;
   constant DOWN_ASFIFO_ITEMS   : integer := 512;
   constant DOWN_FIFO_ITEMS     : integer := 512;

   constant RCB_SIZE            : integer := 64; -- 64 or 128 [B]

   constant AUTO_ASSIGN_TAGS    : boolean := true;

   constant DMA_ADDR_WIDTH      : integer := DMA_REQUEST_GLOBAL'high - DMA_REQUEST_GLOBAL'low + 1;
   constant DMA_LEN_WIDTH       : integer := DMA_REQUEST_LENGTH'high - DMA_REQUEST_LENGTH'low + 1;
   constant DMA_DATA_WIDTH      : integer := 2**DMA_LEN_WIDTH*32+1;

   constant MFB_UP_DATA_WIDTH   : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH;
   constant MFB_DOWN_DATA_WIDTH : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH;

   constant DMA_MFB_UP_DATA_WIDTH   : integer := DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH;
   constant DMA_MFB_DOWN_DATA_WIDTH : integer := DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH;

   constant MFB_UP_SOF_POS_WIDTH   : integer := max(1,log2(MFB_UP_REG_SIZE));                        -- address of block of region's SOF
   constant MFB_UP_EOF_POS_WIDTH   : integer := max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE));      -- address of item of region's EOF

   constant MFB_DOWN_SOF_POS_WIDTH : integer := max(1,log2(MFB_DOWN_REG_SIZE));                      -- address of block of region's SOF
   constant MFB_DOWN_EOF_POS_WIDTH : integer := max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE));  -- address of item of region's EOF

   constant AXI_UP_SOP_POS_WIDTH : integer := log2(MFB_UP_REGIONS*MFB_UP_REG_SIZE)+1;
   constant AXI_UP_EOP_POS_WIDTH : integer := log2(MFB_UP_ITEMS);

   constant AXI_DOWN_SOP_POS_WIDTH : integer := log2(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE);
   constant AXI_DOWN_EOP_POS_WIDTH : integer := log2(MFB_DOWN_ITEMS);

   constant AVAILABLE_WORDS        : integer := DOWN_FIFO_ITEMS;
   constant A_WORDS_WIDTH          : integer := log2(AVAILABLE_WORDS+1);
   constant WORDS_COUNT_WIDTH      : integer := log2(2**DMA_LEN_WIDTH*2-(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH/32)-MFB_DOWN_REGIONS)+1;

   -- verification parameters
   -- common
   constant UP_TRANSACTIONS     : integer  := 8*10**3; -- total number of transactions generated before end
   constant GEN_PRINT_INTERVAL  : integer  := 200; -- number of generated transactions between generator info printing

   constant FULL_PRINT          : boolean  := false; -- switches printing of every send and received transaction (slows down simulation)
   constant RAND_SEED           : positive := 24242; -- random seed value

   -- verification inner parameters
   constant DEFAULT_DATA_VALUE  : integer := 42;

   constant NO_CHECKING         : boolean := false; -- turns verification checking off for the purpose of verification developement

   constant VER_FIFO_SIZE       : integer := 1024; -- size of verification internal FIFOs

   -- UP MVB+MFB generator settings
   constant UP_NOT_SRC_RDY_CHANCE : integer := 50; -- [%] (max - 99)
   constant UP_READ_CHANCE        : integer := 70;   -- [%]
   constant UP_READ_LEN_MIN       : integer := MFB_UP_ITEM_WIDTH/32; -- [dword] (max - 2**10-1)
   constant UP_READ_LEN_MAX       : integer := 2**10-1; -- [dword] (max - 2**10-1)
   constant UP_READ_START_ALIGN_CHANCE : integer := 50; -- [%] - chance, that a read transaction's start addr is aligned to RCB_SIZE
   constant UP_READ_END_ALIGN_CHANCE   : integer := 50; -- [%] - chance, that a read transaction's end   addr is aligned to RCB_SIZE
   constant UP_WRITE_LEN_MIN    : integer := MFB_UP_ITEM_WIDTH/32; -- [dword] (max - 2**10-1)
   constant UP_WRITE_LEN_MAX    : integer := 2**10-1; -- [dword] (max - 2**10-1)
   constant UP_GAP_CHANCE       : integer := 80;    -- [%]
   constant UP_GAP_LEN_MIN      : integer := 1;     -- [dword] (max - max_int)
   constant UP_GAP_LEN_MAX      : integer := 2**6;  -- [dword] (max - max_int)
   -- UP AXI accepting settings
   constant RQ_TREADY_CHANCE    : integer := 70; -- [%]

   constant TAG_ASS_SEND_CHANCE : integer := 40; -- [%]
   -- DOWN AXI sending settings
   constant DOWN_RESPONSE_DELAY_MIN    : integer := 60; -- [CLK] - minimal number of CLK between read request and read response (minimum 2 required by Tag manager assign latency)
   constant DOWN_RESPONSE_START_CHANCE : integer := 30; -- [%] - chance to start sending one of awaiting read responses

   constant DOWN_RESPONSE_PART_LEN_MIN : integer := 1;             -- [RCB_SIZE]
   constant DOWN_RESPONSE_PART_LEN_MAX : integer := 1024/RCB_SIZE; -- [RCB_SIZE]
   constant DOWN_GAP_CHANCE            : integer := 80;   -- [%]
   constant DOWN_GAP_LEN_MIN           : integer := 1;    -- [dword]
   constant DOWN_GAP_LEN_MAX           : integer := 2**6; -- [dword]
   -- DOWN MVB+MFB accepting settings
   constant DOWN_NOT_DST_RDY_CHANCE : integer := 60; -- [%]
   ----

   type str_array_t is array (natural range <>) of string;
   type str_array_2d_t is array (natural range <>) of str_array_t;

   -- MVB+MFB packet
   type mvb_mfb_trans_t is record
      payload          : std_logic; -- is write transaction
      address          : unsigned(DMA_ADDR_WIDTH-1 downto 0); -- target address of write / read request [Byte]
      length           : integer; -- total length of write / read request / completion part [DWORD]
      remaining_bytes  : integer; -- total length of remaining cempletion parts (including this one) [Byte]
      after_gap_length : integer; -- length of empty space after transaction payload [DWORD]
      data             : std_logic_vector(DMA_DATA_WIDTH-1 downto 0); -- payload data
      data_rd_ptr      : integer; -- current read pointer for payload data
      tag              : integer; -- transaction tag (PCIe/DMA)
      id               : integer; -- transaction unitid (DMA)
      completed        : std_logic; -- last part of read response
      is_down          : std_logic; -- is completion transaction
   end record;

   constant MVB_MFB_TRANS_WIDTH : integer := 1+DMA_ADDR_WIDTH+32+32+DMA_DATA_WIDTH+32+32+32+32+1+1;

   type mvb_mfb_trans_array_t is array (natural range <>) of mvb_mfb_trans_t;
   ----

   -- MVB interface
   type mvb_i_t is record
      data    : std_logic_vector;
      vld     : std_logic_vector;
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;

   type mvb_i_arr_t is array (natural range <>) of mvb_i_t;
   ----

   -- MFB interface
   type mfb_i_t is record
      data    : std_logic_vector;
      sof     : std_logic_vector;
      eof     : std_logic_vector;
      sof_pos : std_logic_vector;
      eof_pos : std_logic_vector;
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;

   type mfb_i_arr_t is array (natural range <>) of mfb_i_t;
   ----

   -- RQ tUser signal
   type rq_tuser_t is record
      eop_pos  : i_array_t(MFB_UP_REGIONS-1 downto 0);
      eop      : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
      sop_pos  : i_array_t(MFB_UP_REGIONS-1 downto 0);
      sop      : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
      last_be  : slv_array_t(MFB_UP_REGIONS-1 downto 0)(4-1 downto 0);
      first_be : slv_array_t(MFB_UP_REGIONS-1 downto 0)(4-1 downto 0);
   end record;
   ----

   -- RQ interface
   type rq_i_t is record
      tuser  : rq_tuser_t;
      tdata  : std_logic_vector(MFB_UP_DATA_WIDTH-1 downto 0);
      tlast  : std_logic;                                         -- ignore in straddle AXI
      tkeep  : std_logic_vector(MFB_UP_DATA_WIDTH/32-1 downto 0); -- ignore in straddle AXI
      tready : std_logic;
      tvalid : std_logic;
   end record;
   ----

   -- RC tUser signal
   type rc_tuser_t is record
      eop_pos : i_array_t(MFB_DOWN_REGIONS-1 downto 0);
      eop     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
      sop_pos : i_array_t(MFB_DOWN_REGIONS-1 downto 0);
      sop     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
      be      : std_logic_vector((MFB_DOWN_ITEMS*MFB_DOWN_ITEM_WIDTH)/8-1 downto 0);
   end record;
   ----

   -- RC interface
   type rc_i_t is record
      tuser  : rc_tuser_t;
      tdata  : std_logic_vector(MFB_DOWN_DATA_WIDTH-1 downto 0);
      tlast  : std_logic;                                           -- ignore in straddle AXI
      tkeep  : std_logic_vector(MFB_DOWN_DATA_WIDTH/32-1 downto 0); -- ignore in straddle AXI
      tready : std_logic;
      tvalid : std_logic;
   end record;
   ----

   -- function and procedure declarations

   -- conditional constants
   function PCIE_LOW_ADDR_WIDTH return integer;

   -- MVB+MFB transactions operations
   function mvb_mfb_trans_ser(t : mvb_mfb_trans_t) return std_logic_vector;
   function mvb_mfb_trans_deser(t : std_logic_vector) return mvb_mfb_trans_t;
   procedure mvb_mfb_trans_new(trans : out mvb_mfb_trans_t; seed1 : inout positive; seed2 : inout positive; payload : std_logic; address : unsigned; length : integer; after_gap_length : integer; tag : integer; id : integer; completed : std_logic; is_down : std_logic);
   procedure mvb_mfb_trans_new(trans : out mvb_mfb_trans_t; seed1 : inout positive; seed2 : inout positive; payload : std_logic; address : unsigned; length : integer; remaining_bytes : integer; after_gap_length : integer; tag : integer; id : integer; completed : std_logic; is_down : std_logic);
   procedure mvb_mfb_trans_new_rand(trans : out mvb_mfb_trans_t; seed1 : inout positive; seed2 : inout positive; dma_port : in integer; free_idtag_map : inout std_logic_vector;
                                   min_length : integer; max_length : integer; read : std_logic; after_gap_chance : integer;
                                   ag_min : integer; ag_max : integer; is_down : std_logic);
   procedure mvb_mfb_trans_merge(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t; ret_val : out mvb_mfb_trans_t);
   procedure mvb_mfb_trans_split(t : mvb_mfb_trans_t; t0_length : integer; t0_after_gap_length : integer; ret_val : out mvb_mfb_trans_array_t);
   function mvb_mfb_trans_cmp(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t) return boolean;
   procedure mvb_mfb_trans_print(t : mvb_mfb_trans_t);
   procedure mvb_mfb_trans_fifo_print(fifo : slv_fifo_t);

   -- RQ tuser operations
   function rq_tuser_ser(tu : rq_tuser_t) return std_logic_vector;
   function rq_tuser_deser(tu : std_logic_vector) return rq_tuser_t;
   -- RC tuser operations
   function rc_tuser_ser(tu : rc_tuser_t) return std_logic_vector;
   function rc_tuser_deser(tu : std_logic_vector) return rc_tuser_t;

   -- RC, RQ and MFB conversions
   function mfb2rq_conv(mfb_i : mfb_i_t) return rq_i_t;
   function rc2mfb_conv(rc_i : rc_i_t) return mfb_i_t;

   -- fill std_logic_vector
   procedure repeated_fill(vec : out std_logic_vector; value : integer);

   -- MFB ptr work
   function get_block_ptr(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;
   function get_reg_ptr(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;
   function shift_to_next_reg(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;
   function shift_to_next_block(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;

   -- UP MB+MFB generation
   procedure insert_trans_part_in_mvb_mfb_word(trans : inout mvb_mfb_trans_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer);
   procedure post_new_up_mvb_mfb_word(fifo : inout slv_fifo_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t;
                                      new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector);

   -- RQ accepting
   procedure accept_rq_word(rq_i : inout rq_i_t; rq_mvb_i : inout mvb_i_t; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer;
                            unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector;
                            free_tags : inout std_logic_vector; new_tags : out i_array_t; new_tags_vld : out std_logic_vector;
                            seed1 : inout positive; seed2 : inout positive);

   -- RC generation
   procedure insert_trans_part_in_rc_word(trans : inout mvb_mfb_trans_t; rc_i : inout rc_i_t; rc_mvb_i : inout mvb_i_t; mfb_i_ptr : inout integer;
                                          sop_ptr : inout integer; eop_ptr : inout integer; send_header : boolean);
   procedure post_new_rc_word(rc_i : inout rc_i_t; rc_mvb_i : inout mvb_i_t; response_remaining_addr : inout u_array_t; response_remaining_len : inout i_array_t; response_vld : inout std_logic_vector;
                              unfinished : inout mvb_mfb_trans_t; unfinished_vld : inout std_logic;
                              new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector; seed1 : inout positive; seed2 : inout positive);

   -- DOWN MVB+MFB accepting
   procedure accept_mvb_mfb_word(mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer;
                                 unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic;
                                 accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector; seed1 : inout positive; seed2 : inout positive);
   ----
end test_pkg;

-- ----------------------------------------------------------------------------
--                        DMA BUS package body
-- ----------------------------------------------------------------------------

package body test_pkg is

   -- generates conditional value for a constant
   function PCIE_LOW_ADDR_WIDTH return integer is
      variable width : integer := 12;
   begin
      width := 12;
      if (DEVICE="STRATIX10") then
         width := 7;
      end if;
      return width;
   end function;

   -- mvb mfb serialization
   function mvb_mfb_trans_ser(t : mvb_mfb_trans_t) return std_logic_vector is
      variable l1  : integer := 1;
      variable l2  : integer := l1+DMA_ADDR_WIDTH;
      variable l3  : integer := l2+32;
      variable l4  : integer := l3+32;
      variable l5  : integer := l4+32;
      variable l6  : integer := l5+DMA_DATA_WIDTH;
      variable l7  : integer := l6+32;
      variable l8  : integer := l7+32;
      variable l9  : integer := l8+32;
      variable l10 : integer := l9+1;
      variable l11 : integer := l10+1;
      variable vec : std_logic_vector(l11-1 downto 0);
   begin
      vec := t.is_down
           & t.completed
           & std_logic_vector(to_unsigned(t.id,32))
           & std_logic_vector(to_unsigned(t.tag,32))
           & std_logic_vector(to_unsigned(t.data_rd_ptr,32))
           & t.data
           & std_logic_vector(to_unsigned(t.after_gap_length,32))
           & std_logic_vector(to_unsigned(t.remaining_bytes,32))
           & std_logic_vector(to_unsigned(t.length,32))
           & std_logic_vector(t.address)
           & t.payload;
       return vec;
   end function;
   ----

   -- mvb mfb serialization
   function mvb_mfb_trans_deser(t : std_logic_vector) return mvb_mfb_trans_t is
      variable l1  : integer := 1;
      variable l2  : integer := l1+DMA_ADDR_WIDTH;
      variable l3  : integer := l2+32;
      variable l4  : integer := l3+32;
      variable l5  : integer := l4+32;
      variable l6  : integer := l5+DMA_DATA_WIDTH;
      variable l7  : integer := l6+32;
      variable l8  : integer := l7+32;
      variable l9  : integer := l8+32;
      variable l10 : integer := l9+1;
      variable l11 : integer := l10+1;
      variable trans : mvb_mfb_trans_t;
   begin
      trans.payload          :=                     t(l1 -1);
      trans.address          :=            unsigned(t(l2 -1 downto l1));
      trans.length           := to_integer(unsigned(t(l3 -1 downto l2)));
      trans.remaining_bytes  := to_integer(unsigned(t(l4 -1 downto l3)));
      trans.after_gap_length := to_integer(unsigned(t(l5 -1 downto l4)));
      trans.data             :=                     t(l6 -1 downto l5);
      trans.data_rd_ptr      := to_integer(unsigned(t(l7 -1 downto l6)));
      trans.tag              := to_integer(unsigned(t(l8 -1 downto l7)));
      trans.id               := to_integer(unsigned(t(l9 -1 downto l8)));
      trans.completed        :=                     t(l10-1);
      trans.is_down          :=                     t(l11-1);
      return trans;
   end function;
   ----

   -- mvb+mfb transactions creation
   procedure mvb_mfb_trans_new(trans : out mvb_mfb_trans_t; seed1 : inout positive; seed2 : inout positive; payload : std_logic; address : unsigned; length : integer; after_gap_length : integer; tag : integer; id : integer; completed : std_logic; is_down : std_logic) is
   begin
      trans.payload             := payload;
      trans.address             := address;
      trans.length              := length;
      trans.remaining_bytes     := length*4;
      trans.after_gap_length    := after_gap_length;
      random_vector_proc(seed1,seed2,trans.data);
      trans.data_rd_ptr         := 0;
      trans.tag                 := tag;
      trans.id                  := id;
      trans.completed           := completed;
      trans.is_down             := is_down;
   end procedure;
   ----

   -- mvb+mfb transactions creation (with remaining_bytes defined)
   procedure mvb_mfb_trans_new(trans : out mvb_mfb_trans_t; seed1 : inout positive; seed2 : inout positive; payload : std_logic; address : unsigned; length : integer; remaining_bytes : integer; after_gap_length : integer; tag : integer; id : integer; completed : std_logic; is_down : std_logic) is
   begin
      trans.payload             := payload;
      trans.address             := address;
      trans.length              := length;
      trans.remaining_bytes     := remaining_bytes;
      trans.after_gap_length    := after_gap_length;
      random_vector_proc(seed1,seed2,trans.data);
      trans.data_rd_ptr         := 0;
      trans.tag                 := tag;
      trans.id                  := id;
      trans.completed           := completed;
      trans.is_down             := is_down;
   end procedure;
   ----

   -- mvb+mfb random transaction creation
   procedure mvb_mfb_trans_new_rand(trans : out mvb_mfb_trans_t; seed1 : inout positive; seed2 : inout positive; dma_port : in integer; free_idtag_map : inout std_logic_vector; min_length : integer; max_length : integer; read : std_logic; after_gap_chance : integer; ag_min : integer; ag_max : integer; is_down : std_logic) is
      variable rand : real;
      variable X : integer;
      variable l : line;
      variable e : boolean;
      variable s1,s2 : positive;
   begin
      s1 := seed1;
      s2 := seed2;

      e := false;
      if ((or free_idtag_map)='0' and read='1') then
         e := true;
         write(l,string'("No free ID Tag pair!"));writeline(output,l);
      end if;
      if (min_length>max_length) then
         e := true;
         write(l,string'("Min length "));
         write_dec(l,min_length);
         write(l,string'(" is over Max length "));
         write_dec(l,max_length);
         writeline(output,l);
      end if;
      if (ag_min>ag_max and after_gap_chance>0) then
         e := true;
         write(l,string'("Min gap length "));
         write_dec(l,ag_min);
         write(l,string'(" is over Max gap length "));
         write_dec(l,ag_max);
         writeline(output,l);
      end if;
      if (e) then
         report "Unpossible random MVB+MFB transaction generation parameters set!" severity failure;
      end if;

      trans.payload := not read;

      uniform(s1,s2,rand);
      X := integer(rand*real(max_length-min_length))+min_length;
      trans.length := X;

      uniform(s1,s2,rand);
      X := integer(rand*real(100));
      trans.after_gap_length := 0;
      if (X<after_gap_chance) then
         uniform(s1,s2,rand);
         X := integer(rand*real(ag_max-ag_min))+ag_min;

         trans.after_gap_length := X;
      end if;

      random_val_index(free_idtag_map,'1',s1,s2,X);
      trans.id  := X/(2**DMA_PORT_TAG_WIDTH);
      trans.tag := (dma_port*2**DMA_PORT_TAG_WIDTH) + (X mod (2**DMA_PORT_TAG_WIDTH));
      free_idtag_map(X) := '0';

      trans.data        := random_vector(DMA_DATA_WIDTH,s1);
      trans.data_rd_ptr := 0;

      trans.address             := (others => '0');
      trans.address(DMA_ADDR_WIDTH/4-1 downto 0) := unsigned(random_vector(DMA_ADDR_WIDTH/4,s2));
      trans.address(1 downto 0) := "00";

      trans.completed := '0';
      trans.is_down   := is_down;

      if (read='1') then
         randint(seed1,seed2,0,99,X);
         if (X<UP_READ_START_ALIGN_CHANCE) then
            trans.address := trans.address-(trans.address mod RCB_SIZE);
         elsif (trans.address=trans.address-(trans.address mod RCB_SIZE)) then
            randint(seed1,seed2,1,RCB_SIZE/4-1,X);
            trans.address := trans.address+X*4;
         end if;

         randint(seed1,seed2,0,99,X);
         if (X<UP_READ_END_ALIGN_CHANCE) then
            trans.length := trans.length-to_integer(((trans.address+trans.length*4) mod RCB_SIZE)/4);
            if (trans.length=0) then
               trans.length := RCB_SIZE/4;
            end if;
         elsif (trans.length=trans.length-((trans.address+trans.length*4) mod RCB_SIZE)/4) then
            randint(seed1,seed2,1,RCB_SIZE/4-1,X);
            trans.length := trans.length-X;
            if (trans.length<=0) then
               trans.length := 1;
            end if;
         end if;
      end if;
      trans.remaining_bytes := trans.length*4;

      seed1 := s1;
      seed2 := s2;
   end procedure;
   ----

   -- mvb+mfb transaction print
   procedure mvb_mfb_trans_print(t : mvb_mfb_trans_t) is
      variable l : line;
      variable l_ptr : integer;

      variable block_s : integer := 4; -- [B]
      variable line_s  : integer := 8; -- [blocks]
   begin
      write(l,string'(""));writeline(output,l);
      write(l,string'("--"));
      if (t.is_down='0') then
         write(l,string'("UP TRANS--"));
      else
         write(l,string'("DOWN TRANS--"));
      end if;
      writeline(output,l);
      if (t.is_down='0') then
         if (t.payload='1') then
            write(l,string'("| Type: Write"));
         else
            write(l,string'("| Type: Read "));
         end if;
         write(l,string'(" | Address: 0x"));write_hex(l,t.address);
      else
         write(l,string'("| Completed: "));write_dec(l,unsigned'(0 => t.completed));
         write(l,string'(" | Address low: 0x"));write_hex(l,std_logic_vector(t.address));
      end if;
      write(l,string'(" | Length: " & integer'image(t.length)));
      write(l,string'(" | Tag: " & integer'image(t.tag)));
      write(l,string'(" | ID: " & integer'image(t.id)));
      write(l,string'(" | DMA Port: "));write_dec(l,resize_right(t.address,log2(DMA_PORTS)));
      write(l,string'(" |"));writeline(output,l);
      if (t.payload='1') then
         write(l,string'("| Data pointer: " & integer'image(t.data_rd_ptr)));
         write(l,string'(" | Gap length: " & integer'image(t.after_gap_length)));
         write(l,string'(" |"));writeline(output,l);

         for i in 0 to t.length*32/8/line_s/block_s+1-1 loop
            if (i*line_s*block_s>=t.length*32/8) then
               exit;
            end if;

            write(l,string'("  "));
            for e in 0 to line_s-1 loop
               if (i*line_s*block_s+e*block_s>=t.length*32/8) then
                  exit;
               end if;

               for g in 0 to block_s-1 loop
                  write_hex(l,t.data(line_s*block_s*8*i+block_s*8*e+8*(g+1)-1 downto line_s*block_s*8*i+block_s*8*e+8*g));
                  write(l,string'(" "));
               end loop;
               write(l,string'(" "));
            end loop;
            writeline(output,l);
         end loop;
      end if;
      write(l,string'(""));writeline(output,l);
   end procedure;
   ----

   -- prints all items in FIFO as MVB+MFB transaction
   procedure mvb_mfb_trans_fifo_print(fifo : slv_fifo_t) is
      variable trans_ser : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);

      variable l : line;
   begin
      for i in 0 to fifo.fill-1 loop
         write(l,string'("item: "));
         write_dec(l,i);
         writeline(output,l);

         trans_ser := fifo.fifo(i);
         mvb_mfb_trans_print(mvb_mfb_trans_deser(trans_ser));
      end loop;
   end procedure;
   ----

   -- add t1 to t0
   procedure mvb_mfb_trans_merge(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t; ret_val : out mvb_mfb_trans_t) is
      variable trans : mvb_mfb_trans_t;
      variable e : boolean;
   begin
      e := false;
      if (t0.payload/='1' or t1.payload/='1') then
         report "Merging 2 non-payload transactions!";
         e := true;
      end if;
      if (t0.tag/=t1.tag) then
         report "Merging 2 non-payload transactions with different tags!";
         e := true;
      end if;
      if (t0.id/=t1.id) then
         report "Merging 2 non-payload transactions with different IDs!";
         e := true;
      end if;
      if (e) then
         report "T1";
         mvb_mfb_trans_print(t0);
         report "T2";
         mvb_mfb_trans_print(t1);
         assert (false) severity failure;
      end if;

      trans := t0;
      trans.length := t0.length + t1.length;
      trans.remaining_bytes := t0.remaining_bytes + t1.remaining_bytes;
      trans.data(trans.length*32-1 downto t0.length*32) := t1.data(t1.length*32-1 downto 0);
      trans.after_gap_length := t1.after_gap_length;
      trans.completed := t0.completed or t1.completed;
      ret_val := trans;
   end procedure;
   ----

   -- mvb+mfb write transaction split to two transactions
   procedure mvb_mfb_trans_split(t : mvb_mfb_trans_t; t0_length : integer; t0_after_gap_length : integer; ret_val : out mvb_mfb_trans_array_t) is
      variable s_t : mvb_mfb_trans_array_t(2-1 downto 0);
      variable e : boolean;
   begin
      e := false;
      if (t.payload/='1') then
         report "Attempting to split a non-payload transaction!";
         e := true;
      end if;
      if (t0_length<=0 or t0_length>=t.length) then
         report "Incorrect length for transaction splitting " & integer'image(t0_length) & "!";
         e := true;
      end if;
      if (e) then
         mvb_mfb_trans_print(t);
         assert (false) severity failure;
      end if;

      s_t(0) := t;
      s_t(1) := t;

      s_t(1).length := t.length-t0_length;
      s_t(1).remaining_bytes := (t.length-t0_length)*4;
      s_t(1).data(s_t(1).length-1 downto 0) := t.data(t.length-1 downto t0_length);

      if (t.data_rd_ptr>=t0_length) then
         s_t(0).data_rd_ptr := 0;
         s_t(1).data_rd_ptr := t.data_rd_ptr-t0_length;
      else
         s_t(1).data_rd_ptr := 0;
      end if;

      s_t(0).length := t0_length;
      s_t(0).remaining_bytes := t0_length*4;
      s_t(0).after_gap_length := t0_after_gap_length;

      s_t(0).completed := '0';

      ret_val := s_t;
   end procedure;
   ----

   -- mvb+mfb transactions are equal
   function mvb_mfb_trans_cmp(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t) return boolean is
   begin
      if (t0.payload/=t1.payload or t0.length/=t1.length or (t0.address/=t1.address and t0.is_down='0')) then
         return false;
      elsif (t0.payload='1' and t0.data(t0.length*32-1 downto 0)/=t1.data(t0.length*32-1 downto 0)) then
         return false;
      else
         return true;
      end if;
   end function;
   ----

   -- fill std_logic_vector with repeated 8-bit value
   procedure repeated_fill(vec : out std_logic_vector; value : integer) is
   begin
      for i in 0 to vec'length/8-1 loop
         vec(vec'low+8*(i+1)-1 downto vec'low+8*i) := std_logic_vector(to_unsigned(value,8));
      end loop;
      vec(vec'low+vec'length-1 downto vec'low+8*(vec'length/8)) := std_logic_vector(to_unsigned(value,vec'length mod 8));
   end procedure;
   ----

   -- MFB word pointer operations
   function get_block_ptr(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer is
   begin
      return mfb_i_ptr/MFB_BLOCK_SIZE;
   end function;

   function get_reg_ptr(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer is
      variable mfb_block_ptr : integer;
   begin
      mfb_block_ptr := get_block_ptr(mfb_i_ptr,MFB_REG_SIZE,MFB_BLOCK_SIZE);
      return mfb_block_ptr/MFB_REG_SIZE;
   end function;

   function shift_to_next_reg(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer is
      variable mfb_reg_ptr : integer;
   begin
      mfb_reg_ptr   := get_reg_ptr(mfb_i_ptr,MFB_REG_SIZE,MFB_BLOCK_SIZE);
      if ((mfb_i_ptr mod (MFB_REG_SIZE*MFB_BLOCK_SIZE))/=0) then
         mfb_reg_ptr := mfb_reg_ptr+1;
      end if;

      return mfb_reg_ptr*MFB_REG_SIZE*MFB_BLOCK_SIZE;
   end function;

   function shift_to_next_block(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer is
      variable mfb_block_ptr : integer;
   begin
      mfb_block_ptr := get_block_ptr(mfb_i_ptr,MFB_REG_SIZE,MFB_BLOCK_SIZE);
      if ((mfb_i_ptr mod MFB_BLOCK_SIZE)/=0) then
         mfb_block_ptr := mfb_block_ptr+1;
      end if;

      return mfb_block_ptr*MFB_BLOCK_SIZE;
   end function;
   ----

   -- insert part of MVB+MFB transaction in MVB and MFB word
   procedure insert_trans_part_in_mvb_mfb_word(trans : inout mvb_mfb_trans_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer) is
      variable mvb_item : std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);

      variable mfb_block_ptr : integer;
      variable mfb_reg_ptr   : integer;

      variable l : line;
   begin
      if (trans.data_rd_ptr=0) then -- start of transaction
         -- insert MVB item
         mvb_i.src_rdy := '1';

         mvb_i.vld(mvb_i_ptr) := '1';

         repeated_fill(mvb_item,DEFAULT_DATA_VALUE);

         mvb_item(DMA_REQUEST_GLOBAL) := std_logic_vector(trans.address);
         mvb_item(DMA_REQUEST_LENGTH) := std_logic_vector(to_unsigned(trans.length,DMA_LEN_WIDTH));
         mvb_item(DMA_REQUEST_TYPE)   := DMA_TYPE_WRITE when trans.payload='1' else DMA_TYPE_READ;
         mvb_item(DMA_REQUEST_TAG)    := std_logic_vector(to_unsigned(trans.tag,DMA_TAG_WIDTH));
         mvb_item(DMA_REQUEST_UNITID) := std_logic_vector(to_unsigned(trans.id,DMA_ID_WIDTH));
         mvb_item(DMA_REQUEST_FIRSTIB):= "00";
         mvb_item(DMA_REQUEST_LASTIB) := "00";

         mvb_i.data(DMA_UPHDR_WIDTH*(mvb_i_ptr+1)-1 downto DMA_UPHDR_WIDTH*mvb_i_ptr) := mvb_item;

         mvb_i_ptr := mvb_i_ptr+1;
      end if;

      if (trans.payload='1') then -- transaction with payload
         if (trans.data_rd_ptr<trans.length*32) then
            if (trans.data_rd_ptr=0) then -- start of transaction
               mfb_block_ptr := get_block_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);
               mfb_reg_ptr   := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);

               mfb_i.sof(mfb_reg_ptr) := '1';
               mfb_i.sof_pos(MFB_UP_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_UP_SOF_POS_WIDTH*mfb_reg_ptr) := std_logic_vector(to_unsigned((mfb_i_ptr mod MFB_UP_REG_SIZE),MFB_UP_SOF_POS_WIDTH));
            end if;

            -- send data
            mfb_i.src_rdy := '1';

            while (mfb_i_ptr<DMA_MFB_UP_ITEMS and trans.data_rd_ptr<trans.length*32) loop
               mfb_i.data(MFB_UP_ITEM_WIDTH*(mfb_i_ptr+1)-1 downto MFB_UP_ITEM_WIDTH*mfb_i_ptr) := trans.data(trans.data_rd_ptr+MFB_UP_ITEM_WIDTH-1 downto trans.data_rd_ptr);
               trans.data_rd_ptr := trans.data_rd_ptr + MFB_UP_ITEM_WIDTH;

               if (trans.data_rd_ptr=trans.length*32) then -- end of transaction data
                  mfb_block_ptr := get_block_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);
                  mfb_reg_ptr   := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);

                  mfb_i.eof(mfb_reg_ptr) := '1';
                  mfb_i.eof_pos(MFB_UP_EOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_UP_EOF_POS_WIDTH*mfb_reg_ptr) := std_logic_vector(to_unsigned((mfb_i_ptr mod (MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE)),MFB_UP_EOF_POS_WIDTH));
               elsif (trans.data_rd_ptr>trans.length*32) then -- ERROR
                  report "Data read pointer overflow! Incorrect MFB data align!";
                  mvb_mfb_trans_print(trans);
                  report "" severity failure;
               end if;

               mfb_i_ptr := mfb_i_ptr+1;
            end loop;
         end if;

         if (trans.data_rd_ptr>=trans.length*32 and trans.data_rd_ptr<(trans.length+trans.after_gap_length)*32) then
            -- send gap

            while (mfb_i_ptr<DMA_MFB_UP_ITEMS and trans.data_rd_ptr<(trans.length+trans.after_gap_length)*32) loop
               repeated_fill(mfb_i.data(MFB_UP_ITEM_WIDTH*(mfb_i_ptr+1)-1 downto MFB_UP_ITEM_WIDTH*mfb_i_ptr),42);
               trans.data_rd_ptr := trans.data_rd_ptr + MFB_UP_ITEM_WIDTH;

               if (trans.data_rd_ptr>(trans.length+trans.after_gap_length)*32) then -- ERROR
                  report "Data read pointer overflow! Incorrect MFB data align!";
                  mvb_mfb_trans_print(trans);
                  report "" severity failure;
               end if;

               mfb_i_ptr := mfb_i_ptr+1;
            end loop;
         end if;
      end if;
   end procedure;
   ----

   -- post new MVB+MFB word from MVB+MFB FIFO (adds all newly started transactions to new_trans_send (their valids are in new_trans_send_vld))
   procedure post_new_up_mvb_mfb_word(fifo : inout slv_fifo_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector) is
      variable dummy : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);
      variable trans : mvb_mfb_trans_t;

      variable mvb_i_ptr        : integer; -- points to MVB ITEM
      variable mfb_i_ptr        : integer; -- points to MFB ITEM
      variable mfb_block_ptr    : integer; -- points to MFB BLOCK
      variable mfb_reg_ptr      : integer; -- points to MFB REGION

      variable l : line;
   begin
      new_trans_send_vld := (MVB_UP_ITEMS-1 downto 0 => '0');
      if (fifo.empty='1') then
         if (mvb_i.dst_rdy='1') then
            mvb_i.src_rdy := '0';
         end if;
         if (mfb_i.dst_rdy='1') then
            mfb_i.src_rdy := '0';
         end if;
         return;
      end if;

      mvb_i_ptr := 0;
      mfb_i_ptr := 0;

      if (mvb_i.dst_rdy='0' and mfb_i.dst_rdy='0') then ---------
         -- do nothing
         dummy := (others => '0');
      elsif (mvb_i.dst_rdy='0' and mfb_i.dst_rdy='1') then ---------
         -- if front transaction has send header, than send its next part
         mfb_i.src_rdy := '0';
         mfb_i.sof     := (DMA_MFB_UP_REGIONS-1 downto 0 => '0');
         mfb_i.eof     := (DMA_MFB_UP_REGIONS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         if (trans.payload='1' and trans.data_rd_ptr>0) then
            insert_trans_part_in_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
            fifo.fifo(0) := mvb_mfb_trans_ser(trans);

            if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- ended sending this transaction
               slv_fifo_pop(fifo,dummy);
            end if;
         end if;
      elsif (mvb_i.dst_rdy='1' and mfb_i.dst_rdy='0') then ---------
         -- send all front transactions, that don't have a payload
         mvb_i.src_rdy := '0';
         mvb_i.vld     := (MVB_UP_ITEMS-1 downto 0 => '0');

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         for i in 0 to MVB_UP_ITEMS-1 loop
            exit when (trans.payload='1');

            new_trans_send(mvb_i_ptr)     := trans;
            new_trans_send_vld(mvb_i_ptr) := '1';
            insert_trans_part_in_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);

            slv_fifo_pop(fifo,dummy);

            exit when (fifo.empty='1');

            trans := mvb_mfb_trans_deser(fifo.fifo(0));
         end loop;
      elsif (mvb_i.dst_rdy='1' and mfb_i.dst_rdy='1') then ---------
         -- send anything
         mfb_i.src_rdy := '0';
         mfb_i.sof     := (DMA_MFB_UP_REGIONS-1 downto 0 => '0');
         mfb_i.eof     := (DMA_MFB_UP_REGIONS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         mvb_i.src_rdy := '0';
         mvb_i.vld     := (MVB_UP_ITEMS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         while true loop
            if (trans.payload='0') then
               -- no payload
               new_trans_send(mvb_i_ptr)     := trans;
               new_trans_send_vld(mvb_i_ptr) := '1';
               insert_trans_part_in_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
               fifo.fifo(0) := mvb_mfb_trans_ser(trans);

               slv_fifo_pop(fifo,dummy);

               exit when (fifo.empty='1');

               trans := mvb_mfb_trans_deser(fifo.fifo(0));

               exit when (mvb_i_ptr=MVB_UP_ITEMS); -- filled the whole MVB word
            else
               -- yes payload
               if (trans.data_rd_ptr=0) then
                  -- start
                  mfb_i_ptr := shift_to_next_block(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE); -- new packet must start a new block

                  exit when (mfb_i_ptr=DMA_MFB_UP_ITEMS); -- shifted out of this MFB word

                  mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);
                  if (mfb_i.sof(mfb_reg_ptr)='1') then
                     mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE); -- two packet must not start in the same region
                  end if;

                  exit when (mfb_i_ptr=DMA_MFB_UP_ITEMS); -- shifted out of this MFB word

                  new_trans_send(mvb_i_ptr)     := trans;
                  new_trans_send_vld(mvb_i_ptr) := '1';

                  insert_trans_part_in_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
                  fifo.fifo(0) := mvb_mfb_trans_ser(trans);

                  if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- end of transaction
                     slv_fifo_pop(fifo,dummy);

                     exit when (fifo.empty='1');

                     trans := mvb_mfb_trans_deser(fifo.fifo(0));
                  end if;

                  exit when (mfb_i_ptr=DMA_MFB_UP_ITEMS); -- filled the whole MFB word
                  exit when (mvb_i_ptr=MVB_UP_ITEMS); -- filled the whole MVB word
               else
                  -- continue
                  insert_trans_part_in_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
                  fifo.fifo(0) := mvb_mfb_trans_ser(trans);

                  if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- end of transaction
                     slv_fifo_pop(fifo,dummy);

                     exit when (fifo.empty='1');

                     trans := mvb_mfb_trans_deser(fifo.fifo(0));
                  end if;

                  exit when (mfb_i_ptr=DMA_MFB_UP_ITEMS); -- filled the whole MFB word
                  exit when (mvb_i_ptr=MVB_UP_ITEMS); -- filled the whole MVB word
               end if;
            end if;
         end loop;
      end if;
   end procedure;
   ----

   -- RQ tuser record serialization
   function rq_tuser_ser(tu : rq_tuser_t) return std_logic_vector is
      variable l1 : integer := MFB_UP_REGIONS*4;
      variable l2 : integer := l1+MFB_UP_REGIONS*4;
      variable l3 : integer := l2+4;
      variable l4 : integer := l3+MFB_UP_REGIONS;
      variable l5 : integer := l4+MFB_UP_REGIONS*AXI_UP_SOP_POS_WIDTH;
      variable l6 : integer := l5+MFB_UP_REGIONS;
      variable l7 : integer := l6+MFB_UP_REGIONS*AXI_UP_EOP_POS_WIDTH;
      variable l8 : integer := RQ_TUSER_WIDTH;
      variable vec : std_logic_vector(l8-1 downto 0);
   begin
      vec := (others => '0');

      for i in 0 to MFB_UP_REGIONS-1 loop
         vec( 0+4*(i+1)-1 downto  0+4*i) := tu.first_be(i);
         vec(l1+4*(i+1)-1 downto l1+4*i) := tu.last_be(i);
      end loop;

      if (DEVICE="ULTRASCALE") then
         vec(l4-1 downto l3) := tu.sop;

         for i in 0 to MFB_UP_REGIONS-1 loop
            vec(l4+AXI_UP_SOP_POS_WIDTH*(i+1)-1 downto l4+AXI_UP_SOP_POS_WIDTH*i) := std_logic_vector(to_unsigned(tu.sop_pos(i),AXI_UP_SOP_POS_WIDTH));
         end loop;

         vec(l6-1 downto l5) := tu.eop;

         for i in 0 to MFB_UP_REGIONS-1 loop
            vec(l6+AXI_UP_EOP_POS_WIDTH*(i+1)-1 downto l6+AXI_UP_EOP_POS_WIDTH*i) := std_logic_vector(to_unsigned(tu.eop_pos(i),AXI_UP_EOP_POS_WIDTH));
         end loop;
      end if;

      return vec;
   end function;
   ----

   -- RQ tuser signal deserialization
   function rq_tuser_deser(tu : std_logic_vector) return rq_tuser_t is
      variable l1 : integer := MFB_UP_REGIONS*4;
      variable l2 : integer := l1+MFB_UP_REGIONS*4;
      variable l3 : integer := l2+4;
      variable l4 : integer := l3+MFB_UP_REGIONS;
      variable l5 : integer := l4+MFB_UP_REGIONS*AXI_UP_SOP_POS_WIDTH;
      variable l6 : integer := l5+MFB_UP_REGIONS;
      variable l7 : integer := l6+MFB_UP_REGIONS*AXI_UP_EOP_POS_WIDTH;
      variable l8 : integer := RQ_TUSER_WIDTH;
      variable tuser : rq_tuser_t;
   begin
      for i in 0 to MFB_UP_REGIONS-1 loop
         tuser.first_be(i) := tu( 0+4*(i+1)-1 downto  0+4*i);
         tuser.last_be(i)  := tu(l1+4*(i+1)-1 downto l1+4*i);
      end loop;

      if (DEVICE="ULTRASCALE") then
         tuser.sop := tu(l4-1 downto l3);

         for i in 0 to MFB_UP_REGIONS-1 loop
            tuser.sop_pos(i) := to_integer(unsigned(tu(l4+AXI_UP_SOP_POS_WIDTH*(i+1)-1 downto l4+AXI_UP_SOP_POS_WIDTH*i)));
         end loop;

         tuser.eop := tu(l6-1 downto l5);

         for i in 0 to MFB_UP_REGIONS-1 loop
            tuser.eop_pos(i) := to_integer(unsigned(tu(l6+AXI_UP_EOP_POS_WIDTH*(i+1)-1 downto l6+AXI_UP_EOP_POS_WIDTH*i)));
         end loop;
       end if;

      return tuser;
   end function;
   ----

   -- RC tuser record serialization
   function rc_tuser_ser(tu : rc_tuser_t) return std_logic_vector is
      variable l1 : integer := (MFB_DOWN_ITEMS*MFB_DOWN_ITEM_WIDTH)/8;
      variable l2 : integer := l1+MFB_DOWN_REGIONS;
      variable l3 : integer := l2+log2(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE)*MFB_DOWN_REGIONS;
      variable l4 : integer := l3+MFB_DOWN_REGIONS;
      variable l5 : integer := l4+log2(MFB_DOWN_ITEMS)*MFB_DOWN_REGIONS;
      variable vec : std_logic_vector(RC_TUSER_WIDTH-1 downto 0);
   begin
      vec := (others => '0');
      vec(l1-1 downto  0) := tu.be;

      vec(l2-1 downto l1) := tu.sop;

      if (DEVICE="ULTRASCALE") then
         for i in 0 to MFB_DOWN_REGIONS-1 loop
            vec(l2+AXI_DOWN_SOP_POS_WIDTH*(i+1)-1 downto l2+AXI_DOWN_SOP_POS_WIDTH*i) := std_logic_vector(to_unsigned(tu.sop_pos(i),AXI_DOWN_SOP_POS_WIDTH));
         end loop;

         vec(l4-1 downto l3) := tu.eop;

         for i in 0 to MFB_DOWN_REGIONS-1 loop
            vec(l4+AXI_DOWN_EOP_POS_WIDTH*(i+1)-1 downto l4+AXI_DOWN_EOP_POS_WIDTH*i) := std_logic_vector(to_unsigned(tu.eop_pos(i),AXI_DOWN_EOP_POS_WIDTH));
         end loop;
      else
         for i in 0 to MFB_DOWN_REGIONS-1 loop
            vec(l2+(AXI_DOWN_EOP_POS_WIDTH+1)*i) := tu.eop(i);
            vec(l2+(AXI_DOWN_EOP_POS_WIDTH+1)*(i+1)-1 downto l2+(AXI_DOWN_EOP_POS_WIDTH+1)*i+1) := std_logic_vector(to_unsigned(tu.eop_pos(i),AXI_DOWN_EOP_POS_WIDTH));
         end loop;
      end if;

      return vec;
   end function;
   ----

   -- RC tuser signal deserialization
   function rc_tuser_deser(tu : std_logic_vector) return rc_tuser_t is
      variable l1 : integer := (MFB_DOWN_ITEMS*MFB_DOWN_ITEM_WIDTH)/8;
      variable l2 : integer := l1+MFB_DOWN_REGIONS;
      variable l3 : integer := l2+log2(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE)*MFB_DOWN_REGIONS;
      variable l4 : integer := l3+MFB_DOWN_REGIONS;
      variable l5 : integer := l4+log2(MFB_DOWN_ITEMS)*MFB_DOWN_REGIONS;
      variable tuser : rc_tuser_t;
   begin
      tuser.be  := tu(l1-1 downto  0);

      tuser.sop := tu(l2-1 downto l1);

      if (DEVICE="ULTRASCALE") then
         for i in 0 to MFB_DOWN_REGIONS-1 loop
            tuser.sop_pos(i) := to_integer(unsigned(tu(l2+AXI_DOWN_SOP_POS_WIDTH*(i+1)-1 downto l2+AXI_DOWN_SOP_POS_WIDTH*i)));
         end loop;

         tuser.eop := tu(l4-1 downto l3);

         for i in 0 to MFB_DOWN_REGIONS-1 loop
            tuser.eop_pos(i) := to_integer(unsigned(tu(l4+AXI_DOWN_EOP_POS_WIDTH*(i+1)-1 downto l4+AXI_DOWN_EOP_POS_WIDTH*i)));
         end loop;
      else
         tuser.sop_pos := (others => 0);

         for i in 0 to MFB_DOWN_REGIONS-1 loop
            tuser.eop(i)     := tu(l2+(AXI_DOWN_EOP_POS_WIDTH+1)*i);
            tuser.eop_pos(i) := to_integer(unsigned(tu(l2+(AXI_DOWN_EOP_POS_WIDTH+1)*(i+1)-1 downto l2+(AXI_DOWN_EOP_POS_WIDTH+1)*i+1)));
         end loop;
      end if;

      return tuser;
   end function;
   ----

   -- MFB to RQ interface conversion
   function mfb2rq_conv(mfb_i : mfb_i_t) return rq_i_t is
      variable sop_ptr : integer;
      variable eop_ptr : integer;
      variable rq_i : rq_i_t;
   begin
      rq_i.tuser.sop := (others => '0');
      rq_i.tuser.eop := (others => '0');
      rq_i.tuser.sop_pos := (others => 0);
      rq_i.tuser.eop_pos := (others => 0);
      sop_ptr := 0;
      eop_ptr := 0;
      for i in 0 to MFB_UP_REGIONS-1 loop
         rq_i.tuser.sop    (sop_ptr) := mfb_i.sof(i);
         rq_i.tuser.eop    (eop_ptr) := mfb_i.eof(i);
         rq_i.tuser.sop_pos(sop_ptr) := to_integer(unsigned(mfb_i.sof_pos((i+1)*log2(MFB_UP_REG_SIZE)-1 downto i*log2(MFB_UP_REG_SIZE))))*2+i*MFB_UP_REG_SIZE*2;
         rq_i.tuser.eop_pos(eop_ptr) := to_integer(unsigned(mfb_i.eof_pos((i+1)*log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE)-1 downto i*log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))))+i*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;
         if (mfb_i.sof(i)='1') then
            sop_ptr := sop_ptr+1;
         end if;
         if (mfb_i.eof(i)='1') then
            eop_ptr := eop_ptr+1;
         end if;
      end loop;

      rq_i.tdata  := mfb_i.data;
      rq_i.tvalid := mfb_i.src_rdy;
      rq_i.tready := mfb_i.dst_rdy;
      return rq_i;
   end function;
   ----

   -- RC to MFB interface conversion
   function rc2mfb_conv(rc_i : rc_i_t) return mfb_i_t is
      variable sop_ptr : integer;
      variable eop_ptr : integer;
      variable mfb_i   : mfb_i_t
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
   begin
      mfb_i.sof := (others => '0');
      mfb_i.eof := (others => '0');
      sop_ptr := 0;
      eop_ptr := 0;
      for i in 0 to MFB_DOWN_REGIONS-1 loop
         if (rc_i.tuser.sop_pos(sop_ptr)/(MFB_DOWN_REG_SIZE)=i) then
            mfb_i.sof(i) := rc_i.tuser.sop    (sop_ptr);
            mfb_i.sof_pos((i+1)*log2(MFB_DOWN_REG_SIZE)-1 downto i*log2(MFB_DOWN_REG_SIZE)) := std_logic_vector(to_unsigned(rc_i.tuser.sop_pos(sop_ptr),log2(MFB_DOWN_REG_SIZE)));
            sop_ptr := sop_ptr+1;
         end if;
         if (rc_i.tuser.eop_pos(eop_ptr)/(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE)=i) then
            mfb_i.eof(i) := rc_i.tuser.eop    (eop_ptr);
            mfb_i.eof_pos((i+1)*log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE)-1 downto i*log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE)) := std_logic_vector(to_unsigned(rc_i.tuser.eop_pos(eop_ptr),log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE)));
            eop_ptr := eop_ptr+1;
         end if;
      end loop;

      mfb_i.data    := rc_i.tdata;
      mfb_i.src_rdy := rc_i.tvalid;
      mfb_i.dst_rdy := rc_i.tready;

      return mfb_i;
   end function;
   ----

   -- RQ word accept; checks AXI comunination signals validity and accepts data from rq_tdata (accepted contains new completed transactions; new_tag contains pcie tags assigned to accepted read transactions)
   procedure accept_rq_word(rq_i : inout rq_i_t; rq_mvb_i : inout mvb_i_t; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector; free_tags : inout std_logic_vector; new_tags : out i_array_t; new_tags_vld : out std_logic_vector; seed1 : inout positive; seed2 : inout positive) is
      variable mfb_i_ptr     : integer;
      variable mfb_r_ptr     : integer;

      variable sop_ptr      : integer;
      variable eop_ptr      : integer;
      variable new_tag_ptr  : integer;

      variable trans0 : mvb_mfb_trans_t;
      variable trans1 : mvb_mfb_trans_t;

      variable pcie_up_hdr  : std_logic_vector(PCIE_UPHDR_WIDTH-1 downto 0);
      variable pcie_payload : std_logic;
      variable pcie_type    : std_logic; -- header size type (128-bit of 96-bit) for Stratix 10)
      variable pcie_address_vec : std_logic_vector(DMA_ADDR_WIDTH-1 downto 0);
      variable pcie_address : unsigned(DMA_ADDR_WIDTH-1 downto 0);
      variable pcie_length  : integer;
      variable pcie_tag     : integer;
      variable pcie_tag_tmp : unsigned(PCIE_TAG_WIDTH-1 downto 0);

      variable l : line;

      variable X  : integer;
   begin
      if (DEVICE="7SERIES") then
         -- fake sop, eop, sop_pos and eop_pos
         rq_i.tuser.sop(0) := '1' when rq_i.tvalid='1' and unfinished_vld='0' else '0';
         rq_i.tuser.eop(0) := rq_i.tlast;
         rq_i.tuser.sop_pos(0) := 0;
         rq_i.tuser.eop_pos(0) := 0;
         for i in 0 to MFB_UP_DATA_WIDTH/MFB_UP_ITEM_WIDTH-1 loop
            exit when (rq_i.tkeep(i*MFB_UP_ITEM_WIDTH/32)='0');
            rq_i.tuser.eop_pos(0) := i;
         end loop;
      end if;

      accepted_vld := (accepted_vld'length-1 downto 0 => '0');
      new_tags_vld := (new_tags_vld'length-1 downto 0 => '0');

      if (rq_i.tready='0') then
         return;
      end if;

      if (rq_i.tvalid='0') then
         if (unfinished_vld='1') then
            write(l,now);write(l,string'(" : "));
            write(l,string'("UP AXI tvalid fall during transaction transmition!"));writeline(output,l);
            write(l,string'("Unfinished transaction: "));writeline(output,l);
            mvb_mfb_trans_print(unfinished);
            report "" severity failure;
         end if;
      else
         mfb_i_ptr   := 0;
         sop_ptr     := 0;
         eop_ptr     := 0;
         new_tag_ptr := 0;

         if (unfinished_vld='1') then
            mvb_mfb_trans_new(trans0,seed1,seed2,'1',to_unsigned(0,DMA_ADDR_WIDTH),0,0,unfinished.tag,unfinished.id,'0','0');

            -- continuing transaction
            if (rq_i.tuser.eop(0)='0') then
               -- no end of packet in this word
               mvb_mfb_trans_new(trans0,seed1,seed2,'1',unfinished.address,MFB_UP_DATA_WIDTH/32,0,unfinished.tag,unfinished.id,'0','0');
               trans0.data(MFB_UP_DATA_WIDTH-1 downto 0) := rq_i.tdata;

               mvb_mfb_trans_merge(unfinished,trans0,trans1);
               unfinished := trans1;
            else
               -- finish the unfinished
               mvb_mfb_trans_new(trans0,seed1,seed2,'1',unfinished.address,(rq_i.tuser.eop_pos(0)+1)*MFB_UP_ITEM_WIDTH/32,0,unfinished.tag,unfinished.id,'0','0');
               trans0.data((rq_i.tuser.eop_pos(0)+1)*32-1 downto 0) := rq_i.tdata((rq_i.tuser.eop_pos(0)+1)*32-1 downto 0);

               mvb_mfb_trans_merge(unfinished,trans0,trans1);
               unfinished := trans1;

               if (unfinished.length/=unfinished_expected_len) then
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("UP AXI incorrect length in multiple-word write transaction!"));writeline(output,l);
                  write(l,string'("Unfinished transaction: "));writeline(output,l);
                  mvb_mfb_trans_print(unfinished);
                  write(l,string'("expected length: "));
                  write_dec(l,unfinished_expected_len);
                  writeline(output,l);
                  report "" severity failure;
               end if;

               accepted(eop_ptr)     := unfinished;
               accepted_vld(eop_ptr) := '1';
               eop_ptr               := 1;
               unfinished_vld  := '0';
            end if;

            mfb_i_ptr := trans0.length*32/MFB_UP_ITEM_WIDTH;
            if (mfb_i_ptr=MFB_UP_ITEMS) then
               return;
            end if;
         end if;

         -- accept new transactions

         while (rq_i.tuser.sop(sop_ptr)='1') loop
            if (unfinished_vld='1') then
               write(l,now);write(l,string'(" : "));
               write(l,string'("UP AXI new transaction before previous transaction's end!"));writeline(output,l);
               write(l,string'("Unfinished transaction: "));writeline(output,l);
               mvb_mfb_trans_print(unfinished);
               report "" severity failure;
            end if;

            mfb_i_ptr := rq_i.tuser.sop_pos(sop_ptr)/2*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

            if (DEVICE="STRATIX10" and ENDPOINT_TYPE="P_TILE") then -- header present on separated MVB interface
               mfb_r_ptr   := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);
               pcie_up_hdr := rq_mvb_i.data(mfb_r_ptr*PCIE_UPHDR_WIDTH+PCIE_UPHDR_WIDTH-1 downto mfb_r_ptr*PCIE_UPHDR_WIDTH);
               if (rq_mvb_i.src_rdy='0' or rq_mvb_i.vld(mfb_r_ptr)='0') then -- MVB item should be valid on SOP, but isn't
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("UP AXI missing SOP-aligned header on RQ MVB interface!"));writeline(output,l);
                  report "" severity failure;
               end if;
            else -- header included in the classic RQ interface
               pcie_up_hdr := rq_i.tdata(mfb_i_ptr*MFB_UP_ITEM_WIDTH+PCIE_UPHDR_WIDTH-1 downto mfb_i_ptr*MFB_UP_ITEM_WIDTH);
            end if;

            if (DEVICE="STRATIX10") then -- Intel
               pcie_payload := pcie_up_hdr(30);
               pcie_type    := pcie_up_hdr(29);
               if (pcie_type='1') then -- 128-bit header
                  pcie_address_vec := pcie_up_hdr(PCIE_UPHDR_WIDTH-32-1 downto PCIE_UPHDR_WIDTH-64) & pcie_up_hdr(PCIE_UPHDR_WIDTH-1 downto PCIE_UPHDR_WIDTH-32);
                  pcie_address     := unsigned(pcie_address_vec);
                  if (ENDPOINT_TYPE/="P_TILE") then -- with P_TILE the header is not part of the MFB word
                     mfb_i_ptr := mfb_i_ptr+PCIE_UPHDR_WIDTH/MFB_UP_ITEM_WIDTH;
                  end if;
               else -- 96-bit header
                  pcie_address_vec := (32-1 downto 0 => '0') & pcie_up_hdr(PCIE_UPHDR_WIDTH-32-1 downto PCIE_UPHDR_WIDTH-64);
                  pcie_address     := unsigned(pcie_address_vec);
                  if (ENDPOINT_TYPE/="P_TILE") then -- with P_TILE the header is not part of the MFB word
                     mfb_i_ptr := mfb_i_ptr+PCIE_UPHDR_WIDTH/MFB_UP_ITEM_WIDTH-1;
                  end if;
               end if;
               pcie_length  := to_integer(unsigned(pcie_up_hdr(DMA_LEN_WIDTH-1 downto 0)));
               pcie_tag_tmp := unsigned(pcie_up_hdr(PCIE_TAG_WIDTH+40-1 downto 40));
               if (PCIE_TAG_WIDTH=10) then -- with 10-bit Tag the two most significant bits are placed on different positions
                   pcie_tag_tmp(8-1 downto 0) := unsigned(pcie_up_hdr(8+40-1 downto 40));
                   pcie_tag_tmp(8)            := pcie_up_hdr(19);
                   pcie_tag_tmp(9)            := pcie_up_hdr(23);
               end if;
               pcie_tag     := to_integer(pcie_tag_tmp);
            else -- Xilinx
               pcie_payload := pcie_up_hdr(DMA_ADDR_WIDTH+DMA_LEN_WIDTH);
               pcie_address := unsigned(pcie_up_hdr(DMA_ADDR_WIDTH-1 downto 0));
               pcie_length  := to_integer(unsigned(pcie_up_hdr(DMA_LEN_WIDTH+DMA_ADDR_WIDTH-1 downto DMA_ADDR_WIDTH)));
               pcie_tag     := to_integer(unsigned(pcie_up_hdr(PCIE_TAG_WIDTH+8+DMA_REQUEST_VFID'high+1-DMA_REQUEST_VFID'low+1+3+1+DMA_LEN_WIDTH+DMA_ADDR_WIDTH-1 downto 8+DMA_REQUEST_VFID'high+1-DMA_REQUEST_VFID'low+1+3+1+DMA_LEN_WIDTH+DMA_ADDR_WIDTH)));
               mfb_i_ptr    := mfb_i_ptr+PCIE_UPHDR_WIDTH/MFB_UP_ITEM_WIDTH;
            end if;

            if (rq_i.tuser.eop(eop_ptr)='1') then
               -- transaction starts and ends in this word
               if (pcie_payload='1') then
                  -- new write transaction; check correct eop_pos
                  mvb_mfb_trans_new(trans0,seed1,seed2,pcie_payload,pcie_address,((rq_i.tuser.eop_pos(eop_ptr)+1)*32-mfb_i_ptr*MFB_UP_ITEM_WIDTH)/32,0,pcie_tag,0,'0','0');
                  trans0.data((rq_i.tuser.eop_pos(eop_ptr)+1)*32-mfb_i_ptr*MFB_UP_ITEM_WIDTH-1 downto 0) := rq_i.tdata((rq_i.tuser.eop_pos(eop_ptr)+1)*32-1 downto mfb_i_ptr*MFB_UP_ITEM_WIDTH);

                  if (trans0.length/=pcie_length) then
                     write(l,now);write(l,string'(" : "));
                     write(l,string'("UP AXI incorrect length in single-word write transaction!"));writeline(output,l);
                     write(l,string'("Transaction: "));writeline(output,l);
                     mvb_mfb_trans_print(trans0);
                     write(l,string'("expected length: "));
                     write_dec(l,pcie_length);
                     writeline(output,l);
                     report "" severity failure;
                  end if;
               else
                  -- new read transaction accepted

                  if (AUTO_ASSIGN_TAGS) then
                     -- get the actual tag from the transaction header
                     X := pcie_tag;

                     if (free_tags(X)='0') then
                        write(l,now);write(l,string'(" : "));
                        write(l,string'("UP AXI with already taken Tag "));
                        write_dec(l,X);writeline(output,l);
                        write(l,string'("Transaction: "));writeline(output,l);
                        mvb_mfb_trans_print(trans0);
                        report "" severity failure;
                     end if;
                  else
                     -- assign a new tag
                     random_val_index(free_tags,'1',seed1,seed2,X);

                     if (X=-1) then
                        report "No more free PCIe tags to assign!" severity failure; -- avoid this situation when setting rq_i.tready
                     end if;
                  end if;

                  new_tags(new_tag_ptr)     := X;
                  new_tags_vld(new_tag_ptr) := '1';
                  free_tags(X)              := '0';
                  new_tag_ptr := new_tag_ptr+1;

                  mvb_mfb_trans_new(trans0,seed1,seed2,pcie_payload,pcie_address,pcie_length,0,X,0,'0','0'); -- set transacasction's tag to assigned PCIe tag (needed for response generation)
               end if;

               accepted(eop_ptr)     := trans0;
               accepted_vld(eop_ptr) := '1';

               mfb_i_ptr := (rq_i.tuser.eop_pos(eop_ptr)+1)*32/MFB_UP_ITEM_WIDTH;
               eop_ptr   := eop_ptr+1;
            else
               -- transaction continues to next word
               mvb_mfb_trans_new(trans0,seed1,seed2,pcie_payload,pcie_address,(MFB_UP_DATA_WIDTH-mfb_i_ptr*MFB_UP_ITEM_WIDTH)/32,0,pcie_tag,0,'0','0');
               trans0.data(MFB_UP_DATA_WIDTH-mfb_i_ptr*MFB_UP_ITEM_WIDTH-1 downto 0) := rq_i.tdata(MFB_UP_DATA_WIDTH-1 downto mfb_i_ptr*MFB_UP_ITEM_WIDTH);

               if (trans0.payload='0') then
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("UP AXI read transaction did not fit in one word!"));writeline(output,l);
                  write(l,string'("Transaction: "));writeline(output,l);
                  mvb_mfb_trans_print(trans0);
                  writeline(output,l);
                  report "" severity failure;
               end if;

               unfinished := trans0;
               unfinished_expected_len := pcie_length;
               unfinished_vld := '1';

               mfb_i_ptr := MFB_UP_ITEMS;
            end if;

            if (mfb_i_ptr>MFB_UP_ITEMS) then
               report "UP AXI word read pointer overflow!" severity failure;
            end if;

--            exit when (mfb_i_ptr=MFB_UP_ITEMS);

            sop_ptr := sop_ptr+1;
            exit when (sop_ptr=MVB_UP_ITEMS);
         end loop;
      end if;
   end procedure;
   ----

   -- insert next part of transaction in MFB word in RC interface starting at item mfb_i_ptr
   -- if send_header==true then trans.data_rd_ptr must be 0 and there must be enough space for the PCIe header
   procedure insert_trans_part_in_rc_word(trans : inout mvb_mfb_trans_t; rc_i : inout rc_i_t; rc_mvb_i : inout mvb_i_t; mfb_i_ptr : inout integer; sop_ptr : inout integer; eop_ptr : inout integer; send_header : boolean) is
      variable mfb_r_ptr : integer := 0;
      variable tag_tmp   : unsigned(PCIE_TAG_WIDTH-1 downto 0);
   begin
      if (send_header) then
         -- insert PCIe header
         rc_i.tvalid := '1';
         rc_i.tuser.sop(sop_ptr)     := '1';
         rc_i.tuser.sop_pos(sop_ptr) := get_block_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
         sop_ptr := sop_ptr+1;

         if (DEVICE="STRATIX10") then
            if (ENDPOINT_TYPE="P_TILE") then -- on Stratix10 P_TILE the header is placed in a separated MVB interface
               mfb_r_ptr               := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
               rc_mvb_i.vld(mfb_r_ptr) := '1';
               rc_mvb_i.src_rdy        := '1';

               rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+PCIE_LOW_ADDR_WIDTH+64-1 downto mfb_r_ptr*PCIE_DOWNHDR_WIDTH+64) := std_logic_vector(trans.address(PCIE_LOW_ADDR_WIDTH-1 downto 0)); -- ADDR low
               rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+10                    -1 downto mfb_r_ptr*PCIE_DOWNHDR_WIDTH   ) := std_logic_vector(to_unsigned(trans.length,10)); -- dword count

               tag_tmp := to_unsigned(trans.tag,PCIE_TAG_WIDTH);
               if (PCIE_TAG_WIDTH=10) then -- the 2 MSB bits are placed on different positions
                  rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+8             +72     -1 downto mfb_r_ptr*PCIE_DOWNHDR_WIDTH+72) := std_logic_vector(tag_tmp(8-1 downto 0));
                  rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+19)                                                              := tag_tmp(8);
                  rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+23)                                                              := tag_tmp(9);
               else
                  rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+PCIE_TAG_WIDTH+72     -1 downto mfb_r_ptr*PCIE_DOWNHDR_WIDTH+72) := std_logic_vector(tag_tmp); -- tag
               end if;

               rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+12+32                 -1 downto mfb_r_ptr*PCIE_DOWNHDR_WIDTH+32) := std_logic_vector(to_unsigned(trans.remaining_bytes,12)); -- byte count (number of bytes remaining)
               rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+30) := '1'; -- completion
               rc_mvb_i.data(mfb_r_ptr*PCIE_DOWNHDR_WIDTH+29) := '0'; -- completion
            else
               rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+PCIE_LOW_ADDR_WIDTH+64-1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+64) := std_logic_vector(trans.address(PCIE_LOW_ADDR_WIDTH-1 downto 0)); -- ADDR low
               rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+10                    -1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH   ) := std_logic_vector(to_unsigned(trans.length,10)); -- dword count

               tag_tmp := to_unsigned(trans.tag,PCIE_TAG_WIDTH);
               if (PCIE_TAG_WIDTH=10) then -- the 2 MSB bits are placed on different positions
                  rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+8             +72     -1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+72) := std_logic_vector(tag_tmp(8-1 downto 0));
                  rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+19)                                                               := tag_tmp(8);
                  rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+23)                                                               := tag_tmp(9);
               else
                  rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+PCIE_TAG_WIDTH+72     -1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+72) := std_logic_vector(tag_tmp); -- tag
               end if;


               rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+12+32                 -1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+32) := std_logic_vector(to_unsigned(trans.remaining_bytes,12)); -- byte count (number of bytes remaining)
               rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+30) := '1'; -- completion
               rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+29) := '0'; -- completion
            end if;
         else
            rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+PCIE_LOW_ADDR_WIDTH-1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH)  := std_logic_vector(trans.address(PCIE_LOW_ADDR_WIDTH-1 downto 0));
            rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+32+DMA_LEN_WIDTH-1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+32)  := std_logic_vector(to_unsigned(trans.length,DMA_LEN_WIDTH));
            rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+64+PCIE_TAG_WIDTH-1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+64) := std_logic_vector(to_unsigned(trans.tag,PCIE_TAG_WIDTH));
            rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+30)                                                          := '1' when trans.completed else '0';
         end if;

         if (DEVICE/="STRATIX10" or ENDPOINT_TYPE/="P_TILE") then -- on Stratix10 P_TILE the header is placed in a separated MVB interface
            mfb_i_ptr := mfb_i_ptr+PCIE_DOWNHDR_WIDTH/MFB_DOWN_ITEM_WIDTH;
         end if;
      end if;

      -- insert data
      while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
         exit when (trans.data_rd_ptr>=trans.length*32);

         -- insert one item of data
         rc_i.tvalid := '1';
         rc_i.tdata(MFB_DOWN_ITEM_WIDTH*(mfb_i_ptr+1)-1 downto MFB_DOWN_ITEM_WIDTH*mfb_i_ptr) := trans.data(trans.data_rd_ptr+MFB_DOWN_ITEM_WIDTH-1 downto trans.data_rd_ptr);
         trans.data_rd_ptr := trans.data_rd_ptr+MFB_DOWN_ITEM_WIDTH;

         if (trans.data_rd_ptr>trans.length*32) then
            report "DOWN AXI transaction data read pointer overflow! Probably unaligned transaction length!" severity failure;
         end if;

         if (trans.data_rd_ptr=trans.length*32) then
            -- end of transaction data
            rc_i.tuser.eop(eop_ptr)     := '1';
            rc_i.tuser.eop_pos(eop_ptr) := mfb_i_ptr;
            eop_ptr := eop_ptr+1;
         end if;

         mfb_i_ptr := mfb_i_ptr+1;
      end loop;

      -- insert gap
      while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
         exit when (trans.data_rd_ptr>=(trans.length+trans.after_gap_length)*32);

         -- insert one item of gap
         repeated_fill(rc_i.tdata(MFB_DOWN_ITEM_WIDTH*(mfb_i_ptr+1)-1 downto MFB_DOWN_ITEM_WIDTH*mfb_i_ptr),42);
         trans.data_rd_ptr := trans.data_rd_ptr+MFB_DOWN_ITEM_WIDTH;

         if (trans.data_rd_ptr>(trans.length+trans.after_gap_length)*32) then
            report "DOWN AXI transaction data read pointer overflow! Probably unaligned transaction gap length!" severity failure;
         end if;

         mfb_i_ptr := mfb_i_ptr+1;
      end loop;
   end procedure;
   ----

   -- post new RC word
   -- rc_i                                               - interface status
   -- rc_mvb_i                                           - MVB interface status (Stratix10 P_TILE only)
   -- response_remaining_addr(PCIE_TAG_WIDTH-1 downto 0) - address of awaiting responses
   --                        (DMA_ADDR_WIDTH-1 downto 0) -
   -- response_remaining_len(PCIE_TAG_WIDTH-1 downto 0)  - remaining length to send of each awaiting response
   -- response_vld(PCIE_TAG_WIDTH-1 downto 0)            - valid bit for each awaiting response
   -- unfinished                                         - transaction, whose part was send in previous word
   -- unfinished_vld                                     - valid bit for worked transaction
   -- new_trans_send(MVB_DOWN_ITEMS-1 downto 0)          - newly posted transaction
   -- new_trans_send_vld(MVB_DOWN_ITEMS-1 downto 0)      - valid bit for each newly send posted transaction
   -- seed1, seed2                                       - random seed
   procedure post_new_rc_word(rc_i : inout rc_i_t; rc_mvb_i : inout mvb_i_t; response_remaining_addr : inout u_array_t; response_remaining_len : inout i_array_t; response_vld : inout std_logic_vector; unfinished : inout mvb_mfb_trans_t; unfinished_vld : inout std_logic; new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector; seed1 : inout positive; seed2 : inout positive) is
      variable X     : integer;

      variable mfb_i_ptr : integer;
      variable new_t_ptr : integer;

      variable sop_ptr : integer;
      variable eop_ptr : integer;

      variable tag        : integer;
      variable address    : unsigned(DMA_ADDR_WIDTH-1 downto 0) := (others => '0');
      variable length     : integer;
      variable gap_length : integer;
      variable completed  : std_logic;
      variable trans      : mvb_mfb_trans_t;

      variable rcbs       : integer;

      variable l : line;
   begin
      new_trans_send_vld := (MVB_DOWN_ITEMS-1 downto 0 => '0');
      if (rc_i.tready='0') then
         if (DEVICE="7SERIES") then
            report "RC_DST_RDY fall! Not allowerd on Device 7SERIES!";
            report "" severity failure;
         end if;
         -- do nothing
         return;
      end if;

      rc_mvb_i.src_rdy := '0';
      rc_mvb_i.vld     := (MFB_DOWN_REGIONS-1 downto 0 => '0');

      rc_i.tvalid := '0';
      rc_i.tuser.sop     := (others => '0');
      rc_i.tuser.sop_pos := (others => 0);
      rc_i.tuser.eop     := (others => '0');
      rc_i.tuser.eop_pos := (others => 0);
      rc_i.tuser.be      := (others => '0'); -- ignored value
      rc_i.tlast         := '0'; -- ignored value
      rc_i.tkeep         := (others => '0'); -- ignored value
      repeated_fill(rc_i.tdata,42);

      mfb_i_ptr   := 0;
      new_t_ptr   := 0;
      sop_ptr     := 0;
      eop_ptr     := 0;

      if (unfinished_vld='1') then
         -- send next part of continuing transaction
         insert_trans_part_in_rc_word(unfinished,rc_i,rc_mvb_i,mfb_i_ptr,sop_ptr,eop_ptr,false);
         if (unfinished.data_rd_ptr=(unfinished.length+unfinished.after_gap_length)*32) then
            -- transaction ended
            unfinished_vld := '0';
         end if;
      end if;

      mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE); -- new transaction must start at the beginning of a region

      if (DEVICE="7SERIES" and rc_i.tuser.eop(0)='0' and mfb_i_ptr<MFB_DOWN_ITEMS) then
         -- in Virtex 7 Series standard a transaction cannot start in region 1, if there are no data in region 0
         mfb_i_ptr := 0;
      end if;

      while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
         -- send new transaction

         -- find new tag to send
         random_val_index(response_vld,'1',seed1,seed2,tag);
         exit when (tag=-1); -- no response to send

         -- create transaction
         completed := '0';
         length    := 0;
         address   := response_remaining_addr(tag);

         if ((response_remaining_addr(tag) mod RCB_SIZE)/=0) then -- current address is not aligned to RCB_SIZE
            -- add obligatory first (unaligned) part of transaction
            length := (RCB_SIZE-to_integer(response_remaining_addr(tag) mod RCB_SIZE))/4;
         end if;

         -- add middle part of transaction (n-times RCB blocks)
         randint(seed1,seed2,DOWN_RESPONSE_PART_LEN_MIN,DOWN_RESPONSE_PART_LEN_MAX,rcbs);
         length := length+rcbs*RCB_SIZE/4;
         if (length>=response_remaining_len(tag)) then -- length exeeds (or is equal to) the complete length of the transaction
            -- complete the whole transaction
            length := response_remaining_len(tag);
            completed := '1';
            response_vld(tag) := '0';
         end if;

         response_remaining_len(tag)  := response_remaining_len(tag) -length;
         response_remaining_addr(tag) := response_remaining_addr(tag)+length*4;

         gap_length := 0;
         randint(seed1,seed2,0,99,X);
         if (X<DOWN_GAP_CHANCE) then
            randint(seed1,seed2,DOWN_GAP_LEN_MIN,DOWN_GAP_LEN_MAX,gap_length);
         end if;

         mvb_mfb_trans_new(trans,seed1,seed2,'1',address,length,(response_remaining_len(tag)+length)*4,gap_length,tag,0,completed,'1');
         new_trans_send(new_t_ptr)     := trans;
         new_trans_send_vld(new_t_ptr) := '1';
         new_t_ptr := new_t_ptr+1;

         -- send start of new transaction
         insert_trans_part_in_rc_word(trans,rc_i,rc_mvb_i,mfb_i_ptr,sop_ptr,eop_ptr,true);
         if (trans.data_rd_ptr<(trans.length+trans.after_gap_length)*32) then
            -- transaction not send whole
            unfinished := trans;
            unfinished_vld := '1';
            exit;
         end if;

         mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE); -- new transaction must start at the beginning of a region
      end loop;
   end procedure;
   ----

   -- MVB+MFB word accept; checks correct MVB+MFB comunication and accepts MVB+MFB transactions
   -- mvb_i, mfb_i                                  - MVB+MFB interface status
   -- mvb_i_ptr, mfb_i_ptr                          - current MVB and MFB item read pointers
   -- unfinished                                    - transaction continuing from previous word
   -- unfinished_expected_len                       - expected total length of unfinished transaction
   -- unfinished_vld                                - valid bit of unfinished transaction
   -- accepted(DMA_MFB_DOWN_REGIONS-1 downto 0)     - newly completely accepted transactions
   -- accepted_vld(DMA_MFB_DOWN_REGIONS-1 downto 0) - valid bits of newly accepted transactions
   procedure accept_mvb_mfb_word(mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector; seed1 : inout positive; seed2 : inout positive) is
      variable trans0 : mvb_mfb_trans_t;
      variable trans1 : mvb_mfb_trans_t;

      variable acc_ptr : integer;

      variable mfb_reg_ptr   : integer;
      variable mfb_block_ptr : integer;

      variable sof_ptr : integer;
      variable eof_ptr : integer;

      variable pos : integer;

      variable pcie_up_hdr  : std_logic_vector(PCIE_UPHDR_WIDTH-1 downto 0);
      variable pcie_payload : std_logic;
      variable pcie_length  : integer;

      variable dma_hdr   : std_logic_vector(DMA_DOWNHDR_WIDTH-1 downto 0);
      variable address   : unsigned(DMA_ADDR_WIDTH-1 downto 0) := (others => '0');
      variable length    : integer;
      variable tag       : integer;
      variable id        : integer;
      variable completed : std_logic;

      variable end_flag : boolean;

      variable l : line;
   begin
      accepted_vld := (accepted_vld'length-1 downto 0 => '0');
      acc_ptr := 0;

      mvb_i.dst_rdy := '0';
      mfb_i.dst_rdy := '0';

      if (mfb_i.src_rdy='1') then
         if (unfinished_vld='1') then
            -- read unfinished transaction

            -- find next eof
            eof_ptr := -1;
            while (mfb_i_ptr<DMA_MFB_DOWN_ITEMS) loop
               mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

               pos := to_integer(unsigned(mfb_i.eof_pos(MFB_DOWN_EOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_EOF_POS_WIDTH*mfb_reg_ptr)));
               if (mfb_i.eof(mfb_reg_ptr)='1') then
                  eof_ptr   := mfb_reg_ptr*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE+pos;
                  mfb_i_ptr := eof_ptr+1;
                  exit;
               end if;
               mfb_i_ptr := mfb_i_ptr+1;
            end loop;

            -- copy data
            mvb_mfb_trans_new(trans0,seed1,seed2,'1',unfinished.address,mfb_i_ptr*MFB_DOWN_ITEM_WIDTH/32,0,unfinished.tag,unfinished.id,unfinished.completed,'1');
            trans0.data(MFB_DOWN_ITEM_WIDTH*mfb_i_ptr-1 downto 0) := mfb_i.data(MFB_DOWN_ITEM_WIDTH*mfb_i_ptr-1 downto 0);
            mvb_mfb_trans_merge(unfinished,trans0,trans1);
            unfinished := trans1;

            if (eof_ptr/=-1) then
               -- finish the unfinished
               if (unfinished.length/=unfinished_expected_len) then
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("DOWN MVB+MFB incorrect length in multiple-word transaction!"));writeline(output,l);
                  write(l,string'("Unfinished transaction: "));writeline(output,l);
                  mvb_mfb_trans_print(unfinished);
                  write(l,string'("expected length: "));
                  write_dec(l,unfinished_expected_len);
                  writeline(output,l);
                  report "" severity failure;
               end if;

               accepted(acc_ptr)           := unfinished;
               accepted_vld(acc_ptr)       := '1';
               acc_ptr := acc_ptr+1;

               unfinished_vld := '0';
            end if;
         end if;

         if (mvb_i.src_rdy='1') then
            -- read new transactions
            while (mvb_i_ptr<MVB_DOWN_ITEMS) loop
               if (mvb_i.vld(mvb_i_ptr)='0') then
                  -- non-valid MVB item; pass
                  mvb_i_ptr := mvb_i_ptr+1;
                  next;
               end if;

               exit when (mfb_i_ptr=DMA_MFB_DOWN_ITEMS); -- end of MFB word

               -- find next sof
               sof_ptr := -1;
               while (mfb_i_ptr<DMA_MFB_DOWN_ITEMS) loop
                  mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

                  pos := to_integer(unsigned(mfb_i.sof_pos(MFB_DOWN_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*mfb_reg_ptr)));
                  if (mfb_i.sof(mfb_reg_ptr)='1') then
                     sof_ptr   := mfb_reg_ptr*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE+pos*MFB_DOWN_BLOCK_SIZE;
                     mfb_i_ptr := sof_ptr;
                     exit;
                  end if;
                  mfb_i_ptr := mfb_i_ptr+1;
               end loop;

               exit when (sof_ptr=-1); -- no new sof found

               -- find next eof
               eof_ptr := -1;
               while (mfb_i_ptr<DMA_MFB_DOWN_ITEMS) loop
                  mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

                  pos := to_integer(unsigned(mfb_i.eof_pos(MFB_DOWN_EOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_EOF_POS_WIDTH*mfb_reg_ptr)));
                  if (mfb_i.eof(mfb_reg_ptr)='1') then
                     eof_ptr   := mfb_reg_ptr*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE+pos;
                     mfb_i_ptr := eof_ptr+1;
                     exit;
                  end if;
                  mfb_i_ptr := mfb_i_ptr+1;
               end loop;

               -- get header info
               dma_hdr   := mvb_i.data(DMA_DOWNHDR_WIDTH*(mvb_i_ptr+1)-1 downto DMA_DOWNHDR_WIDTH*mvb_i_ptr);
               address   := (others => '0');
               length    := to_integer(unsigned(dma_hdr(DMA_COMPLETION_LENGTH)));
               tag       := to_integer(unsigned(dma_hdr(DMA_COMPLETION_TAG)));
               id        := to_integer(unsigned(dma_hdr(DMA_COMPLETION_UNITID)));
               completed :=                     dma_hdr(DMA_COMPLETION_COMPLETED'low);

               if (eof_ptr=-1) then
                  -- new unfinished transaction
                  if (unfinished_vld='1') then
                     write(l,now);write(l,string'(" : "));
                     write(l,string'("DOWN MVB+MFB new transaction before previous transaction's end!"));writeline(output,l);
                     write(l,string'("Unfinished transaction: "));writeline(output,l);
                     mvb_mfb_trans_print(unfinished);
                     report "" severity failure;
                  end if;
                  mvb_mfb_trans_new(unfinished,seed1,seed2,'1',address,(DMA_MFB_DOWN_ITEMS-sof_ptr)*MFB_DOWN_ITEM_WIDTH/32,0,tag,id,completed,'1');
                  unfinished.data(unfinished.length*32-1 downto 0) := mfb_i.data(DMA_MFB_DOWN_DATA_WIDTH-1 downto MFB_DOWN_ITEM_WIDTH*sof_ptr);
                  unfinished_expected_len := length;
                  unfinished_vld := '1';
               else
                  -- transaction started and ended in this word
                  mvb_mfb_trans_new(trans0,seed1,seed2,'1',address,(eof_ptr-sof_ptr+1)*MFB_DOWN_ITEM_WIDTH/32,0,tag,id,completed,'1');
                  trans0.data(trans0.length*32-1 downto 0) := mfb_i.data(MFB_DOWN_ITEM_WIDTH*(eof_ptr+1)-1 downto MFB_DOWN_ITEM_WIDTH*sof_ptr);

                  if (trans0.length/=length) then
                     write(l,now);write(l,string'(" : "));
                     write(l,string'("DOWN MVB+MFB incorrect length in single-word transaction!"));writeline(output,l);
                     write(l,string'("Transaction: "));writeline(output,l);
                     mvb_mfb_trans_print(trans0);
                     write(l,string'("expected length: "));
                     write_dec(l,length);
                     writeline(output,l);
                     report "" severity failure;
                  end if;

                  accepted(acc_ptr)           := trans0;
                  accepted_vld(acc_ptr)       := '1';
                  acc_ptr := acc_ptr+1;
               end if;

               mvb_i_ptr := mvb_i_ptr+1;
               mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
            end loop;

            -- find next sof (skip to end of MFB word if no sof found)
            while (mfb_i_ptr<DMA_MFB_DOWN_ITEMS) loop
               mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

               pos := to_integer(unsigned(mfb_i.sof_pos(MFB_DOWN_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*mfb_reg_ptr)));
               if (mfb_i.sof(mfb_reg_ptr)='1') then
                  mfb_i_ptr := mfb_reg_ptr*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE+pos*MFB_DOWN_BLOCK_SIZE;
                  exit;
               end if;
               mfb_i_ptr := mfb_i_ptr+1;
            end loop;

         end if;
      -- Only Error on UP way
      --elsif (unfinished_vld='1') then
      --   write(l,now);write(l,string'(" : "));
      --   write(l,string'("DOWN MFB src_rdy fall during transaction transmission!"));writeline(output,l);
      --   write(l,string'("Unfinished transaction: "));writeline(output,l);
      --   mvb_mfb_trans_print(unfinished);
      --   report "" severity failure;
      end if;

      -- set dst rdy to 1, if the whole MVB / MFB word was read
      if (mvb_i_ptr=MVB_DOWN_ITEMS) then
         mvb_i_ptr := 0;
         mvb_i.dst_rdy := '1';
      end if;

      if (mfb_i_ptr=DMA_MFB_DOWN_ITEMS) then
         mfb_i_ptr := 0;
         mfb_i.dst_rdy := '1';
      end if;
   end procedure;
   ----

end test_pkg;
