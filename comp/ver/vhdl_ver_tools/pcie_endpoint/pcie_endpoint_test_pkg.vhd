-- pcie_endpoint_test_pkg.vhd: Test Package
-- Copyright (C) 2017 CESNET
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
use std.env.stop;
use STD.textio.all;
use work.basics_test_pkg.all;
use work.mvb_mfb_test_pkg.all;

   -- ----------------------------------------------------------------------------
   --                        package declarations
   -- ----------------------------------------------------------------------------

package pcie_endpoint_test_pkg is

   constant DEVICE : string  := "ULTRASCALE"; -- "ULTRASCALE", "7SERIES"

   -------------------------------
   -- 7SERIES bus configuration
   -------------------------------
   --constant MVB_UP_ITEMS        : integer := 1;

   --constant MFB_UP_REGIONS      : integer := 1;
   --constant MFB_UP_REG_SIZE     : integer := 1;
   --constant MFB_UP_BLOCK_SIZE   : integer := 8;
   --constant MFB_UP_ITEM_WIDTH   : integer := 32;

   --constant MFB_UP_ITEMS        : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

   --constant MVB_DOWN_ITEMS      : integer := 2;

   --constant MFB_DOWN_REGIONS    : integer := 2;
   --constant MFB_DOWN_REG_SIZE   : integer := 1;
   --constant MFB_DOWN_BLOCK_SIZE : integer := 4;
   --constant MFB_DOWN_ITEM_WIDTH : integer := 32;

   --constant MFB_DOWN_ITEMS      : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;

   --constant RQ_TUSER_WIDTH      : integer := 60;
   --constant RC_TUSER_WIDTH      : integer := 75;

   -------------------------------

   -------------------------------
   -- ULTRASCALE bus configuration
   -------------------------------
   constant MVB_UP_ITEMS        : integer := 2;

   constant MFB_UP_REGIONS      : integer := 2;
   constant MFB_UP_REG_SIZE     : integer := 1;
   constant MFB_UP_BLOCK_SIZE   : integer := 8;
   constant MFB_UP_ITEM_WIDTH   : integer := 32;

   constant MFB_UP_ITEMS        : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

   constant MVB_DOWN_ITEMS      : integer := 4;

   constant MFB_DOWN_REGIONS    : integer := 4;
   constant MFB_DOWN_REG_SIZE   : integer := 1;
   constant MFB_DOWN_BLOCK_SIZE : integer := 4;
   constant MFB_DOWN_ITEM_WIDTH : integer := 32;

   constant MFB_DOWN_ITEMS      : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE;

   constant RQ_TUSER_WIDTH      : integer := 137;
   constant RC_TUSER_WIDTH      : integer := 161;

   -------------------------------

   constant PCIE_UPHDR_WIDTH    : integer := 128;
   constant PCIE_DOWNHDR_WIDTH  : integer := 3*4*8;

   constant PCIE_TAG_WIDTH      : integer := 8;

   constant RCB_SIZE            : integer := 64; -- 64 or 128 [B]

   constant DMA_ADDR_WIDTH      : integer := DMA_REQUEST_GLOBAL'high - DMA_REQUEST_GLOBAL'low + 1;
   constant DMA_LEN_WIDTH       : integer := DMA_REQUEST_LENGTH'high - DMA_REQUEST_LENGTH'low + 1;
   constant DMA_DATA_WIDTH      : integer := 2**DMA_LEN_WIDTH*32+1;

   constant MFB_UP_DATA_WIDTH   : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH;
   constant MFB_DOWN_DATA_WIDTH : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH;

   constant AXI_UP_SOP_POS_WIDTH : integer := log2(MFB_UP_REGIONS*MFB_UP_REG_SIZE)+1;
   constant AXI_UP_EOP_POS_WIDTH : integer := log2(MFB_UP_ITEMS);

   constant AXI_DOWN_SOP_POS_WIDTH : integer := log2(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE);
   constant AXI_DOWN_EOP_POS_WIDTH : integer := log2(MFB_DOWN_ITEMS);

   -- verification parameters
   -- DOWN AXI sending settings
   constant DOWN_RESPONSE_PART_LEN_MIN : integer := 1;             -- [RCB_SIZE]
   constant DOWN_RESPONSE_PART_LEN_MAX : integer := 1024/RCB_SIZE; -- [RCB_SIZE]
   constant DOWN_GAP_CHANCE            : integer := 80;   -- [%]
   constant DOWN_GAP_LEN_MIN           : integer := 1;    -- [dword]
   constant DOWN_GAP_LEN_MAX           : integer := 2**6; -- [dword]
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

   -- RQ tuser operations
   function rq_tuser_ser(tu : rq_tuser_t) return std_logic_vector;
   function rq_tuser_deser(tu : std_logic_vector) return rq_tuser_t;
   -- RC tuser operations
   function rc_tuser_ser(tu : rc_tuser_t) return std_logic_vector;
   function rc_tuser_deser(tu : std_logic_vector) return rc_tuser_t;

   -- RQ accepting
   procedure accept_rq_word(rq_i : inout rq_i_t; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer;
                            unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector;
                            free_tags : inout std_logic_vector; new_tags : out i_array_t; new_tags_vld : out std_logic_vector;
                            seed1 : inout integer; seed2 : inout integer);

   -- RC generation
   procedure insert_trans_part_in_rc_word(trans : inout mvb_mfb_trans_t; rc_i : inout rc_i_t; mfb_i_ptr : inout integer;
                                          sop_ptr : inout integer; eop_ptr : inout integer; send_header : boolean);
   procedure post_new_rc_word(rc_i : inout rc_i_t; response_remaining_addr : inout u_array_t; response_remaining_len : inout i_array_t; response_vld : inout std_logic_vector;
                              unfinished : inout mvb_mfb_trans_t; unfinished_vld : inout std_logic;
                              new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector; seed1 : inout integer; seed2 : inout integer);
   ----
end pcie_endpoint_test_pkg;

   -- ----------------------------------------------------------------------------
   --                            package body
   -- ----------------------------------------------------------------------------

package body pcie_endpoint_test_pkg is

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

   -- RQ word accept; checks AXI comunination signals validity and accepts data from rq_tdata (accepted contains new completed transactions; new_tag contains pcie tags assigned to accepted read transactions)
   procedure accept_rq_word(rq_i : inout rq_i_t; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector; free_tags : inout std_logic_vector; new_tags : out i_array_t; new_tags_vld : out std_logic_vector; seed1 : inout integer; seed2 : inout integer) is
      variable mfb_i_ptr     : integer;

      variable sop_ptr      : integer;
      variable eop_ptr      : integer;
      variable new_tag_ptr  : integer;

      variable trans0 : mvb_mfb_trans_t;
      variable trans1 : mvb_mfb_trans_t;

      variable pcie_up_hdr  : std_logic_vector(PCIE_UPHDR_WIDTH-1 downto 0);
      variable pcie_payload : std_logic;
      variable pcie_address : unsigned(DMA_ADDR_WIDTH-1 downto 0);
      variable pcie_length  : integer;

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
            trans0 := mvb_mfb_trans_new('1',to_unsigned(0,DMA_ADDR_WIDTH),0,0,unfinished.tag,unfinished.id,'0','0');

            -- continuing transaction
            if (rq_i.tuser.eop(0)='0') then
               -- no end of packet in this word
               trans0 := mvb_mfb_trans_new('1',unfinished.address,MFB_UP_DATA_WIDTH/32,0,unfinished.tag,unfinished.id,'0','0');
               trans0.data(MFB_UP_DATA_WIDTH-1 downto 0) := rq_i.tdata;

               mvb_mfb_trans_merge(unfinished,trans0,trans1);
               unfinished := trans1;
            else
               -- finish the unfinished
               trans0 := mvb_mfb_trans_new('1',unfinished.address,(rq_i.tuser.eop_pos(0)+1)*MFB_UP_ITEM_WIDTH/32,0,unfinished.tag,unfinished.id,'0','0');
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

            mfb_i_ptr    := rq_i.tuser.sop_pos(sop_ptr)/2*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE;

            pcie_up_hdr  := rq_i.tdata(mfb_i_ptr*MFB_UP_ITEM_WIDTH+PCIE_UPHDR_WIDTH-1 downto mfb_i_ptr*MFB_UP_ITEM_WIDTH);

            pcie_payload := pcie_up_hdr(DMA_ADDR_WIDTH+DMA_LEN_WIDTH);
            pcie_address := unsigned(pcie_up_hdr(DMA_ADDR_WIDTH-1 downto 0));
            pcie_length  := to_integer(unsigned(pcie_up_hdr(DMA_LEN_WIDTH+DMA_ADDR_WIDTH-1 downto DMA_ADDR_WIDTH)));

            mfb_i_ptr    := mfb_i_ptr+PCIE_UPHDR_WIDTH/MFB_UP_ITEM_WIDTH;

            if (rq_i.tuser.eop(eop_ptr)='1') then
               -- transaction starts and ends in this word
               if (pcie_payload='1') then
                  -- new write transaction; check correct eop_pos
                  trans0 := mvb_mfb_trans_new(pcie_payload,pcie_address,((rq_i.tuser.eop_pos(eop_ptr)+1)*32-mfb_i_ptr*MFB_UP_ITEM_WIDTH)/32,0,0,0,'0','0');
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
                  -- new read transaction accepted; assign a new tag

                  random_val_index(free_tags,'1',seed1,seed2,X);

                  if (X=-1) then
                     report "No more free PCIe tags to assign!" severity failure; -- avoid this situation when setting rq_i.tready
                  end if;

                  new_tags(new_tag_ptr)     := X;
                  new_tags_vld(new_tag_ptr) := '1';
                  free_tags(X)              := '0';
                  new_tag_ptr := new_tag_ptr+1;

                  trans0 := mvb_mfb_trans_new(pcie_payload,pcie_address,pcie_length,0,X,0,'0','0'); -- set transacasction's tag to assigned PCIe tag (needed for response generation)
               end if;

               accepted(eop_ptr)     := trans0;
               accepted_vld(eop_ptr) := '1';

               mfb_i_ptr := (rq_i.tuser.eop_pos(eop_ptr)+1)*32/MFB_UP_ITEM_WIDTH;
               eop_ptr   := eop_ptr+1;
            else
               -- transaction continues to next word
               trans0 := mvb_mfb_trans_new(pcie_payload,pcie_address,(MFB_UP_DATA_WIDTH-mfb_i_ptr*MFB_UP_ITEM_WIDTH)/32,0,0,0,'0','0');
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
   procedure insert_trans_part_in_rc_word(trans : inout mvb_mfb_trans_t; rc_i : inout rc_i_t; mfb_i_ptr : inout integer; sop_ptr : inout integer; eop_ptr : inout integer; send_header : boolean) is
   begin
      if (send_header) then
         -- insert PCIe header
         rc_i.tvalid := '1';
         rc_i.tuser.sop(sop_ptr)     := '1';
         rc_i.tuser.sop_pos(sop_ptr) := get_block_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
         sop_ptr := sop_ptr+1;

         rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+32+DMA_LEN_WIDTH-1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+32)  := std_logic_vector(to_unsigned(trans.length,DMA_LEN_WIDTH));
         rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+64+PCIE_TAG_WIDTH-1 downto mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+64) := std_logic_vector(to_unsigned(trans.tag,PCIE_TAG_WIDTH));
         rc_i.tdata(mfb_i_ptr*MFB_DOWN_ITEM_WIDTH+30)                                                          := '1' when trans.completed else '0';

         mfb_i_ptr := mfb_i_ptr+PCIE_DOWNHDR_WIDTH/MFB_DOWN_ITEM_WIDTH;
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
   -- response_remaining_addr(PCIE_TAG_WIDTH-1 downto 0) - address of awaiting responses
   --                        (DMA_ADDR_WIDTH-1 downto 0) -
   -- response_remaining_len(PCIE_TAG_WIDTH-1 downto 0)  - remaining length to send of each awaiting response
   -- response_vld(PCIE_TAG_WIDTH-1 downto 0)            - valid bit for each awaiting response
   -- unfinished                                         - transaction, whose part was send in previous word
   -- unfinished_vld                                     - valid bit for worked transaction
   -- new_trans_send(MVB_DOWN_ITEMS-1 downto 0)          - newly posted transaction
   -- new_trans_send_vld(MVB_DOWN_ITEMS-1 downto 0)      - valid bit for each newly send posted transaction
   -- seed1, seed2                                       - random seed
   procedure post_new_rc_word(rc_i : inout rc_i_t; response_remaining_addr : inout u_array_t; response_remaining_len : inout i_array_t; response_vld : inout std_logic_vector; unfinished : inout mvb_mfb_trans_t; unfinished_vld : inout std_logic; new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector; seed1 : inout integer; seed2 : inout integer) is
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
      if (rc_i.tready='0') then
         -- do nothing
         return;
      end if;

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
      new_trans_send_vld := (MVB_DOWN_ITEMS-1 downto 0 => '0');

      if (unfinished_vld='1') then
         -- send next part of continuing transaction
         insert_trans_part_in_rc_word(unfinished,rc_i,mfb_i_ptr,sop_ptr,eop_ptr,false);
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

         -- resolve length based on read completion boundary
         if ((response_remaining_addr(tag) mod RCB_SIZE)=0) then -- current address is aligned to RCB_SIZE
            randint(seed1,seed2,DOWN_RESPONSE_PART_LEN_MIN,DOWN_RESPONSE_PART_LEN_MAX,rcbs);
            length := rcbs*RCB_SIZE/4;
            if (length>response_remaining_len(tag)) then
               length := response_remaining_len(tag) - (response_remaining_len(tag) mod (RCB_SIZE/4));
            end if;

            if (length=response_remaining_len(tag)) then -- end of transaction is aligned to RCBS
               completed := '1';
               response_vld(tag) := '0';
            elsif (length=0) then -- last part is smaller than RCB_SIZE
               length    := response_remaining_len(tag);
               completed := '1';
               response_vld(tag) := '0';
            end if;
         else -- current address is not aligned to RCB_SIZE
            length := (RCB_SIZE-to_integer(response_remaining_addr(tag) mod RCB_SIZE))/4;
            if (length>response_remaining_len(tag)) then -- transaction's part is inside one RCB_SIZE
               length := response_remaining_len(tag);
               completed := '1';
               response_vld(tag) := '0';
            end if;
         end if;
         response_remaining_len(tag)  := response_remaining_len(tag) -length;
         response_remaining_addr(tag) := response_remaining_addr(tag)+length*4;

         gap_length := 0;
         randint(seed1,seed2,0,99,X);
         if (X<DOWN_GAP_CHANCE) then
            randint(seed1,seed2,DOWN_GAP_LEN_MIN,DOWN_GAP_LEN_MAX,gap_length);
         end if;

         trans   := mvb_mfb_trans_new('1',address,length,gap_length,tag,0,completed,'1');
         new_trans_send(new_t_ptr)     := trans;
         new_trans_send_vld(new_t_ptr) := '1';
         new_t_ptr := new_t_ptr+1;

         -- send start of new transaction
         insert_trans_part_in_rc_word(trans,rc_i,mfb_i_ptr,sop_ptr,eop_ptr,true);
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

end pcie_endpoint_test_pkg;

