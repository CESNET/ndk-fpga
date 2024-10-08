-- mvb_mfb_test_pkg.vhd: Test Package
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

   -- ----------------------------------------------------------------------------
   --                        package declarations
   -- ----------------------------------------------------------------------------

package mvb_mfb_test_pkg is

   -------------------------------
   -- MVB+MFB bus configuration
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

   -------------------------------

   constant DMA_TAG_WIDTH       : integer := DMA_REQUEST_TAG'high - DMA_REQUEST_TAG'low + 1;
   constant DMA_ID_WIDTH        : integer := DMA_REQUEST_UNITID'high - DMA_REQUEST_UNITID'low + 1;

   constant RCB_SIZE            : integer := 64; -- 64 or 128 [B]

   constant DMA_ADDR_WIDTH      : integer := DMA_REQUEST_GLOBAL'high - DMA_REQUEST_GLOBAL'low + 1;
   constant DMA_LEN_WIDTH       : integer := DMA_REQUEST_LENGTH'high - DMA_REQUEST_LENGTH'low + 1;
   constant DMA_DATA_WIDTH      : integer := 2**DMA_LEN_WIDTH*32+1;

   constant MFB_UP_DATA_WIDTH   : integer := MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH;
   constant MFB_DOWN_DATA_WIDTH : integer := MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH;

   constant MFB_UP_SOF_POS_WIDTH   : integer := max(1,log2(MFB_UP_REG_SIZE));                        -- address of block of region's SOF
   constant MFB_UP_EOF_POS_WIDTH   : integer := max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE));      -- address of item of region's EOF

   constant MFB_DOWN_SOF_POS_WIDTH : integer := max(1,log2(MFB_DOWN_REG_SIZE));                      -- address of block of region's SOF
   constant MFB_DOWN_EOF_POS_WIDTH : integer := max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE));  -- address of item of region's EOF

   -- verification inner parameters
   constant DEFAULT_DATA_VALUE  : integer := 42;

   -- UP MVB+MFB generator settings
   constant UP_READ_START_ALIGN_CHANCE : integer := 50; -- [%] - chance, that a read transaction's start addr is aligned to RCB_SIZE
   constant UP_READ_END_ALIGN_CHANCE   : integer := 50; -- [%] - chance, that a read transaction's end   addr is aligned to RCB_SIZE
   ----

   -- MVB+MFB packet
   type mvb_mfb_trans_t is record
      payload          : std_logic; -- is write transaction
      address          : unsigned(DMA_ADDR_WIDTH-1 downto 0); -- target address of write / read request [Byte]
      length           : integer; -- total length of write / read request [DWORD]
      after_gap_length : integer; -- length of empty space after transaction payload [DWORD]
      data             : std_logic_vector(DMA_DATA_WIDTH-1 downto 0); -- payload data
      data_rd_ptr      : integer; -- current read pointer for payload data
      tag              : integer; -- transaction tag (PCIe/DMA)
      id               : integer; -- transaction unitid (DMA)
      completed        : std_logic; -- last part of read response
      is_down          : std_logic; -- is completion transaction
   end record;

   constant MVB_MFB_TRANS_WIDTH : integer := 1+DMA_ADDR_WIDTH+32+32+DMA_DATA_WIDTH+32+32+32+1+1;

   type mvb_mfb_trans_array_t is array (natural range <>) of mvb_mfb_trans_t;
   ----

   -- MVB interface
   type mvb_i_t is record
      data    : std_logic_vector;
      vld     : std_logic_vector;
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;
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
   ----

   -- function and procedure declarations

   -- MVB+MFB transactions operations
   function mvb_mfb_trans_ser(t : mvb_mfb_trans_t) return std_logic_vector;
   function mvb_mfb_trans_deser(t : std_logic_vector) return mvb_mfb_trans_t;
   function mvb_mfb_trans_new(payload : std_logic; address : unsigned; length : integer; after_gap_length : integer; tag : integer; id : integer; completed : std_logic; is_down : std_logic) return mvb_mfb_trans_t;
   procedure mvb_mfb_trans_new_rand(trans : out mvb_mfb_trans_t; seed1 : inout integer; seed2 : inout integer; free_idtag_map : inout std_logic_vector;
                                   min_length : integer; max_length : integer; read : std_logic; after_gap_chance : integer;
                                   ag_min : integer; ag_max : integer; is_down : std_logic);
   procedure mvb_mfb_trans_merge(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t; ret_val : out mvb_mfb_trans_t);
   procedure mvb_mfb_trans_split(t : mvb_mfb_trans_t; t0_length : integer; t0_after_gap_length : integer; ret_val : out mvb_mfb_trans_array_t);
   function mvb_mfb_trans_cmp(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t) return boolean;
   procedure mvb_mfb_trans_print(t : mvb_mfb_trans_t);
   procedure mvb_mfb_trans_fifo_print(fifo : slv_fifo_t);

   -- MFB ptr work
   function get_block_ptr(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;
   function get_reg_ptr(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;
   function shift_to_next_reg(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;
   function shift_to_next_block(mfb_i_ptr : integer; MFB_REG_SIZE : integer; MFB_BLOCK_SIZE : integer) return integer;

   -- UP MB+MFB generation
   procedure insert_trans_part_in_up_mvb_mfb_word(trans : inout mvb_mfb_trans_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer);
   procedure post_new_up_mvb_mfb_word(fifo : inout slv_fifo_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t;
                                      new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector);

   -- UP MVB+MFB accepting
   procedure accept_up_mvb_mfb_word(mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer;
                                    unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic;
                                    accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector);

   -- DOWN MB+MFB generation
   procedure insert_trans_part_in_down_mvb_mfb_word(trans : inout mvb_mfb_trans_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer);
   procedure post_new_down_mvb_mfb_word(fifo : inout slv_fifo_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t;
                                        new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector);

   -- DOWN MVB+MFB accepting
   procedure accept_down_mvb_mfb_word(mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer;
                                      unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic;
                                      accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector);
   ----
end mvb_mfb_test_pkg;

   -- ----------------------------------------------------------------------------
   --                            package body
   -- ----------------------------------------------------------------------------

package body mvb_mfb_test_pkg is

   -- mvb mfb serialization
   function mvb_mfb_trans_ser(t : mvb_mfb_trans_t) return std_logic_vector is
      variable l1  : integer := 1;
      variable l2  : integer := l1+DMA_ADDR_WIDTH;
      variable l3  : integer := l2+32;
      variable l4  : integer := l3+32;
      variable l5  : integer := l4+DMA_DATA_WIDTH;
      variable l6  : integer := l5+32;
      variable l7  : integer := l6+32;
      variable l8  : integer := l7+32;
      variable l9  : integer := l8+1;
      variable l10 : integer := l9+1;
      variable vec : std_logic_vector(l10-1 downto 0);
   begin
      vec := t.is_down
           & t.completed
           & std_logic_vector(to_unsigned(t.id,32))
           & std_logic_vector(to_unsigned(t.tag,32))
           & std_logic_vector(to_unsigned(t.data_rd_ptr,32))
           & t.data
           & std_logic_vector(to_unsigned(t.after_gap_length,32))
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
      variable l5  : integer := l4+DMA_DATA_WIDTH;
      variable l6  : integer := l5+32;
      variable l7  : integer := l6+32;
      variable l8  : integer := l7+32;
      variable l9  : integer := l8+1;
      variable l10 : integer := l9+1;
      variable trans : mvb_mfb_trans_t;
   begin
      trans.payload          :=                     t(l1 -1);
      trans.address          :=            unsigned(t(l2 -1 downto l1));
      trans.length           := to_integer(unsigned(t(l3 -1 downto l2)));
      trans.after_gap_length := to_integer(unsigned(t(l4 -1 downto l3)));
      trans.data             :=                     t(l5 -1 downto l4);
      trans.data_rd_ptr      := to_integer(unsigned(t(l6 -1 downto l5)));
      trans.tag              := to_integer(unsigned(t(l7 -1 downto l6)));
      trans.id               := to_integer(unsigned(t(l8 -1 downto l7)));
      trans.completed        :=                     t(l9 -1);
      trans.is_down          :=                     t(l10-1);
      return trans;
   end function;
   ----

   -- mvb+mfb transactions creation
   function mvb_mfb_trans_new(payload : std_logic; address : unsigned; length : integer; after_gap_length : integer; tag : integer; id : integer; completed : std_logic; is_down : std_logic) return mvb_mfb_trans_t is
      variable trans : mvb_mfb_trans_t;
   begin
      trans.payload             := payload;
      trans.address             := address;
      trans.length              := length;
      trans.after_gap_length    := after_gap_length;
      trans.data                := random_vector(DMA_DATA_WIDTH,length+after_gap_length+tag+id+1);
      trans.data_rd_ptr         := 0;
      trans.tag                 := tag;
      trans.id                  := id;
      trans.completed           := completed;
      trans.is_down             := is_down;
      return trans;
   end function;
   ----

   -- mvb+mfb random transaction creation
   procedure mvb_mfb_trans_new_rand(trans : out mvb_mfb_trans_t; seed1 : inout integer; seed2 : inout integer; free_idtag_map : inout std_logic_vector; min_length : integer; max_length : integer; read : std_logic; after_gap_chance : integer; ag_min : integer; ag_max : integer; is_down : std_logic) is
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
      trans.id  := X/(2**DMA_TAG_WIDTH);
      trans.tag := X mod (2**DMA_TAG_WIDTH);
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
         write(l,string'(" | Address: 0x"));write_hex(l,std_logic_vector(t.address));
      else
         write(l,string'("| Completed: "));write_dec(l,std_logic_vector'(0 => t.completed));
      end if;
      write(l,string'(" | Length: " & integer'image(t.length)));
      write(l,string'(" | Tag: " & integer'image(t.tag)));
      write(l,string'(" | ID: " & integer'image(t.id)));
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
      trans.data(trans.length*32-1 downto t0.length*32) := t1.data(t1.length*32-1 downto 0);
      trans.after_gap_length := t1.after_gap_length;
      trans.completed := t0.completed or t1.completed;
      ret_val := trans;
   end procedure;
   ----

   -- mvb+mfb transaction split to two transactions
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
      s_t(1).data(s_t(1).length-1 downto 0) := t.data(t.length-1 downto t0_length);

      if (t.data_rd_ptr>=t0_length) then
         s_t(0).data_rd_ptr := 0;
         s_t(1).data_rd_ptr := t.data_rd_ptr-t0_length;
      else
         s_t(1).data_rd_ptr := 0;
      end if;

      s_t(0).length := t0_length;
      s_t(0).after_gap_length := t0_after_gap_length;

      s_t(0).completed := '0';

      ret_val := s_t;
   end procedure;
   ----

   -- mvb+mfb transactions are equal
   function mvb_mfb_trans_cmp(t0 : mvb_mfb_trans_t; t1 : mvb_mfb_trans_t) return boolean is
   begin
      if (t0.payload/=t1.payload or t0.length/=t1.length or t0.address/=t1.address) then
         return false;
      elsif (t0.payload='1' and t0.data(t0.length*32-1 downto 0)/=t1.data(t0.length*32-1 downto 0)) then
         return false;
      else
         return true;
      end if;
   end function;
   ----

   -- MFB word pointer operations
   function count_val(vec : std_logic_vector; val : std_logic) return integer is
      variable ret : integer := 0;
   begin
      for i in vec'low to vec'high loop
         if (vec(i)=val) then
            ret := ret+1;
         end if;
      end loop;

      return ret;
   end function;
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

   -- insert part of UP MVB+MFB transaction in MVB and MFB word
   procedure insert_trans_part_in_up_mvb_mfb_word(trans : inout mvb_mfb_trans_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer) is
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

            while (mfb_i_ptr<MFB_UP_ITEMS and trans.data_rd_ptr<trans.length*32) loop
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

            while (mfb_i_ptr<MFB_UP_ITEMS and trans.data_rd_ptr<(trans.length+trans.after_gap_length)*32) loop
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

   -- post new UP MVB+MFB word from MVB+MFB FIFO (adds all newly started transactions to new_trans_send (their valids are in new_trans_send_vld))
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
      if ((mvb_i.dst_rdy='1' or mfb_i.dst_rdy='1') and fifo.empty='1') then
         mvb_i.src_rdy := '0';
         mfb_i.src_rdy := '0';
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
         mfb_i.sof     := (MFB_UP_REGIONS-1 downto 0 => '0');
         mfb_i.eof     := (MFB_UP_REGIONS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         if (trans.payload='1' and trans.data_rd_ptr>0) then
            insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
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
            insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);

            slv_fifo_pop(fifo,dummy);

            exit when (fifo.empty='1');

            trans := mvb_mfb_trans_deser(fifo.fifo(0));
         end loop;
      elsif (mvb_i.dst_rdy='1' and mfb_i.dst_rdy='1') then ---------
         -- send anything
         mfb_i.src_rdy := '0';
         mfb_i.sof     := (MFB_UP_REGIONS-1 downto 0 => '0');
         mfb_i.eof     := (MFB_UP_REGIONS-1 downto 0 => '0');
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
               insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
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

                  exit when (mfb_i_ptr=MFB_UP_ITEMS); -- shifted out of this MFB word

                  mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);
                  if (mfb_i.sof(mfb_reg_ptr)='1') then
                     mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE); -- two packet must not start in the same region
                  end if;

                  exit when (mfb_i_ptr=MFB_UP_ITEMS); -- shifted out of this MFB word

                  new_trans_send(mvb_i_ptr)     := trans;
                  new_trans_send_vld(mvb_i_ptr) := '1';

                  insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
                  fifo.fifo(0) := mvb_mfb_trans_ser(trans);

                  if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- end of transaction
                     slv_fifo_pop(fifo,dummy);

                     exit when (fifo.empty='1');

                     trans := mvb_mfb_trans_deser(fifo.fifo(0));
                  end if;

                  exit when (mfb_i_ptr=MFB_UP_ITEMS); -- filled the whole MFB word
                  exit when (mvb_i_ptr=MVB_UP_ITEMS); -- filled the whole MVB word
               else
                  -- continue
                  insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
                  fifo.fifo(0) := mvb_mfb_trans_ser(trans);

                  if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- end of transaction
                     slv_fifo_pop(fifo,dummy);

                     exit when (fifo.empty='1');

                     trans := mvb_mfb_trans_deser(fifo.fifo(0));
                  end if;

                  exit when (mfb_i_ptr=MFB_UP_ITEMS); -- filled the whole MFB word
                  exit when (mvb_i_ptr=MVB_UP_ITEMS); -- filled the whole MVB word
               end if;
            end if;
         end loop;
      end if;
   end procedure;
   ----

   -- UP MVB+MFB word accept; checks correct MVB+MFB comunication and accepts MVB+MFB transactions
   -- mvb_i, mfb_i                                  - MVB+MFB interface status
   -- mvb_i_ptr, mfb_i_ptr                          - current MVB and MFB item read pointers
   -- unfinished                                    - transaction continuing from previous word
   -- unfinished_expected_len                       - expected total length of unfinished transaction
   -- unfinished_vld                                - valid bit of unfinished transaction
   -- accepted(MVB_UP_ITEMS-1 downto 0)             - newly completely accepted transactions
   -- accepted_vld(MVB_UP_ITEMS-1 downto 0)         - valid bits of newly accepted transactions
   procedure accept_up_mvb_mfb_word(mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector) is
      variable trans0 : mvb_mfb_trans_t;
      variable trans1 : mvb_mfb_trans_t;

      variable acc_ptr : integer;

      variable mfb_reg_ptr   : integer;
      variable mfb_block_ptr : integer;

      variable sof_ptr : integer;
      variable eof_ptr : integer;

      variable pos : integer;

      variable dma_hdr   : std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);
      variable address   : unsigned(DMA_ADDR_WIDTH-1 downto 0) := (others => '0');
      variable length    : integer;
      variable tag       : integer;
      variable id        : integer;
      variable payload   : std_logic;

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
            while (mfb_i_ptr<MFB_UP_ITEMS) loop
               mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);

               pos := to_integer(unsigned(mfb_i.eof_pos(MFB_UP_EOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_UP_EOF_POS_WIDTH*mfb_reg_ptr)));
               if (mfb_i.eof(mfb_reg_ptr)='1') then
                  eof_ptr   := mfb_reg_ptr*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE+pos;
                  mfb_i_ptr := eof_ptr+1;
                  exit;
               end if;
               mfb_i_ptr := mfb_i_ptr+1;
            end loop;

            -- copy data
            trans0 := mvb_mfb_trans_new(unfinished.payload,unfinished.address,mfb_i_ptr*MFB_UP_ITEM_WIDTH/32,0,unfinished.tag,unfinished.id,'1','0');
            trans0.data(MFB_UP_ITEM_WIDTH*mfb_i_ptr-1 downto 0) := mfb_i.data(MFB_UP_ITEM_WIDTH*mfb_i_ptr-1 downto 0);
            mvb_mfb_trans_merge(unfinished,trans0,trans1);
            unfinished := trans1;

            if (eof_ptr/=-1) then
               -- finish the unfinished
               if (unfinished.length/=unfinished_expected_len) then
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("UP MVB+MFB incorrect length in multiple-word transaction!"));writeline(output,l);
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
      elsif (unfinished_vld='1') then
         write(l,now);write(l,string'(" : "));
         write(l,string'("DOWN MFB src_rdy fall during transaction transmission!"));writeline(output,l);
         write(l,string'("Unfinished transaction: "));writeline(output,l);
         mvb_mfb_trans_print(unfinished);
         report "" severity failure;
      end if;

      if (mvb_i.src_rdy='1') then
         -- read new transactions
         while (mvb_i_ptr<MVB_UP_ITEMS) loop
            if (mvb_i.vld(mvb_i_ptr)='0') then
               -- non-valid MVB item; pass
               mvb_i_ptr := mvb_i_ptr+1;
               next;
            end if;

            exit when (mfb_i_ptr=MFB_UP_ITEMS); -- end of MFB word

            -- get header info
            dma_hdr   := mvb_i.data(DMA_UPHDR_WIDTH*(mvb_i_ptr+1)-1 downto DMA_UPHDR_WIDTH*mvb_i_ptr);
            address   :=            unsigned(dma_hdr(DMA_REQUEST_GLOBAL));
            length    := to_integer(unsigned(dma_hdr(DMA_REQUEST_LENGTH)));
            tag       := to_integer(unsigned(dma_hdr(DMA_REQUEST_TAG)));
            id        := to_integer(unsigned(dma_hdr(DMA_REQUEST_UNITID)));
            payload   := '1' when dma_hdr(DMA_REQUEST_TYPE)=DMA_TYPE_WRITE else '0';

            if (payload='0') then
               -- new read transaction
               trans0 := mvb_mfb_trans_new(payload,address,length,0,tag,id,'1','0');

               accepted(acc_ptr)     := trans0;
               accepted_vld(acc_ptr) := '1';
               acc_ptr := acc_ptr+1;

               mvb_i_ptr := mvb_i_ptr+1;
               next;
            end if;

            exit when (mfb_i.src_rdy='0');

            -- find next sof
            sof_ptr := -1;
            while (mfb_i_ptr<MFB_UP_ITEMS) loop
               mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);

               pos := to_integer(unsigned(mfb_i.sof_pos(MFB_UP_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_UP_SOF_POS_WIDTH*mfb_reg_ptr)));
               if (mfb_i.sof(mfb_reg_ptr)='1') then
                  sof_ptr   := mfb_reg_ptr*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE+pos*MFB_UP_BLOCK_SIZE;
                  mfb_i_ptr := sof_ptr;
                  exit;
               end if;
               mfb_i_ptr := mfb_i_ptr+1;
            end loop;

            exit when (sof_ptr=-1); -- no new sof found

            -- find next eof
            eof_ptr := -1;
            while (mfb_i_ptr<MFB_UP_ITEMS) loop
               mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);

               pos := to_integer(unsigned(mfb_i.eof_pos(MFB_UP_EOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_UP_EOF_POS_WIDTH*mfb_reg_ptr)));
               if (mfb_i.eof(mfb_reg_ptr)='1') then
                  eof_ptr   := mfb_reg_ptr*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE+pos;
                  mfb_i_ptr := eof_ptr+1;
                  exit;
               end if;
               mfb_i_ptr := mfb_i_ptr+1;
            end loop;

            if (eof_ptr=-1) then
               -- new unfinished transaction
               if (unfinished_vld='1') then
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("UP MVB+MFB new transaction before previous transaction's end!"));writeline(output,l);
                  write(l,string'("Unfinished transaction: "));writeline(output,l);
                  mvb_mfb_trans_print(unfinished);
                  report "" severity failure;
               end if;
               unfinished := mvb_mfb_trans_new(payload,address,(MFB_UP_ITEMS-sof_ptr)*MFB_UP_ITEM_WIDTH/32,0,tag,id,'1','0');
               unfinished.data(unfinished.length*32-1 downto 0) := mfb_i.data(MFB_UP_DATA_WIDTH-1 downto MFB_UP_ITEM_WIDTH*sof_ptr);
               unfinished_expected_len := length;
               unfinished_vld := '1';
            else
               -- transaction started and ended in this word
               trans0 := mvb_mfb_trans_new(payload,address,(eof_ptr-sof_ptr+1)*MFB_UP_ITEM_WIDTH/32,0,tag,id,'1','0');
               trans0.data(trans0.length*32-1 downto 0) := mfb_i.data(MFB_UP_ITEM_WIDTH*(eof_ptr+1)-1 downto MFB_UP_ITEM_WIDTH*sof_ptr);

               if (trans0.length/=length) then
                  write(l,now);write(l,string'(" : "));
                  write(l,string'("UP MVB+MFB incorrect length in single-word transaction!"));writeline(output,l);
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
            mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);
         end loop;

         -- find next sof (skip to end of MFB word if no sof found)
         while (mfb_i_ptr<MFB_UP_ITEMS) loop
            mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_UP_REG_SIZE,MFB_UP_BLOCK_SIZE);

            pos := to_integer(unsigned(mfb_i.sof_pos(MFB_UP_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_UP_SOF_POS_WIDTH*mfb_reg_ptr)));
            if (mfb_i.sof(mfb_reg_ptr)='1') then
               mfb_i_ptr := mfb_reg_ptr*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE+pos*MFB_UP_BLOCK_SIZE;
               exit;
            end if;
            mfb_i_ptr := mfb_i_ptr+1;
         end loop;

      end if;

      -- set dst rdy to 1, if the whole MVB / MFB word was read
      if (mvb_i_ptr=MVB_UP_ITEMS) then
         mvb_i_ptr := 0;
         mvb_i.dst_rdy := '1';
      end if;

      if (mfb_i_ptr=MFB_UP_ITEMS) then
         mfb_i_ptr := 0;
         mfb_i.dst_rdy := '1';
      end if;
   end procedure;
   ----

   -- insert part of DOWN MVB+MFB transaction in MVB and MFB word
   procedure insert_trans_part_in_down_mvb_mfb_word(trans : inout mvb_mfb_trans_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer) is
      variable mvb_item : std_logic_vector(DMA_DOWNHDR_WIDTH-1 downto 0);

      variable mfb_block_ptr : integer;
      variable mfb_reg_ptr   : integer;

      variable l : line;
   begin
      if (trans.data_rd_ptr=0) then -- start of transaction
         -- insert MVB item
         mvb_i.src_rdy := '1';

         mvb_i.vld(mvb_i_ptr) := '1';

         repeated_fill(mvb_item,DEFAULT_DATA_VALUE);

         mvb_item(DMA_COMPLETION_LENGTH)        := std_logic_vector(to_unsigned(trans.length,DMA_LEN_WIDTH));
         mvb_item(DMA_COMPLETION_COMPLETED'low) := trans.completed;
         mvb_item(DMA_COMPLETION_TAG)           := std_logic_vector(to_unsigned(trans.tag,DMA_TAG_WIDTH));
         mvb_item(DMA_COMPLETION_UNITID)        := std_logic_vector(to_unsigned(trans.id,DMA_ID_WIDTH));

         mvb_i.data(DMA_DOWNHDR_WIDTH*(mvb_i_ptr+1)-1 downto DMA_DOWNHDR_WIDTH*mvb_i_ptr) := mvb_item;

         mvb_i_ptr := mvb_i_ptr+1;
      end if;

      if (trans.payload='1') then -- transaction with payload
         if (trans.data_rd_ptr<trans.length*32) then
            if (trans.data_rd_ptr=0) then -- start of transaction
               mfb_block_ptr := get_block_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
               mfb_reg_ptr   := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

               mfb_i.sof(mfb_reg_ptr) := '1';
               mfb_i.sof_pos(MFB_DOWN_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*mfb_reg_ptr) := std_logic_vector(to_unsigned((mfb_i_ptr mod MFB_DOWN_REG_SIZE),MFB_DOWN_SOF_POS_WIDTH));
            end if;

            -- send data
            mfb_i.src_rdy := '1';

            while (mfb_i_ptr<MFB_DOWN_ITEMS and trans.data_rd_ptr<trans.length*32) loop
               mfb_i.data(MFB_DOWN_ITEM_WIDTH*(mfb_i_ptr+1)-1 downto MFB_DOWN_ITEM_WIDTH*mfb_i_ptr) := trans.data(trans.data_rd_ptr+MFB_DOWN_ITEM_WIDTH-1 downto trans.data_rd_ptr);
               trans.data_rd_ptr := trans.data_rd_ptr + MFB_DOWN_ITEM_WIDTH;

               if (trans.data_rd_ptr=trans.length*32) then -- end of transaction data
                  mfb_block_ptr := get_block_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
                  mfb_reg_ptr   := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

                  mfb_i.eof(mfb_reg_ptr) := '1';
                  mfb_i.eof_pos(MFB_DOWN_EOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_EOF_POS_WIDTH*mfb_reg_ptr) := std_logic_vector(to_unsigned((mfb_i_ptr mod (MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE)),MFB_DOWN_EOF_POS_WIDTH));
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

            while (mfb_i_ptr<MFB_DOWN_ITEMS and trans.data_rd_ptr<(trans.length+trans.after_gap_length)*32) loop
               repeated_fill(mfb_i.data(MFB_DOWN_ITEM_WIDTH*(mfb_i_ptr+1)-1 downto MFB_DOWN_ITEM_WIDTH*mfb_i_ptr),42);
               trans.data_rd_ptr := trans.data_rd_ptr + MFB_DOWN_ITEM_WIDTH;

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

   -- post new DOWN MVB+MFB word from MVB+MFB FIFO (adds all newly started transactions to new_trans_send (their valids are in new_trans_send_vld))
   procedure post_new_down_mvb_mfb_word(fifo : inout slv_fifo_t; mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; new_trans_send : out mvb_mfb_trans_array_t; new_trans_send_vld : out std_logic_vector) is
      variable dummy : std_logic_vector(MVB_MFB_TRANS_WIDTH-1 downto 0);
      variable trans : mvb_mfb_trans_t;

      variable mvb_i_ptr        : integer; -- points to MVB ITEM
      variable mfb_i_ptr        : integer; -- points to MFB ITEM
      variable mfb_block_ptr    : integer; -- points to MFB BLOCK
      variable mfb_reg_ptr      : integer; -- points to MFB REGION

      variable l : line;
   begin
      new_trans_send_vld := (MVB_DOWN_ITEMS-1 downto 0 => '0');
      if ((mvb_i.dst_rdy='1' or mfb_i.dst_rdy='1') and fifo.empty='1') then
         mvb_i.src_rdy := '0';
         mfb_i.src_rdy := '0';
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
         mfb_i.sof     := (MFB_DOWN_REGIONS-1 downto 0 => '0');
         mfb_i.eof     := (MFB_DOWN_REGIONS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         if (trans.payload='1' and trans.data_rd_ptr>0) then
            insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
            fifo.fifo(0) := mvb_mfb_trans_ser(trans);

            if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- ended sending this transaction
               slv_fifo_pop(fifo,dummy);
            end if;
         end if;
      elsif (mvb_i.dst_rdy='1' and mfb_i.dst_rdy='0') then ---------
         -- send all front transactions, that don't have a payload
         mvb_i.src_rdy := '0';
         mvb_i.vld     := (MVB_DOWN_ITEMS-1 downto 0 => '0');

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         for i in 0 to MVB_DOWN_ITEMS-1 loop
            exit when (trans.payload='1');

            new_trans_send(mvb_i_ptr)     := trans;
            new_trans_send_vld(mvb_i_ptr) := '1';
            insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);

            slv_fifo_pop(fifo,dummy);

            exit when (fifo.empty='1');

            trans := mvb_mfb_trans_deser(fifo.fifo(0));
         end loop;
      elsif (mvb_i.dst_rdy='1' and mfb_i.dst_rdy='1') then ---------
         -- send anything
         mfb_i.src_rdy := '0';
         mfb_i.sof     := (MFB_DOWN_REGIONS-1 downto 0 => '0');
         mfb_i.eof     := (MFB_DOWN_REGIONS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         mvb_i.src_rdy := '0';
         mvb_i.vld     := (MVB_DOWN_ITEMS-1 downto 0 => '0');
         repeated_fill(mfb_i.data,DEFAULT_DATA_VALUE);

         trans := mvb_mfb_trans_deser(fifo.fifo(0));

         while true loop
            if (trans.payload='0') then
               -- no payload
               new_trans_send(mvb_i_ptr)     := trans;
               new_trans_send_vld(mvb_i_ptr) := '1';
               insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
               fifo.fifo(0) := mvb_mfb_trans_ser(trans);

               slv_fifo_pop(fifo,dummy);

               exit when (fifo.empty='1');

               trans := mvb_mfb_trans_deser(fifo.fifo(0));

               exit when (mvb_i_ptr=MVB_DOWN_ITEMS); -- filled the whole MVB word
            else
               -- yes payload
               if (trans.data_rd_ptr=0) then
                  -- start
                  mfb_i_ptr := shift_to_next_block(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE); -- new packet must start a new block

                  exit when (mfb_i_ptr=MFB_DOWN_ITEMS); -- shifted out of this MFB word

                  mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);
                  if (mfb_i.sof(mfb_reg_ptr)='1') then
                     mfb_i_ptr := shift_to_next_reg(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE); -- two packet must not start in the same region
                  end if;

                  exit when (mfb_i_ptr=MFB_DOWN_ITEMS); -- shifted out of this MFB word

                  new_trans_send(mvb_i_ptr)     := trans;
                  new_trans_send_vld(mvb_i_ptr) := '1';

                  insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
                  fifo.fifo(0) := mvb_mfb_trans_ser(trans);

                  if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- end of transaction
                     slv_fifo_pop(fifo,dummy);

                     exit when (fifo.empty='1');

                     trans := mvb_mfb_trans_deser(fifo.fifo(0));
                  end if;

                  exit when (mfb_i_ptr=MFB_DOWN_ITEMS); -- filled the whole MFB word
                  exit when (mvb_i_ptr=MVB_DOWN_ITEMS); -- filled the whole MVB word
               else
                  -- continue
                  insert_trans_part_in_up_mvb_mfb_word(trans,mvb_i,mfb_i,mvb_i_ptr,mfb_i_ptr);
                  fifo.fifo(0) := mvb_mfb_trans_ser(trans);

                  if (trans.data_rd_ptr=(trans.length+trans.after_gap_length)*32) then -- end of transaction
                     slv_fifo_pop(fifo,dummy);

                     exit when (fifo.empty='1');

                     trans := mvb_mfb_trans_deser(fifo.fifo(0));
                  end if;

                  exit when (mfb_i_ptr=MFB_DOWN_ITEMS); -- filled the whole MFB word
                  exit when (mvb_i_ptr=MVB_DOWN_ITEMS); -- filled the whole MVB word
               end if;
            end if;
         end loop;
      end if;
   end procedure;
   ----

   -- DOWN MVB+MFB word accept; checks correct MVB+MFB comunication and accepts MVB+MFB transactions
   -- mvb_i, mfb_i                                  - MVB+MFB interface status
   -- mvb_i_ptr, mfb_i_ptr                          - current MVB and MFB item read pointers
   -- unfinished                                    - transaction continuing from previous word
   -- unfinished_expected_len                       - expected total length of unfinished transaction
   -- unfinished_vld                                - valid bit of unfinished transaction
   -- accepted(MVB_DOWN_ITEMS-1 downto 0)           - newly completely accepted transactions
   -- accepted_vld(MVB_DOWN_ITEMS-1 downto 0)       - valid bits of newly accepted transactions
   procedure accept_down_mvb_mfb_word(mvb_i : inout mvb_i_t; mfb_i : inout mfb_i_t; mvb_i_ptr : inout integer; mfb_i_ptr : inout integer; unfinished : inout mvb_mfb_trans_t; unfinished_expected_len : inout integer; unfinished_vld : inout std_logic; accepted : out mvb_mfb_trans_array_t; accepted_vld : out std_logic_vector) is
      variable trans0 : mvb_mfb_trans_t;
      variable trans1 : mvb_mfb_trans_t;

      variable acc_ptr : integer;

      variable mfb_reg_ptr   : integer;
      variable mfb_block_ptr : integer;

      variable sof_ptr : integer;
      variable eof_ptr : integer;

      variable pos : integer;

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
            while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
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
            trans0 := mvb_mfb_trans_new('1',unfinished.address,mfb_i_ptr*MFB_DOWN_ITEM_WIDTH/32,0,unfinished.tag,unfinished.id,unfinished.completed,'1');
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

               exit when (mfb_i_ptr=MFB_DOWN_ITEMS); -- end of MFB word

               -- find next sof
               sof_ptr := -1;
               while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
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
               while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
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
                  unfinished := mvb_mfb_trans_new('1',address,(MFB_DOWN_ITEMS-sof_ptr)*MFB_DOWN_ITEM_WIDTH/32,0,tag,id,completed,'1');
                  unfinished.data(unfinished.length*32-1 downto 0) := mfb_i.data(MFB_DOWN_DATA_WIDTH-1 downto MFB_DOWN_ITEM_WIDTH*sof_ptr);
                  unfinished_expected_len := length;
                  unfinished_vld := '1';
               else
                  -- transaction started and ended in this word
                  trans0 := mvb_mfb_trans_new('1',address,(eof_ptr-sof_ptr+1)*MFB_DOWN_ITEM_WIDTH/32,0,tag,id,completed,'1');
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
            while (mfb_i_ptr<MFB_DOWN_ITEMS) loop
               mfb_reg_ptr := get_reg_ptr(mfb_i_ptr,MFB_DOWN_REG_SIZE,MFB_DOWN_BLOCK_SIZE);

               pos := to_integer(unsigned(mfb_i.sof_pos(MFB_DOWN_SOF_POS_WIDTH*(mfb_reg_ptr+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*mfb_reg_ptr)));
               if (mfb_i.sof(mfb_reg_ptr)='1') then
                  mfb_i_ptr := mfb_reg_ptr*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE+pos*MFB_DOWN_BLOCK_SIZE;
                  exit;
               end if;
               mfb_i_ptr := mfb_i_ptr+1;
            end loop;

         end if;
      elsif (unfinished_vld='1') then
         write(l,now);write(l,string'(" : "));
         write(l,string'("DOWN MFB src_rdy fall during transaction transmission!"));writeline(output,l);
         write(l,string'("Unfinished transaction: "));writeline(output,l);
         mvb_mfb_trans_print(unfinished);
         report "" severity failure;
      end if;

      -- set dst rdy to 1, if the whole MVB / MFB word was read
      if (mvb_i_ptr=MVB_DOWN_ITEMS) then
         mvb_i_ptr := 0;
         mvb_i.dst_rdy := '1';
      end if;

      if (mfb_i_ptr=MFB_DOWN_ITEMS) then
         mfb_i_ptr := 0;
         mfb_i.dst_rdy := '1';
      end if;
   end procedure;
   ----

end mvb_mfb_test_pkg;

