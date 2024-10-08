-- signal_organizer.vhd: SIgnal Organizer for AXI2MFB testbench
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields
use work.test_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity signal_organizer is
end entity signal_organizer;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of signal_organizer is

   ----
   type org_rq_user_t is record
      sop      : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
      sop_pos  : i_array_t       (MFB_UP_REGIONS-1 downto 0);
      eop      : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
      eop_pos  : i_array_t       (MFB_UP_REGIONS-1 downto 0);
      first_be : slv_array_t     (MFB_UP_REGIONS-1 downto 0)(4-1 downto 0);
      last_be  : slv_array_t     (MFB_UP_REGIONS-1 downto 0)(4-1 downto 0);
   end record;
   --
   function org_rq_user_deser(tuser : std_logic_vector) return org_rq_user_t is
      variable r : org_rq_user_t;
   begin
      for i in 0 to MFB_UP_REGIONS-1 loop
         r.first_be(i) := tuser(4*(i+1)-1 downto 4*i);
         r.last_be(i)  := tuser(MFB_UP_REGIONS*4+4*(i+1)-1 downto MFB_UP_REGIONS*4+4*i);
      end loop;

      r.sop     := (others => '0');
      r.sop_pos := (others => 0);
      r.eop     := (others => '0');
      r.eop_pos := (others => 0);

      if (DEVICE="ULTRASCALE") then
         for i in 0 to MFB_UP_REGIONS-1 loop
            r.sop(i)     := tuser((MFB_UP_REGIONS*4)*2+4+i);
            r.sop_pos(i) := to_integer(unsigned(
                tuser((MFB_UP_REGIONS*4)*2+4+MFB_UP_REGIONS+AXI_UP_SOP_POS_WIDTH*(i+1)-1
               downto (MFB_UP_REGIONS*4)*2+4+MFB_UP_REGIONS+AXI_UP_SOP_POS_WIDTH*i)
                                          ))*MFB_UP_BLOCK_SIZE/2;

            r.eop(i)     := tuser((MFB_UP_REGIONS*4)*2+4+MFB_UP_REGIONS+AXI_UP_SOP_POS_WIDTH*MFB_UP_REGIONS+i);
            r.eop_pos(i) := to_integer(unsigned(
                tuser((MFB_UP_REGIONS*4)*2+4+MFB_UP_REGIONS+AXI_UP_SOP_POS_WIDTH*MFB_UP_REGIONS+MFB_UP_REGIONS+AXI_UP_EOP_POS_WIDTH*(i+1)-1
               downto (MFB_UP_REGIONS*4)*2+4+MFB_UP_REGIONS+AXI_UP_SOP_POS_WIDTH*MFB_UP_REGIONS+MFB_UP_REGIONS+AXI_UP_EOP_POS_WIDTH*i)
                                          ));
         end loop;
      end if;

      return r;
   end function;
   ----

   ----
   type org_rq_t is record
      tdata  : slv_array_t(MFB_UP_REGIONS-1 downto 0)(MFB_UP_DATA_WIDTH/MFB_UP_REGIONS-1 downto 0);
      tuser  : org_rq_user_t;
      tlast  : std_logic;
      tkeep  : slv_array_t(MFB_UP_REGIONS-1 downto 0)(MFB_UP_DATA_WIDTH/MFB_UP_REGIONS/32-1 downto 0);
      tready : std_logic;
      tvalid : std_logic;
   end record;
   --
   function org_rq_deser(data : std_logic_vector; user : std_logic_vector; last : std_logic; keep : std_logic_vector; ready : std_logic; valid : std_logic) return org_rq_t is
      variable r : org_rq_t;
   begin
      for i in 0 to MFB_UP_REGIONS-1 loop
         r.tdata(i) := data((MFB_UP_DATA_WIDTH/MFB_UP_REGIONS)*(i+1)-1 downto (MFB_UP_DATA_WIDTH/MFB_UP_REGIONS)*i);
         r.tkeep(i) := keep((MFB_UP_DATA_WIDTH/MFB_UP_REGIONS/32)*(i+1)-1 downto (MFB_UP_DATA_WIDTH/MFB_UP_REGIONS/32)*i);
      end loop;

      r.tuser := org_rq_user_deser(user);

      r.tlast  := last;
      r.tready := ready;
      r.tvalid := valid;

      return r;
   end function;
   ----

   ----
   type org_rc_user_t is record
      sop      : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
      sop_pos  : i_array_t       (MFB_DOWN_REGIONS-1 downto 0);
      eop      : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
      eop_pos  : i_array_t       (MFB_DOWN_REGIONS-1 downto 0);
   end record;
   --
   function org_rc_user_deser(user : std_logic_vector) return org_rc_user_t is
      variable r : org_rc_user_t;
   begin
      if (DEVICE="ULTRASCALE") then
         for i in 0 to MFB_DOWN_REGIONS-1 loop
            r.sop(i)     := user(MFB_DOWN_DATA_WIDTH/8+i);
            r.sop_pos(i) := to_integer(unsigned(
                         user(MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+AXI_DOWN_SOP_POS_WIDTH*(i+1)-1
                       downto MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+AXI_DOWN_SOP_POS_WIDTH*i)
                                               ))*MFB_DOWN_BLOCK_SIZE;

            r.eop(i)     := user(MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+AXI_DOWN_SOP_POS_WIDTH*MFB_DOWN_REGIONS+i);
            r.eop_pos(i) := to_integer(unsigned(
                         user(MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+AXI_DOWN_SOP_POS_WIDTH*MFB_DOWN_REGIONS+MFB_DOWN_REGIONS+AXI_DOWN_EOP_POS_WIDTH*(i+1)-1
                       downto MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+AXI_DOWN_SOP_POS_WIDTH*MFB_DOWN_REGIONS+MFB_DOWN_REGIONS+AXI_DOWN_EOP_POS_WIDTH*i)
                                               ));
         end loop;
      else
         for i in 0 to MFB_DOWN_REGIONS-1 loop
            r.sop(i)     := user(MFB_DOWN_DATA_WIDTH/8+i);

            r.eop(i)     := user(MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+(AXI_DOWN_EOP_POS_WIDTH+1)*i);
            r.eop_pos(i) := to_integer(unsigned(
                         user(MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+MFB_DOWN_REGIONS+(AXI_DOWN_EOP_POS_WIDTH+1)*(i+1)-1
                       downto MFB_DOWN_DATA_WIDTH/8+MFB_DOWN_REGIONS+MFB_DOWN_REGIONS+(AXI_DOWN_EOP_POS_WIDTH+1)*i+1)
                                               ));
         end loop;
         r.sop_pos := (others => 0);
      end if;

      return r;
   end function;
   ----

   ----
   type org_rc_t is record
      tdata  : slv_array_t(MFB_DOWN_REGIONS-1 downto 0)(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
      tuser  : org_rc_user_t;
      tvalid : std_logic;
      tready : std_logic;
   end record;
   --
   function org_rc_deser(data : std_logic_vector; user : std_logic_vector; valid : std_logic; ready : std_logic) return org_rc_t is
      variable r : org_rc_t;
   begin
      for i in 0 to MFB_DOWN_REGIONS-1 loop
         r.tdata(i) := data((MFB_DOWN_DATA_WIDTH/MFB_DOWN_REGIONS)*(i+1)-1 downto (MFB_DOWN_DATA_WIDTH/MFB_DOWN_REGIONS)*i);
      end loop;

      r.tuser  := org_rc_user_deser(user);

      r.tvalid := valid;
      r.tready := ready;

      return r;
   end function;
   ----

   ----
   type org_dma_up_mvb_t is record
      address : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0);
      length  : i_array_t(MVB_UP_ITEMS-1 downto 0);
      rd_wr   : str_array_t(MVB_UP_ITEMS-1 downto 0)(2 downto 1); -- WR / RD
      tag     : i_array_t(MVB_UP_ITEMS-1 downto 0);
      id      : i_array_t(MVB_UP_ITEMS-1 downto 0);

      vld     : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;

   type org_dma_up_mvb_array_t is array (natural range <>) of org_dma_up_mvb_t;
   --
   function org_dma_up_mvb_deser(data : std_logic_vector; vld : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_dma_up_mvb_t is
      variable hdr : std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);
      variable r   : org_dma_up_mvb_t;
   begin
      for i in 0 to MVB_UP_ITEMS-1 loop
         hdr       := data(DMA_UPHDR_WIDTH*(i+1)-1 downto DMA_UPHDR_WIDTH*i);

         r.address(i) := hdr(DMA_REQUEST_GLOBAL);
         r.length(i)  := to_integer(unsigned(hdr(DMA_REQUEST_LENGTH)));
         r.rd_wr(i)   := "RD" when hdr(DMA_REQUEST_TYPE)=DMA_TYPE_READ else "WR";
         r.tag(i)     := to_integer(unsigned(hdr(DMA_REQUEST_TAG)));
         r.id(i)      := to_integer(unsigned(hdr(DMA_REQUEST_UNITID)));
      end loop;

      r.vld     := vld;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;

   function org_dma_up_mvb_array_deser(data : slv_array_t; vld : slv_array_t; src_rdy : std_logic_vector; dst_rdy : std_logic_vector) return org_dma_up_mvb_array_t is
      variable r   : org_dma_up_mvb_array_t(DMA_PORTS-1 downto 0);
   begin
      for i in 0 to DMA_PORTS-1 loop
         r(i) := org_dma_up_mvb_deser(data(i),vld(i),src_rdy(i),dst_rdy(i));
      end loop;
      return r;
   end function;
   ----

   ----
   type org_dma_down_mvb_t is record
      length    : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      tag       : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      id        : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      completed : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);

      vld       : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
      src_rdy   : std_logic;
      dst_rdy   : std_logic;
   end record;

   type org_dma_down_mvb_array_t is array (natural range <>) of org_dma_down_mvb_t;
   --
   function org_dma_down_mvb_deser(data : std_logic_vector; vld : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_dma_down_mvb_t is
      variable hdr : std_logic_vector(DMA_DOWNHDR_WIDTH-1 downto 0);
      variable r   : org_dma_down_mvb_t;
   begin
      for i in 0 to MVB_DOWN_ITEMS-1 loop
         hdr       := data(DMA_DOWNHDR_WIDTH*(i+1)-1 downto DMA_DOWNHDR_WIDTH*i);

         r.completed(i) := hdr(DMA_COMPLETION_COMPLETED'low);
         r.length(i)    := to_integer(unsigned(hdr(DMA_COMPLETION_LENGTH)));
         r.tag(i)       := to_integer(unsigned(hdr(DMA_COMPLETION_TAG)));
         r.id(i)        := to_integer(unsigned(hdr(DMA_COMPLETION_UNITID)));
      end loop;

      r.vld     := vld;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;

   function org_dma_down_mvb_array_deser(data : slv_array_t; vld : slv_array_t; src_rdy : std_logic_vector; dst_rdy : std_logic_vector) return org_dma_down_mvb_array_t is
      variable r   : org_dma_down_mvb_array_t(DMA_PORTS-1 downto 0);
   begin
      for i in 0 to DMA_PORTS-1 loop
         r(i) := org_dma_down_mvb_deser(data(i),vld(i),src_rdy(i),dst_rdy(i));
      end loop;
      return r;
   end function;
   ----

   ----
   type org_pcie_up_mvb_t is record
      address : slv_array_t(MVB_UP_ITEMS-1 downto 0)(DMA_ADDR_WIDTH-1 downto 0);
      length  : i_array_t(MVB_UP_ITEMS-1 downto 0);
      rd_wr   : str_array_t(MVB_UP_ITEMS-1 downto 0)(2 downto 1); -- WR / RD
      tag     : i_array_t(MVB_UP_ITEMS-1 downto 0);

      vld     : std_logic_vector(MVB_UP_ITEMS-1 downto 0);
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;
   --
   function org_pcie_up_mvb_deser(data : std_logic_vector; vld : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_pcie_up_mvb_t is
      variable hdr : std_logic_vector(PCIE_UPHDR_WIDTH-1 downto 0);
      variable r   : org_pcie_up_mvb_t;
   begin
      for i in 0 to MVB_UP_ITEMS-1 loop
         hdr          := data(PCIE_UPHDR_WIDTH*(i+1)-1 downto PCIE_UPHDR_WIDTH*i);

         if (DEVICE="STRATIX10") then
            if (hdr(29)='1') then
               r.address(i) := hdr(DMA_ADDR_WIDTH/2+64-1 downto 64) & hdr(DMA_ADDR_WIDTH+64-1 downto DMA_ADDR_WIDTH/2+64);
            else
               r.address(i) := (DMA_ADDR_WIDTH/2-1 downto 0 => '0') & hdr(DMA_ADDR_WIDTH/2+64-1 downto 64);
            end if;
            r.length(i)  := to_integer(unsigned(hdr(10-1 downto 0)));
            r.rd_wr(i)   := "RD" when hdr(30)=DMA_TYPE_READ(0) else "WR";
            r.tag(i)     := to_integer(unsigned(hdr(PCIE_TAG_WIDTH+40-1 downto 40)));
         else
            r.address(i) := hdr(DMA_ADDR_WIDTH-1 downto 0);
            r.length(i)  := to_integer(unsigned(hdr(DMA_LEN_WIDTH+DMA_ADDR_WIDTH-1 downto DMA_ADDR_WIDTH)));
            r.rd_wr(i)   := "RD" when hdr(DMA_LEN_WIDTH+DMA_ADDR_WIDTH)=DMA_TYPE_READ(0) else "WR";
            r.tag(i)     := to_integer(unsigned(hdr(PCIE_TAG_WIDTH+8+DMA_REQUEST_VFID'high+1-DMA_REQUEST_VFID'low+1+3+1+DMA_LEN_WIDTH+DMA_ADDR_WIDTH-1 downto 8+DMA_REQUEST_VFID'high+1-DMA_REQUEST_VFID'low+1+3+1+DMA_LEN_WIDTH+DMA_ADDR_WIDTH)));
         end if;
      end loop;

      r.vld     := vld;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;
   ----

   ----
   type org_pcie_down_mvb_t is record
      address_low : slv_array_t(MVB_DOWN_ITEMS-1 downto 0)(PCIE_LOW_ADDR_WIDTH-1 downto 0);
      length      : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      rem_bytes   : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      completed   : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
      tag         : i_array_t(MVB_DOWN_ITEMS-1 downto 0);

      vld     : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;
   --
   function org_pcie_down_mvb_deser(data : std_logic_vector; vld : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_pcie_down_mvb_t is
      variable hdr : std_logic_vector(PCIE_DOWNHDR_WIDTH-1 downto 0);
      variable r   : org_pcie_down_mvb_t;
   begin
      for i in 0 to MVB_DOWN_ITEMS-1 loop
         hdr       := data(PCIE_DOWNHDR_WIDTH*(i+1)-1 downto PCIE_DOWNHDR_WIDTH*i);

         if (DEVICE="STRATIX10") then
            r.address_low(i) := hdr(PCIE_LOW_ADDR_WIDTH+64-1 downto 64);
            r.length(i)      := to_integer(unsigned(hdr(10-1 downto 0)));
            r.rem_bytes(i)   := to_integer(unsigned(hdr(12+32-1 downto 32)));
            r.tag(i)         := to_integer(unsigned(hdr(72+PCIE_TAG_WIDTH-1 downto 72)));
            r.completed(i)   := '1' when r.rem_bytes(i)=r.length(i)*4 else '0';
         else
            r.address_low(i) := hdr(PCIE_LOW_ADDR_WIDTH-1 downto 0);
            r.length(i)      := to_integer(unsigned(hdr(32+11-1 downto 32)));
            r.rem_bytes(i)   := -1;
            r.tag(i)         := to_integer(unsigned(hdr(64+PCIE_TAG_WIDTH-1 downto 64)));
            r.completed(i)   := hdr(30);
         end if;
      end loop;

      r.vld     := vld;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;
   ----

   ----
   type org_up_mfb_t is record
      data      : slv_array_t(MFB_UP_REGIONS-1 downto 0)(MFB_UP_DATA_WIDTH/MFB_UP_REGIONS-1 downto 0);
      sof       : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
      sof_pos   : i_array_t(MFB_UP_REGIONS-1 downto 0); -- item pointer
      eof       : std_logic_vector(MFB_UP_REGIONS-1 downto 0);
      eof_pos   : i_array_t(MFB_UP_REGIONS-1 downto 0); -- item pointer

      src_rdy   : std_logic;
      dst_rdy   : std_logic;
   end record;

   type org_up_mfb_array_t is array (natural range <>) of org_up_mfb_t;
   --
   function org_up_mfb_deser(data : std_logic_vector; sof_pos : std_logic_vector; eof_pos : std_logic_vector; sof : std_logic_vector; eof : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_up_mfb_t is
      variable r   : org_up_mfb_t;
   begin
      for i in 0 to MFB_UP_REGIONS-1 loop
         r.data(i) := data(MFB_UP_DATA_WIDTH/MFB_UP_REGIONS*(i+1)-1 downto MFB_UP_DATA_WIDTH/MFB_UP_REGIONS*i);
         r.sof_pos(i) := to_integer(unsigned(sof_pos(MFB_UP_SOF_POS_WIDTH*(i+1)-1 downto MFB_UP_SOF_POS_WIDTH*i)))*MFB_UP_BLOCK_SIZE/2;
         r.eof_pos(i) := to_integer(unsigned(eof_pos(MFB_UP_EOF_POS_WIDTH*(i+1)-1 downto MFB_UP_EOF_POS_WIDTH*i)));
      end loop;

      r.sof     := sof;
      r.eof     := eof;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;

   function org_up_mfb_array_deser(data : slv_array_t; sof_pos : slv_array_t; eof_pos : slv_array_t; sof : slv_array_t; eof : slv_array_t; src_rdy : std_logic_vector; dst_rdy : std_logic_vector) return org_up_mfb_array_t is
      variable r   : org_up_mfb_array_t(DMA_PORTS-1 downto 0);
   begin
      for i in 0 to DMA_PORTS-1 loop
         r(i) := org_up_mfb_deser(data(i),sof_pos(i),eof_pos(i),sof(i),eof(i),src_rdy(i),dst_rdy(i));
      end loop;
      return r;
   end function;
   ----

   ----
   type org_dma_up_mfb_t is record
      data      : slv_array_t(DMA_MFB_UP_REGIONS-1 downto 0)(DMA_MFB_UP_DATA_WIDTH/DMA_MFB_UP_REGIONS-1 downto 0);
      sof       : std_logic_vector(DMA_MFB_UP_REGIONS-1 downto 0);
      sof_pos   : i_array_t(DMA_MFB_UP_REGIONS-1 downto 0); -- item pointer
      eof       : std_logic_vector(DMA_MFB_UP_REGIONS-1 downto 0);
      eof_pos   : i_array_t(DMA_MFB_UP_REGIONS-1 downto 0); -- item pointer

      src_rdy   : std_logic;
      dst_rdy   : std_logic;
   end record;

   type org_dma_up_mfb_array_t is array (natural range <>) of org_dma_up_mfb_t;
   --
   function org_dma_up_mfb_deser(data : std_logic_vector; sof_pos : std_logic_vector; eof_pos : std_logic_vector; sof : std_logic_vector; eof : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_dma_up_mfb_t is
      variable r   : org_dma_up_mfb_t;
   begin
      for i in 0 to DMA_MFB_UP_REGIONS-1 loop
         r.data(i) := data(DMA_MFB_UP_DATA_WIDTH/DMA_MFB_UP_REGIONS*(i+1)-1 downto DMA_MFB_UP_DATA_WIDTH/DMA_MFB_UP_REGIONS*i);
         r.sof_pos(i) := to_integer(unsigned(sof_pos(MFB_UP_SOF_POS_WIDTH*(i+1)-1 downto MFB_UP_SOF_POS_WIDTH*i)))*MFB_UP_BLOCK_SIZE/2;
         r.eof_pos(i) := to_integer(unsigned(eof_pos(MFB_UP_EOF_POS_WIDTH*(i+1)-1 downto MFB_UP_EOF_POS_WIDTH*i)));
      end loop;

      r.sof     := sof;
      r.eof     := eof;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;

   function org_dma_up_mfb_array_deser(data : slv_array_t; sof_pos : slv_array_t; eof_pos : slv_array_t; sof : slv_array_t; eof : slv_array_t; src_rdy : std_logic_vector; dst_rdy : std_logic_vector) return org_dma_up_mfb_array_t is
      variable r   : org_dma_up_mfb_array_t(DMA_PORTS-1 downto 0);
   begin
      for i in 0 to DMA_PORTS-1 loop
         r(i) := org_dma_up_mfb_deser(data(i),sof_pos(i),eof_pos(i),sof(i),eof(i),src_rdy(i),dst_rdy(i));
      end loop;
      return r;
   end function;
   ----

   ----
   type org_down_mfb_t is record
      data      : slv_array_t(MFB_DOWN_REGIONS-1 downto 0)(MFB_DOWN_DATA_WIDTH/MFB_DOWN_REGIONS-1 downto 0);
      sof       : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
      sof_pos   : i_array_t(MFB_DOWN_REGIONS-1 downto 0); -- item pointer
      eof       : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0);
      eof_pos   : i_array_t(MFB_DOWN_REGIONS-1 downto 0); -- item pointer

      src_rdy   : std_logic;
      dst_rdy   : std_logic;
   end record;

   type org_down_mfb_array_t is array (natural range <>) of org_down_mfb_t;
   --
   function org_down_mfb_deser(data : std_logic_vector; sof_pos : std_logic_vector; eof_pos : std_logic_vector; sof : std_logic_vector; eof : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_down_mfb_t is
      variable r   : org_down_mfb_t;
   begin
      for i in 0 to MFB_DOWN_REGIONS-1 loop
         r.data(i) := data(MFB_DOWN_DATA_WIDTH/MFB_DOWN_REGIONS*(i+1)-1 downto MFB_DOWN_DATA_WIDTH/MFB_DOWN_REGIONS*i);
         r.sof_pos(i) := to_integer(unsigned(sof_pos(MFB_DOWN_SOF_POS_WIDTH*(i+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*i)))*MFB_DOWN_BLOCK_SIZE/2;
         r.eof_pos(i) := to_integer(unsigned(eof_pos(MFB_DOWN_EOF_POS_WIDTH*(i+1)-1 downto MFB_DOWN_EOF_POS_WIDTH*i)));
      end loop;

      r.sof     := sof;
      r.eof     := eof;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;

   function org_down_mfb_array_deser(data : slv_array_t; sof_pos : slv_array_t; eof_pos : slv_array_t; sof : slv_array_t; eof : slv_array_t; src_rdy : std_logic_vector; dst_rdy : std_logic_vector) return org_down_mfb_array_t is
      variable r   : org_down_mfb_array_t(DMA_PORTS-1 downto 0);
   begin
      for i in 0 to DMA_PORTS-1 loop
         r(i) := org_down_mfb_deser(data(i),sof_pos(i),eof_pos(i),sof(i),eof(i),src_rdy(i),dst_rdy(i));
      end loop;
      return r;
   end function;
   ----

   ----
   type org_dma_down_mfb_t is record
      data      : slv_array_t(DMA_MFB_DOWN_REGIONS-1 downto 0)(DMA_MFB_DOWN_DATA_WIDTH/DMA_MFB_DOWN_REGIONS-1 downto 0);
      sof       : std_logic_vector(DMA_MFB_DOWN_REGIONS-1 downto 0);
      sof_pos   : i_array_t(DMA_MFB_DOWN_REGIONS-1 downto 0); -- item pointer
      eof       : std_logic_vector(DMA_MFB_DOWN_REGIONS-1 downto 0);
      eof_pos   : i_array_t(DMA_MFB_DOWN_REGIONS-1 downto 0); -- item pointer

      src_rdy   : std_logic;
      dst_rdy   : std_logic;
   end record;

   type org_dma_down_mfb_array_t is array (natural range <>) of org_dma_down_mfb_t;
   --
   function org_dma_down_mfb_deser(data : std_logic_vector; sof_pos : std_logic_vector; eof_pos : std_logic_vector; sof : std_logic_vector; eof : std_logic_vector; src_rdy : std_logic; dst_rdy : std_logic) return org_dma_down_mfb_t is
      variable r   : org_dma_down_mfb_t;
   begin
      for i in 0 to DMA_MFB_DOWN_REGIONS-1 loop
         r.data(i) := data(DMA_MFB_DOWN_DATA_WIDTH/DMA_MFB_DOWN_REGIONS*(i+1)-1 downto DMA_MFB_DOWN_DATA_WIDTH/DMA_MFB_DOWN_REGIONS*i);
         r.sof_pos(i) := to_integer(unsigned(sof_pos(MFB_DOWN_SOF_POS_WIDTH*(i+1)-1 downto MFB_DOWN_SOF_POS_WIDTH*i)))*MFB_DOWN_BLOCK_SIZE/2;
         r.eof_pos(i) := to_integer(unsigned(eof_pos(MFB_DOWN_EOF_POS_WIDTH*(i+1)-1 downto MFB_DOWN_EOF_POS_WIDTH*i)));
      end loop;

      r.sof     := sof;
      r.eof     := eof;
      r.src_rdy := src_rdy;
      r.dst_rdy := dst_rdy;

      return r;
   end function;

   function org_dma_down_mfb_array_deser(data : slv_array_t; sof_pos : slv_array_t; eof_pos : slv_array_t; sof : slv_array_t; eof : slv_array_t; src_rdy : std_logic_vector; dst_rdy : std_logic_vector) return org_dma_down_mfb_array_t is
      variable r   : org_dma_down_mfb_array_t(DMA_PORTS-1 downto 0);
   begin
      for i in 0 to DMA_PORTS-1 loop
         r(i) := org_dma_down_mfb_deser(data(i),sof_pos(i),eof_pos(i),sof(i),eof(i),src_rdy(i),dst_rdy(i));
      end loop;
      return r;
   end function;
   ----

   ----
   type org_tagm_rel_t is record
      pcie_tag : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      low_addr : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      len      : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      rel      : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
      vld      : std_logic_vector(MVB_DOWN_ITEMS-1 downto 0);
      dma_tag  : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
      dma_id   : i_array_t(MVB_DOWN_ITEMS-1 downto 0);
   end record;
   --
   function org_tagm_rel_deser(tag : std_logic_vector; low_addr : std_logic_vector; len : std_logic_vector; rel : std_logic_vector; vld : std_logic_vector; dma_tag : std_logic_vector; dma_id : std_logic_vector) return org_tagm_rel_t is
      variable r : org_tagm_rel_t;
   begin
      for i in 0 to MVB_DOWN_ITEMS-1 loop
         r.pcie_tag(i) := to_integer(unsigned(tag(PCIE_TAG_WIDTH*(i+1)-1 downto PCIE_TAG_WIDTH*i)));
         r.low_addr(i) := to_integer(unsigned(low_addr(PCIE_LOW_ADDR_WIDTH*(i+1)-1 downto PCIE_LOW_ADDR_WIDTH*i)));
         r.len(i)      := to_integer(unsigned(len(DMA_LEN_WIDTH*(i+1)-1 downto DMA_LEN_WIDTH*i)));
         r.dma_tag(i)  := to_integer(unsigned(dma_tag(DMA_TAG_WIDTH*(i+1)-1 downto DMA_TAG_WIDTH*i)));
         r.dma_id(i)   := to_integer(unsigned(dma_id(DMA_ID_WIDTH*(i+1)-1 downto DMA_ID_WIDTH*i)));
      end loop;
      r.rel := rel;
      r.vld := vld;

      return r;
   end function;
   ----

   -------------------------------------------------------------------------------------

   signal org_UP_MVB : org_dma_up_mvb_array_t(DMA_PORTS-1 downto 0);
   signal org_UP_MFB : org_dma_up_mfb_array_t(DMA_PORTS-1 downto 0);

   signal org_up_mvb_asfifo_out          : org_dma_up_mvb_array_t(DMA_PORTS-1 downto 0);
   signal org_up_mfb_asfifo_out          : org_dma_up_mfb_array_t(DMA_PORTS-1 downto 0);
   signal org_up_mfb_trans_out           : org_up_mfb_array_t    (DMA_PORTS-1 downto 0);
   signal org_up_mvb_merge_out           : org_dma_up_mvb_t;
   signal org_up_mfb_merge_out           : org_up_mfb_t;
   signal org_up_mvb_mrgfi_out           : org_dma_up_mvb_t;
   signal org_tagm_mvb_in                : org_dma_up_mvb_t;
   signal org_tagm_mvb_out               : org_dma_up_mvb_t;
   signal org_up_mvb_dma2pcie_out        : org_pcie_up_mvb_t;
   signal org_up_mvb_c_checker_out       : org_pcie_up_mvb_t;
   signal org_up_mfb_hdr_merge_out       : org_up_mfb_t;

   signal org_RQ     : org_rq_t;
   signal org_RQ_MVB : org_pcie_up_mvb_t;
   signal org_RQ_MFB : org_up_mfb_t;

   signal org_RC_MVB : org_pcie_down_mvb_t;
   signal org_RC_MFB : org_down_mfb_t;
   signal org_RC     : org_rc_t;

   signal org_down_mfb_get_items_in      : org_down_mfb_t;
   signal org_down_mfb_cutter_in         : org_down_mfb_t;
   signal org_down_mvb_stfifo_in         : org_pcie_down_mvb_t;
   signal org_down_mfb_stfifo_in         : org_down_mfb_t;
   signal org_down_mvb_pcie2dma_in       : org_pcie_down_mvb_t;
   signal org_tagm_release               : org_tagm_rel_t;
   signal org_down_mfb_splfi_in          : org_down_mfb_t;
   signal org_down_mvb_split_in          : org_dma_down_mvb_t;
   signal org_down_mfb_split_in          : org_down_mfb_t;
   signal org_down_mfb_trans_in          : org_down_mfb_array_t    (DMA_PORTS-1 downto 0);
   signal org_down_mvb_asfifo_in         : org_dma_down_mvb_array_t(DMA_PORTS-1 downto 0);
   signal org_down_mfb_asfifo_in         : org_dma_down_mfb_array_t(DMA_PORTS-1 downto 0);

   signal org_DOWN_MVB : org_dma_down_mvb_array_t(DMA_PORTS-1 downto 0);
   signal org_DOWN_MFB : org_dma_down_mfb_array_t(DMA_PORTS-1 downto 0);

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -------------------------------------------------------------------------------------

   org_UP_MVB <= org_dma_up_mvb_array_deser
                              (
                               <<signal ^.uut.UP_MVB_DATA    : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.UP_MVB_VLD     : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0)>>,
                               <<signal ^.uut.UP_MVB_SRC_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.UP_MVB_DST_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_UP_MFB <= org_dma_up_mfb_array_deser
                              (
                               <<signal ^.uut.UP_MFB_DATA    : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.UP_MFB_SOF_POS : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.UP_MFB_EOF_POS : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.UP_MFB_SOF     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.UP_MFB_EOF     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.UP_MFB_SRC_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.UP_MFB_DST_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_up_mvb_asfifo_out <= org_dma_up_mvb_array_deser
                              (
                               <<signal ^.uut.up_mvb_asfifo_out_data    : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_asfifo_out_vld     : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_UP_ITEMS-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_asfifo_out_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_asfifo_out_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_up_mfb_asfifo_out      <= org_dma_up_mfb_array_deser
                              (
                               <<signal ^.uut.up_mfb_asfifo_out_data    : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_asfifo_out_sof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_asfifo_out_eof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_asfifo_out_sof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_asfifo_out_eof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_asfifo_out_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_asfifo_out_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_up_mfb_trans_out      <= org_up_mfb_array_deser
                              (
                               <<signal ^.uut.up_mfb_trans_out_data    : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_trans_out_sof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_trans_out_eof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_trans_out_sof     : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_trans_out_eof     : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_trans_out_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_trans_out_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_up_mvb_merge_out <= org_dma_up_mvb_deser
                              (
                               <<signal ^.uut.up_mvb_merge_out_data    : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_merge_out_vld     : std_logic_vector(MVB_UP_ITEMS-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_merge_out_src_rdy : std_logic>>,
                               <<signal ^.uut.up_mvb_merge_out_dst_rdy : std_logic>>
                              );

   org_up_mfb_merge_out      <= org_up_mfb_deser
                              (
                               <<signal ^.uut.up_mfb_merge_out_data    : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_merge_out_sof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_merge_out_eof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_merge_out_sof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_merge_out_eof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_merge_out_src_rdy : std_logic>>,
                               <<signal ^.uut.up_mfb_merge_out_dst_rdy : std_logic>>
                              );

   org_up_mvb_mrgfi_out <= org_dma_up_mvb_deser
                              (
                               <<signal ^.uut.up_mvb_mrgfi_out_data    : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_mrgfi_out_vld     : std_logic_vector(MVB_UP_ITEMS-1 downto 0)>>,
                               <<signal ^.uut.up_mvb_mrgfi_out_src_rdy : std_logic>>,
                               <<signal ^.uut.up_mvb_mrgfi_out_dst_rdy : std_logic>>
                              );

   org_tagm_mvb_in <= org_dma_up_mvb_deser
                              (
                               <<signal ^.uut.tagm_mvb_in          : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.tagm_mvb_in_vld      : std_logic_vector(MVB_UP_ITEMS                -1 downto 0)>>,
                               <<signal ^.uut.tagm_mvb_in_src_rdy  : std_logic>>,
                               <<signal ^.uut.tagm_mvb_in_dst_rdy  : std_logic>>
                              );

   org_tagm_mvb_out <= org_dma_up_mvb_deser
                              (
                               <<signal ^.uut.tagm_mvb_out          : std_logic_vector(MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.tagm_mvb_out_vld      : std_logic_vector(MVB_UP_ITEMS                -1 downto 0)>>,
                               <<signal ^.uut.tagm_mvb_out_src_rdy  : std_logic>>,
                               <<signal ^.uut.tagm_mvb_out_dst_rdy  : std_logic>>
                              );

   org_up_mvb_dma2pcie_out      <= org_pcie_up_mvb_deser
                              (
                               <<signal ^.uut.up_mvb_dma2pcie_out_data         : std_logic_vector(MVB_UP_ITEMS*PCIE_UPHDR_WIDTH     -1 downto 0)>>,
                               <<signal ^.uut.up_mvb_dma2pcie_out_vld          : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0)>>,
                               <<signal ^.uut.up_mvb_dma2pcie_out_src_rdy      : std_logic>>,
                               <<signal ^.uut.up_mvb_dma2pcie_out_dst_rdy      : std_logic>>
                              );

   org_up_mvb_c_checker_out     <= org_pcie_up_mvb_deser
                              (
                               <<signal ^.uut.up_mvb_c_checker_out_data         : std_logic_vector(MVB_UP_ITEMS*PCIE_UPHDR_WIDTH     -1 downto 0)>>,
                               <<signal ^.uut.up_mvb_c_checker_out_vld          : std_logic_vector(MVB_UP_ITEMS                      -1 downto 0)>>,
                               <<signal ^.uut.up_mvb_c_checker_out_src_rdy      : std_logic>>,
                               <<signal ^.uut.up_mvb_c_checker_out_dst_rdy      : std_logic>>
                              );

   org_up_mfb_hdr_merge_out      <= org_up_mfb_deser
                              (
                               <<signal ^.uut.up_mfb_hdr_merge_out_data    : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_hdr_merge_out_sof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_hdr_merge_out_eof_pos : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_hdr_merge_out_sof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_hdr_merge_out_eof     : std_logic_vector(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.up_mfb_hdr_merge_out_src_rdy : std_logic>>,
                               <<signal ^.uut.up_mfb_hdr_merge_out_dst_rdy : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_RQ <= org_rq_deser
                              (
                               <<signal ^.uut.RQ_TDATA     : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RQ_TUSER     : std_logic_vector(RQ_TUSER_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RQ_TLAST     : std_logic>>,
                               <<signal ^.uut.RQ_TKEEP     : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH/32-1 downto 0)>>,
                               <<signal ^.uut.RQ_TREADY    : std_logic>>,
                               <<signal ^.uut.RQ_TVALID    : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_RQ_MVB <= org_pcie_up_mvb_deser
                              (
                               <<signal ^.uut.RQ_MVB_HDR_DATA : std_logic_vector(MFB_UP_REGIONS*PCIE_UPHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RQ_MVB_VLD      : std_logic_vector(MFB_UP_REGIONS                 -1 downto 0)>>,
                               <<signal ^.uut.RQ_MFB_SRC_RDY  : std_logic>>,
                               <<signal ^.uut.RQ_MFB_DST_RDY  : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_RQ_MFB <= org_up_mfb_deser
                              (
                               <<signal ^.uut.RQ_MFB_DATA    : std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RQ_MFB_SOF_POS : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.RQ_MFB_EOF_POS : std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.RQ_MFB_SOF     : std_logic_vector(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.RQ_MFB_EOF     : std_logic_vector(MFB_UP_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.RQ_MFB_SRC_RDY : std_logic>>,
                               <<signal ^.uut.RQ_MFB_DST_RDY : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_RC_MVB <= org_pcie_down_mvb_deser
                              (
                               <<signal ^.uut.RC_MVB_HDR_DATA : std_logic_vector(MFB_DOWN_REGIONS*PCIE_DOWNHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RC_MVB_VLD      : std_logic_vector(MFB_DOWN_REGIONS                   -1 downto 0)>>,
                               <<signal ^.uut.RC_MFB_SRC_RDY  : std_logic>>,
                               <<signal ^.uut.RC_MFB_DST_RDY  : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_RC_MFB <= org_down_mfb_deser
                              (
                               <<signal ^.uut.RC_MFB_DATA    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RC_MFB_SOF_POS : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.RC_MFB_EOF_POS : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.RC_MFB_SOF     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.RC_MFB_EOF     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.RC_MFB_SRC_RDY : std_logic>>,
                               <<signal ^.uut.RC_MFB_DST_RDY : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_RC <= org_rc_deser
                              (
                               <<signal ^.uut.RC_TDATA     : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RC_TUSER     : std_logic_vector(RC_TUSER_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.RC_TVALID    : std_logic>>,
                               <<signal ^.uut.RC_TREADY    : std_logic>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_down_mfb_get_items_in      <= org_down_mfb_deser
                              (
                               <<signal ^.uut.down_mfb_get_items_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_get_items_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_get_items_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_get_items_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_get_items_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_get_items_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mfb_get_items_in_dst_rdy : std_logic>>
                              );

   org_down_mfb_cutter_in      <= org_down_mfb_deser
                              (
                               <<signal ^.uut.down_mfb_cutter_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_cutter_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_cutter_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_cutter_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_cutter_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_cutter_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mfb_cutter_in_dst_rdy : std_logic>>
                              );

   org_down_mvb_stfifo_in      <= org_pcie_down_mvb_deser
                              (
                               <<signal ^.uut.down_mvb_stfifo_in_data    : std_logic_vector(MVB_DOWN_ITEMS*PCIE_DOWNHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mvb_stfifo_in_vld     : std_logic_vector(MVB_DOWN_ITEMS                   -1 downto 0)>>,
                               <<signal ^.uut.down_mvb_stfifo_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mvb_stfifo_in_dst_rdy : std_logic>>
                              );

   org_down_mfb_stfifo_in      <= org_down_mfb_deser
                              (
                               <<signal ^.uut.down_mfb_stfifo_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_stfifo_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_stfifo_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_stfifo_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_stfifo_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_stfifo_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mfb_stfifo_in_dst_rdy : std_logic>>
                              );

   org_down_mvb_pcie2dma_in      <= org_pcie_down_mvb_deser
                              (
                               <<signal ^.uut.down_mvb_pcie2dma_in_data    : std_logic_vector(MVB_DOWN_ITEMS*PCIE_DOWNHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mvb_pcie2dma_in_vld     : std_logic_vector(MVB_DOWN_ITEMS                   -1 downto 0)>>,
                               <<signal ^.uut.down_mvb_pcie2dma_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mvb_pcie2dma_in_dst_rdy : std_logic>>
                              );

   org_tagm_release <= org_tagm_rel_deser
                              (
                               <<signal ^.uut.tagm_tag                : std_logic_vector(MVB_DOWN_ITEMS*PCIE_TAG_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.tagm_tag_compl_low_addr : std_logic_vector(MVB_DOWN_ITEMS*PCIE_LOW_ADDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.tagm_tag_compl_len      : std_logic_vector(MVB_DOWN_ITEMS*(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1)-1 downto 0)>>,
                               <<signal ^.uut.tagm_tag_release        : std_logic_vector(MVB_DOWN_ITEMS               -1 downto 0)>>,
                               <<signal ^.uut.tagm_tag_vld            : std_logic_vector(MVB_DOWN_ITEMS               -1 downto 0)>>,
                               <<signal ^.uut.tagm_dma_down_tag       : std_logic_vector(MVB_DOWN_ITEMS*DMA_TAG_WIDTH -1 downto 0)>>,
                               <<signal ^.uut.tagm_dma_down_id        : std_logic_vector(MVB_DOWN_ITEMS*DMA_ID_WIDTH  -1 downto 0)>>
                              );

   org_down_mfb_splfi_in      <= org_down_mfb_deser
                              (
                               <<signal ^.uut.down_mfb_splfi_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_splfi_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_splfi_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_splfi_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_splfi_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_splfi_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mfb_splfi_in_dst_rdy : std_logic>>
                              );

   org_down_mvb_split_in      <= org_dma_down_mvb_deser
                              (
                               <<signal ^.uut.down_mvb_split_in_data    : std_logic_vector(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mvb_split_in_vld     : std_logic_vector(MVB_DOWN_ITEMS                  -1 downto 0)>>,
                               <<signal ^.uut.down_mvb_split_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mvb_split_in_dst_rdy : std_logic>>
                              );

   org_down_mfb_split_in      <= org_down_mfb_deser
                              (
                               <<signal ^.uut.down_mfb_split_in_data    : std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_split_in_sof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_split_in_eof_pos : std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_split_in_sof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_split_in_eof     : std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_split_in_src_rdy : std_logic>>,
                               <<signal ^.uut.down_mfb_split_in_dst_rdy : std_logic>>
                              );

   org_down_mfb_trans_in      <= org_down_mfb_array_deser
                              (
                               <<signal ^.uut.down_mfb_trans_in_data    : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_trans_in_sof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_trans_in_eof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_trans_in_sof     : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_trans_in_eof     : slv_array_t     (DMA_PORTS-1 downto 0)(MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_trans_in_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_trans_in_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_down_mvb_asfifo_in      <= org_dma_down_mvb_array_deser
                              (
                               <<signal ^.uut.down_mvb_asfifo_in_data    : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mvb_asfifo_in_vld     : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS                  -1 downto 0)>>,
                               <<signal ^.uut.down_mvb_asfifo_in_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.down_mvb_asfifo_in_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_down_mfb_asfifo_in      <= org_dma_down_mfb_array_deser
                              (
                               <<signal ^.uut.down_mfb_asfifo_in_data    : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_asfifo_in_sof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_asfifo_in_eof_pos : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_asfifo_in_sof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_asfifo_in_eof     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_asfifo_in_src_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.down_mfb_asfifo_in_dst_rdy : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

   org_DOWN_MVB <= org_dma_down_mvb_array_deser
                              (
                               <<signal ^.uut.DOWN_MVB_DATA    : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MVB_VLD     : slv_array_t     (DMA_PORTS-1 downto 0)(MVB_DOWN_ITEMS-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MVB_SRC_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MVB_DST_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

   org_DOWN_MFB <= org_dma_down_mfb_array_deser
                              (
                               <<signal ^.uut.DOWN_MFB_DATA    : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MFB_SOF_POS : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MFB_EOF_POS : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MFB_SOF     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MFB_EOF     : slv_array_t     (DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MFB_SRC_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>,
                               <<signal ^.uut.DOWN_MFB_DST_RDY : std_logic_vector(DMA_PORTS-1 downto 0)>>
                              );

end architecture;
