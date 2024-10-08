-- ptc_hdr_data_merge_dins.vhd: PTC header data merge - data insert
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PTC_HDR_DATA_MERGE_DINS is
   generic(
      -- =======================================================================
      -- MFB DATA BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MFB(2,1,8,32) for PCIe on UltraScale+
      MFB_REGIONS     : natural := 2;
      MFB_REGION_SIZE : natural := 1;
      MFB_BLOCK_SIZE  : natural := 8;
      MFB_ITEM_WIDTH  : natural := 32;
      -- =======================================================================
      -- MVB HEADER BUS CONFIGURATION:
      -- =======================================================================
      MVB_ITEM_WIDTH  : natural := 128;
      -- =======================================================================
      -- OTHER CONFIGURATION:
      -- =======================================================================
      -- Depth of MFB FIFO (payload data)
      MFB_FIFO_DEPTH  : natural := 32;
      DEVICE          : string  := "ULTRASCALE";
      ENDPOINT_TYPE   : string  := "H_TILE"
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK                 : in  std_logic;
      RESET               : in  std_logic;
      -- =======================================================================
      -- INPUT MVB HEADER INTERFACE
      -- =======================================================================
      RX_MVB_DATA         : in  std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
      RX_MVB_VLD          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    --RX_MVB_SRC_RDY      : in  std_logic; -- only RX_MFB_HDR_SRC_RDY is used
    --RX_MVB_DST_RDY      : out std_logic; -- only RX_MFB_HDR_DST_RDY is used
      -- =======================================================================
      -- INPUT MFB HEADER INTERFACE
      -- =======================================================================
      RX_MFB_HDR_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_MFB_HDR_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      RX_MFB_HDR_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      RX_MFB_HDR_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_HDR_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_HDR_BE       : in  std_logic_vector(MFB_REGIONS*8-1 downto 0);
      RX_MFB_HDR_PAYLOAD  : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_HDR_TYPE     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_HDR_SRC_RDY  : in  std_logic;
      RX_MFB_HDR_DST_RDY  : out std_logic;
      -- =======================================================================
      -- INPUT MFB DATA INTERFACE CONECTED DIRECTLY TO FIFO
      -- =======================================================================
      RX_MFB_DATA_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_MFB_DATA_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      RX_MFB_DATA_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      RX_MFB_DATA_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_DATA_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_DATA_SRC_RDY : in  std_logic;
      RX_MFB_DATA_DST_RDY : out std_logic;
      -- =======================================================================
      -- OUTPUT MVB HEADER INTERFACE
      -- =======================================================================
      TX_MVB_DATA         : out std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
      TX_MVB_VLD          : out std_logic_vector(MFB_REGIONS-1 downto 0);
    --TX_MVB_SRC_RDY      : out std_logic; -- only TX_MFB_SRC_RDY is used
    --TX_MVB_DST_RDY      : in  std_logic; -- only TX_MFB_DST_RDY is used
      -- =======================================================================
      -- OUTPUT MFB HEADER+DATA INTERFACE
      -- =======================================================================
      TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_SRC_RDY      : out std_logic;
      TX_MFB_DST_RDY      : in  std_logic;
      TX_MFB_BE           : out std_logic_vector(MFB_REGIONS*8-1 downto 0)
   );
end PTC_HDR_DATA_MERGE_DINS;

architecture FULL of PTC_HDR_DATA_MERGE_DINS is

   constant HDR_WIDTH               : natural := 128;
   constant MFB_REGION_WIDTH        : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
   constant MFB_DATA_WIDTH          : natural := MFB_REGIONS*MFB_REGION_WIDTH;
   constant MFB_EOF_POS_W           : natural := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
   constant MFB_HDR_ITEMS           : natural := MFB_DATA_WIDTH/HDR_WIDTH;
   constant MFB_REGION_HDR_ITEMS    : natural := MFB_REGION_WIDTH/HDR_WIDTH;
   constant MUX_SEL_WIDTH           : natural := max(1,log2(MFB_REGIONS));
   constant INTEL_DEVICE            : boolean := (DEVICE = "STRATIX10") or (DEVICE = "AGILEX");
   constant PTILE_RTILE_DEVICE      : boolean := (DEVICE = "STRATIX10" or DEVICE = "AGILEX") and (ENDPOINT_TYPE = "P_TILE" or ENDPOINT_TYPE = "R_TILE");

   signal s_rx_mfb_hdr_data         : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
   signal s_rx_mfb_hdr_sof_pos      : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
   signal s_rx_mfb_hdr_eof_pos      : std_logic_vector(MFB_REGIONS*MFB_EOF_POS_W-1 downto 0);
   signal s_rx_mfb_hdr_eof_pos_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_EOF_POS_W-1 downto 0);
   signal s_rx_mfb_hdr_sof          : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_rx_mfb_hdr_eof          : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_rx_mfb_hdr_be           : std_logic_vector(MFB_REGIONS*8-1 downto 0);
   signal s_rx_mfb_hdr_payload      : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_rx_mfb_hdr_type         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_rx_mfb_hdr_src_rdy      : std_logic;

   signal s_inc_pkt                 : std_logic_vector(MFB_REGIONS downto 0);
   signal s_rx_mfb_data_sof         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_rx_mfb_data_vld         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_rx_mfb_data_dst_rdy_n   : std_logic;

   signal s_rx_mfb_data_arr         : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
   signal s_rx_mfb_data_plus_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH+1 downto 0);
   signal s_rx_mfb_data_plus        : std_logic_vector(MFB_REGIONS*(MFB_REGION_WIDTH+2)-1 downto 0);

   signal s_fifo_mfb_data_plus      : std_logic_vector(MFB_REGIONS*(MFB_REGION_WIDTH+2)-1 downto 0);
   signal s_fifo_mfb_data_plus_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH+1 downto 0);
   signal s_fifo_mfb_data_arr       : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
   signal s_fifo_mfb_data           : std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
   signal s_fifo_mfb_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mfb_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mfb_data_vld       : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mfb_data_vld_n     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_fifo_mfb_data_dst_rdy   : std_logic_vector(MFB_REGIONS-1 downto 0);

   signal s_data_insert_start       : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_data_insert_end         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_eof_pos_96m             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_eof_pos_128m            : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_size_is_128         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_size_is_128_reg     : std_logic;
   signal s_hdr_only_region         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_data_insert_clr         : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_data_insert_continue    : std_logic_vector(MFB_REGIONS+1-1 downto 0);
   signal s_data_insert_en          : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_data_accept             : std_logic_vector(MFB_REGIONS-1 downto 0);

   signal s_data_mux_sel            : slv_array_t(MFB_REGIONS-1 downto 0)(MUX_SEL_WIDTH-1 downto 0);
   signal s_data_mux_dout           : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);

   signal s_r1_mvb_hdr              : std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
   signal s_r1_mvb_hdr_arr          : slv_array_t(MFB_REGIONS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
   signal s_r1_mfb_data             : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
   signal s_r1_mfb_eof_pos          : std_logic_vector(MFB_REGIONS*MFB_EOF_POS_W-1 downto 0);
   signal s_r1_mfb_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_r1_mfb_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_r1_mfb_be               : std_logic_vector(MFB_REGIONS*8-1 downto 0);
   signal s_r1_mfb_payload          : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_r1_mfb_type             : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_r1_mfb_src_rdy          : std_logic;

   signal s_data_shifted_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);
   signal s_data_shifted_over_arr   : slv_array_t(MFB_REGIONS downto 0)(HDR_WIDTH-1 downto 0);
   signal s_data_shifted_over_reg   : std_logic_vector(HDR_WIDTH-1 downto 0);
   signal s_shift_4_dwords          : std_logic_vector(MFB_REGIONS downto 0);
   signal s_shift_4_dwords_reg      : std_logic;

   signal s_data_shifted            : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
   signal s_tx_mfb_data_muxed_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(MFB_REGION_WIDTH-1 downto 0);

begin

   assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
      report "PTC_HDR_DATA_MERGE_DINS: unsupported device!" severity failure;

   -----------------------------------------------------------------------------
   -- MFB DATA REGION VALID FLAGS
   -----------------------------------------------------------------------------

   incomplete_pkt_g : for r in 0 to MFB_REGIONS-1 generate
      s_inc_pkt(r+1) <= (RX_MFB_DATA_SOF(r) and not RX_MFB_DATA_EOF(r) and not s_inc_pkt(r)) or
                        (RX_MFB_DATA_SOF(r) and RX_MFB_DATA_EOF(r) and s_inc_pkt(r)) or
                        (not RX_MFB_DATA_SOF(r) and not RX_MFB_DATA_EOF(r) and s_inc_pkt(r));
   end generate;

   incomplete_pkt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_inc_pkt(0) <= '0';
         elsif (RX_MFB_DATA_DST_RDY = '1' and RX_MFB_DATA_SRC_RDY = '1') then
            s_inc_pkt(0) <= s_inc_pkt(MFB_REGIONS);
         end if;
      end if;
   end process;

   rx_valid_g : for r in 0 to MFB_REGIONS-1 generate
      s_rx_mfb_data_sof(r) <= RX_MFB_DATA_SRC_RDY and RX_MFB_DATA_SOF(r);
      s_rx_mfb_data_vld(r) <= RX_MFB_DATA_SRC_RDY and (RX_MFB_DATA_SOF(r) or RX_MFB_DATA_EOF(r) or s_inc_pkt(r));
   end generate;

   -----------------------------------------------------------------------------
   -- MFB DATA FIFOX MULTI
   -----------------------------------------------------------------------------

   s_rx_mfb_data_arr <= slv_array_downto_deser(RX_MFB_DATA_DATA,MFB_REGIONS,MFB_REGION_WIDTH);

   data_plus_arr_g : for r in 0 to MFB_REGIONS-1 generate
      s_rx_mfb_data_plus_arr(r) <= s_rx_mfb_data_arr(r) & RX_MFB_DATA_SOF(r) & RX_MFB_DATA_EOF(r);
   end generate;

   s_rx_mfb_data_plus <= slv_array_ser(s_rx_mfb_data_plus_arr,MFB_REGIONS,MFB_REGION_WIDTH+2);

   data_fifoxm_i : entity work.FIFOX_MULTI
   generic map(
      DATA_WIDTH          => MFB_REGION_WIDTH+2,
      ITEMS               => MFB_REGIONS*MFB_FIFO_DEPTH,
      WRITE_PORTS         => MFB_REGIONS,
      READ_PORTS          => MFB_REGIONS,
      RAM_TYPE            => "AUTO",
      DEVICE              => DEVICE,
      SAFE_READ_MODE      => false,
      ALMOST_FULL_OFFSET  => 1,
      ALMOST_EMPTY_OFFSET => 1
   )
   port map(
      CLK    => CLK,
      RESET  => RESET,

      DI     => s_rx_mfb_data_plus,
      WR     => s_rx_mfb_data_vld,
      FULL   => s_rx_mfb_data_dst_rdy_n,
      AFULL  => open,

      DO     => s_fifo_mfb_data_plus,
      RD     => s_fifo_mfb_data_dst_rdy,
      EMPTY  => s_fifo_mfb_data_vld_n,
      AEMPTY => open
   );

   RX_MFB_DATA_DST_RDY <= not s_rx_mfb_data_dst_rdy_n;
   s_fifo_mfb_data_vld <= not s_fifo_mfb_data_vld_n;

   s_fifo_mfb_data_dst_rdy <= s_data_accept and TX_MFB_DST_RDY and s_rx_mfb_hdr_src_rdy;
   s_fifo_mfb_data_plus_arr <= slv_array_downto_deser(s_fifo_mfb_data_plus,MFB_REGIONS,MFB_REGION_WIDTH+2);

   fifo_data_plus_arr_g : for r in 0 to MFB_REGIONS-1 generate
      s_fifo_mfb_data_arr(r) <= s_fifo_mfb_data_plus_arr(r)(MFB_REGION_WIDTH+2-1 downto 2);
      s_fifo_mfb_sof(r)      <= s_fifo_mfb_data_plus_arr(r)(1);
      s_fifo_mfb_eof(r)      <= s_fifo_mfb_data_plus_arr(r)(0);
   end generate;

   s_fifo_mfb_data <= slv_array_ser(s_fifo_mfb_data_arr,MFB_REGIONS,MFB_REGION_WIDTH);

   -----------------------------------------------------------------------------
   -- MFB HDR INPUT
   -----------------------------------------------------------------------------

   -- the DINS module must always be ready, the DINS cannot stop the data flow!
   RX_MFB_HDR_DST_RDY <= TX_MFB_DST_RDY;

   -- input MFB header signals
   s_rx_mfb_hdr_data    <= RX_MFB_HDR_DATA;
   s_rx_mfb_hdr_sof_pos <= RX_MFB_HDR_SOF_POS;
   s_rx_mfb_hdr_eof_pos <= RX_MFB_HDR_EOF_POS;
   s_rx_mfb_hdr_sof     <= RX_MFB_HDR_SOF;
   s_rx_mfb_hdr_eof     <= RX_MFB_HDR_EOF;
   s_rx_mfb_hdr_be      <= RX_MFB_HDR_BE;
   s_rx_mfb_hdr_payload <= RX_MFB_HDR_PAYLOAD;
   s_rx_mfb_hdr_type    <= RX_MFB_HDR_TYPE when (INTEL_DEVICE) else (others => '1');
   s_rx_mfb_hdr_src_rdy <= RX_MFB_HDR_SRC_RDY;

   -- create header array from s_rx_mfb_hdr_data
   s_rx_mfb_hdr_eof_pos_arr <= slv_array_deser(s_rx_mfb_hdr_eof_pos,MFB_REGIONS,MFB_EOF_POS_W);

   -----------------------------------------------------------------------------
   -- DATA INSERT CONTROL LOGIC
   -----------------------------------------------------------------------------

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1' and s_rx_mfb_hdr_src_rdy = '1') then
            s_hdr_size_is_128_reg <= s_hdr_size_is_128(MFB_REGIONS-1);
            s_data_insert_continue(0) <= s_data_insert_continue(MFB_REGIONS);
         end if;
         if (RESET = '1') then
            s_data_insert_continue(0) <= '0';
         end if;
      end if;
   end process;

   s_hdr_size_is_128(0) <= s_rx_mfb_hdr_type(0) when (s_rx_mfb_hdr_sof(0) = '1') else s_hdr_size_is_128_reg;
   hdr_size_is_128_g : for r in 1 to MFB_REGIONS-1 generate
      s_hdr_size_is_128(r) <= s_rx_mfb_hdr_type(r) when (s_rx_mfb_hdr_sof(r) = '1') else s_hdr_size_is_128(r-1);
   end generate;

   data_insert_g : for r in 0 to MFB_REGIONS-1 generate
      -- start inserting data when is SOF for data transaction on the bus
      s_data_insert_start(r) <= s_rx_mfb_hdr_sof(r) and s_rx_mfb_hdr_payload(r);

      -- flag of end of data inserting
      s_data_insert_end(r) <= s_rx_mfb_hdr_eof(r);

      -- detection last region with header only
      s_eof_pos_96m(r)  <= '1' when (unsigned(s_rx_mfb_hdr_eof_pos_arr(r)) <= 2) else '0';
      s_eof_pos_128m(r) <= '1' when (unsigned(s_rx_mfb_hdr_eof_pos_arr(r)) <= 3) else '0';
      s_hdr_only_region(r) <= s_eof_pos_128m(r) when (s_hdr_size_is_128(r) = '1') else s_eof_pos_96m(r);

      data_insert_clr_g : if (PTILE_RTILE_DEVICE) generate
         s_data_insert_clr(r) <= '0';
      else generate
         s_data_insert_clr(r) <= s_rx_mfb_hdr_eof(r) and s_hdr_only_region(r);
      end generate;

      -- flag of enabled data inserting
      s_data_insert_en(r) <= s_data_insert_start(r) or (s_data_insert_continue(r) and not s_data_insert_clr(r));

      s_data_insert_continue(r+1) <= '0' when (s_data_insert_end(r) = '1')   else
                                     '1' when (s_data_insert_start(r) = '1') else
                                     s_data_insert_continue(r);
   end generate;

   -- accepted data in FIFO_MULTI order
   data_accept_p : process (s_data_insert_en)
      variable var_cnt    : integer range 0 to MFB_REGIONS;
      variable var_accept : std_logic_vector(MFB_REGIONS-1 downto 0);
   begin
      var_accept := (others => '0');
      var_cnt := 0;
      temp_or : for r in 0 to MFB_REGIONS-1 loop
         if (s_data_insert_en(r) = '1') then
            var_accept(var_cnt) := '1';
            var_cnt := var_cnt + 1;
         end if;
      end loop;
      s_data_accept <= var_accept;
   end process;

   -----------------------------------------------------------------------------
   -- DATA MULTIPLEXORS
   -----------------------------------------------------------------------------

   -- create selection signals for data multiplexors
   s_data_mux_sel(0) <= (others => '0');
   mux_sel_g : for r in 1 to MFB_REGIONS-1 generate
      s_data_mux_sel(r) <= std_logic_vector(unsigned(s_data_mux_sel(r-1)) + 1) when (s_data_insert_en(r-1) = '1') else s_data_mux_sel(r-1);
   end generate;

   data_mux_g : for r in 0 to MFB_REGIONS-1 generate
      data_mux_i : entity work.GEN_MUX
      generic map(
         DATA_WIDTH => MFB_REGION_WIDTH,
         MUX_WIDTH  => MFB_REGIONS
      )
      port map(
         DATA_IN  => s_fifo_mfb_data,
         SEL      => s_data_mux_sel(r),
         DATA_OUT => s_data_mux_dout(r)
      );
   end generate;

   -----------------------------------------------------------------------------
   -- REGISTERS AFTER DATA INSERT
   -----------------------------------------------------------------------------

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1') then
            s_r1_mvb_hdr     <= RX_MVB_DATA;
            s_r1_mfb_data    <= s_data_mux_dout;
            s_r1_mfb_eof_pos <= s_rx_mfb_hdr_eof_pos;
            s_r1_mfb_sof     <= s_rx_mfb_hdr_sof;
            s_r1_mfb_eof     <= s_rx_mfb_hdr_eof;
            s_r1_mfb_be      <= s_rx_mfb_hdr_be;
            s_r1_mfb_payload <= s_rx_mfb_hdr_payload;
            s_r1_mfb_type    <= s_rx_mfb_hdr_type;
            s_r1_mfb_src_rdy <= s_rx_mfb_hdr_src_rdy;
         end if;
         if (RESET = '1') then
            s_r1_mfb_src_rdy <= '0';
         end if;
      end if;
   end process;

   s_r1_mvb_hdr_arr <= slv_array_deser(s_r1_mvb_hdr,MFB_REGIONS,MVB_ITEM_WIDTH);

   -----------------------------------------------------------------------------
   -- DATA SHIFT DUE TO HDR INSERTION
   -----------------------------------------------------------------------------

   -- registers for data left after shifting
   data_muxed_over_arr_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1') then
            s_data_shifted_over_reg <= s_data_shifted_over_arr(MFB_REGIONS);
            s_shift_4_dwords_reg <= s_shift_4_dwords(MFB_REGIONS);
         end if;
      end if;
   end process;

   s_data_shifted_over_arr(0) <= s_data_shifted_over_reg;
   -- overwrite data shift of the new word begins with a new SOF
   s_shift_4_dwords(0) <= s_shift_4_dwords_reg when (s_r1_mfb_sof(0) = '0') else s_r1_mfb_type(0);

   data_shift_g : for r in 0 to MFB_REGIONS-1 generate
      xilinx_data_shift_g : if (not INTEL_DEVICE) generate
         -- shift data by constant value (HDR_WIDTH)
         s_data_shifted_arr(r)(HDR_WIDTH-1 downto 0) <= s_data_shifted_over_arr(r);
         s_data_shifted_arr(r)(MFB_REGION_WIDTH-1 downto HDR_WIDTH) <= s_r1_mfb_data(r)(MFB_REGION_WIDTH-HDR_WIDTH-1 downto 0);
         s_data_shifted_over_arr(r+1) <= s_r1_mfb_data(r)(MFB_REGION_WIDTH-1 downto MFB_REGION_WIDTH-HDR_WIDTH);
      end generate;

      intel_data_shift_g : if (PTILE_RTILE_DEVICE) generate
         -- no data shift with P-TILE devices
         s_data_shifted_arr(r) <= s_r1_mfb_data(r);
         s_data_shifted_over_arr(r+1) <= (others => '0');
         s_shift_4_dwords(r+1) <= '0';
      elsif (DEVICE="STRATIX10" and not PTILE_RTILE_DEVICE) generate
         -- shift data by variable value (by 4 dwords (for 128-bit header) or 3 dwords (for 96-bit header))
         s_data_shifted_arr(r)(HDR_WIDTH-1 downto 0) <= s_data_shifted_over_arr(r)
            when (s_shift_4_dwords(r)='1') else s_r1_mfb_data(r)(32-1 downto 0) & s_data_shifted_over_arr(r)(3*32-1 downto 0);

         s_data_shifted_arr(r)(MFB_REGION_WIDTH-1 downto HDR_WIDTH) <= s_r1_mfb_data(r)(MFB_REGION_WIDTH-HDR_WIDTH-1 downto 0)
            when (s_shift_4_dwords(r)='1') else s_r1_mfb_data(r)(MFB_REGION_WIDTH-3*32-1 downto 32);

         s_data_shifted_over_arr(r+1) <= s_r1_mfb_data(r)(MFB_REGION_WIDTH-1 downto MFB_REGION_WIDTH-HDR_WIDTH)
            when (s_shift_4_dwords(r)='1') else (32-1 downto 0 => '0') & s_r1_mfb_data(r)(MFB_REGION_WIDTH-1 downto MFB_REGION_WIDTH-3*32);

         s_shift_4_dwords(r+1) <= s_shift_4_dwords(r) when s_r1_mfb_sof(r)='0' else s_r1_mfb_type(r);
      end generate;
   end generate;

   -----------------------------------------------------------------------------
   -- HDR INSERT MULTIPLEXORS
   -----------------------------------------------------------------------------

   hdr_mux_en_g: if (PTILE_RTILE_DEVICE) generate
      -- no HDR insert on P-TILE devices
      s_tx_mfb_data_muxed_arr <= s_data_shifted_arr;
   else generate

      hdr_mux_g : for r in 0 to MFB_REGIONS-1 generate
         -- insert 96b or 128b HDR to data stream
         process (all)
         begin
            s_tx_mfb_data_muxed_arr(r) <= s_data_shifted_arr(r);
            if (s_r1_mfb_sof(r) = '1') then
               if (DEVICE = "STRATIX10" and s_r1_mfb_type(r) = '0') then
                  s_tx_mfb_data_muxed_arr(r)(96-1 downto 0) <= s_r1_mvb_hdr_arr(r)(96-1 downto 0);
               else
                  s_tx_mfb_data_muxed_arr(r)(HDR_WIDTH-1 downto 0) <= s_r1_mvb_hdr_arr(r);
               end if;
            end if;
         end process;
      end generate;
   end generate;

   -----------------------------------------------------------------------------
   -- OUTPUT REGISTERS
   -----------------------------------------------------------------------------

   tx_mfb_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_MFB_DST_RDY = '1') then
            TX_MVB_DATA    <= s_r1_mvb_hdr;
            TX_MVB_VLD     <= s_r1_mfb_sof and s_r1_mfb_src_rdy;
            TX_MFB_DATA    <= slv_array_ser(s_tx_mfb_data_muxed_arr,MFB_REGIONS,MFB_REGION_WIDTH);
            TX_MFB_SOF_POS <= (others => '0');
            TX_MFB_EOF_POS <= s_r1_mfb_eof_pos;
            TX_MFB_SOF     <= s_r1_mfb_sof;
            TX_MFB_EOF     <= s_r1_mfb_eof;
            TX_MFB_BE      <= s_r1_mfb_be;
            TX_MFB_SRC_RDY <= s_r1_mfb_src_rdy;
         end if;
         if (RESET = '1') then
            TX_MFB_SRC_RDY <= '0';
         end if;
      end if;
   end process;

end architecture;
