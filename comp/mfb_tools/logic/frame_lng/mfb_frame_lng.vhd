-- mfb_frame_lng.vhd: MFB frame lenght counter
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_FRAME_LNG is
   generic(
      -- =======================================================================
      -- MFB CONFIGURATION:
      -- =======================================================================
      REGIONS        : natural := 4;
      REGION_SIZE    : natural := 8;
      BLOCK_SIZE     : natural := 8;
      ITEM_WIDTH     : natural := 8;
      META_WIDTH     : natural := 8;

      -- =======================================================================
      -- FRAME LENGHT CONFIGURATION:
      -- =======================================================================
      -- Minimum value of LNG_WIDTH is: log2(REGIONS*REGION_SIZE*BLOCK_SIZE+1)
      LNG_WIDTH      : natural := 14;
      REG_BITMAP     : std_logic_vector(2 downto 0) := "111";
      SATURATION     : boolean := False;
      -- "serial", "parallel"
      IMPLEMENTATION : string  := "parallel"
   );
      port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK         : in  std_logic;
      RESET       : in  std_logic;

      -- =======================================================================
      -- RX MFB INTERFACE
      -- =======================================================================
      RX_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META     : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
      RX_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY  : in  std_logic;
      RX_DST_RDY  : out std_logic;

      -- =======================================================================
      -- TX MFB INTERFACE
      -- =======================================================================
      TX_DATA      : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META      : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS   : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS   : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF       : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF       : out std_logic_vector(REGIONS-1 downto 0);
      -- Continue of frame from previous regions
      TX_COF       : out std_logic_vector(REGIONS-1 downto 0);
      -- TEMP frame length in items calculated to end of current region, valid when is SRC_RDY and not EOF
      TX_TEMP_LNG  : out std_logic_vector(REGIONS*LNG_WIDTH-1 downto 0);
      -- Frame length in items, valid when is SRC_RDY and EOF
      TX_FRAME_LNG : out std_logic_vector(REGIONS*LNG_WIDTH-1 downto 0);
      -- Frame length overflow flag, valid when is SRC_RDY and EOF, only in SATURATION mode
      TX_FRAME_OVF : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY   : out std_logic;
      TX_DST_RDY   : in  std_logic
   );
end MFB_FRAME_LNG;

architecture FULL of MFB_FRAME_LNG is

   constant REGION_COUNT_ITEMS : natural := REGION_SIZE*BLOCK_SIZE;
   constant DATA_WIDTH         : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_SIZE       : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_SIZE       : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant WORD_LNG_WIDTH     : natural := log2(REGIONS*REGION_COUNT_ITEMS+1);
   constant LNG_WIDTH_INT      : natural := tsel(SATURATION,(LNG_WIDTH+1),LNG_WIDTH);
   constant DOWN_ZEROS         : unsigned(max(1,log2(BLOCK_SIZE))-1 downto 0) := (others=>'0');
   constant UP_ZEROS           : std_logic_vector(LNG_WIDTH-1 downto EOF_POS_SIZE) := (others=>'0');

   type uns_array_t is array (natural range <>) of unsigned;

   signal s_reg0_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal s_reg0_meta        : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
   signal s_reg0_sof_pos     : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
   signal s_reg0_eof_pos     : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
   signal s_reg0_sof         : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg0_eof         : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg0_src_rdy     : std_logic;

   signal s_sof_pos_arr      : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
   signal s_sof_pos_uns      : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_eof_pos_arr      : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
   signal s_eof_lng          : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
   signal s_cnt_add_sof      : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
   signal s_cnt_add_wf       : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
   signal s_inc_frame        : std_logic_vector(REGIONS downto 0);

   signal s_reg1_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal s_reg1_meta        : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
   signal s_reg1_sof_pos     : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
   signal s_reg1_eof_pos     : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
   signal s_reg1_sof         : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_eof         : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg1_src_rdy     : std_logic;
   signal s_reg1_cnt_add_sof : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
   signal s_reg1_cnt_add_wf  : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
   signal s_reg1_eof_lng     : uns_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
   signal s_reg1_inc_frame   : std_logic_vector(REGIONS-1 downto 0);

   signal s_last_lng_cnt_reg : unsigned(LNG_WIDTH_INT-1 downto 0);
   signal s_cnt_no_sof_add   : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH_INT-1 downto 0);
   signal s_lng_cnt          : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH_INT-1 downto 0);
   signal s_lng_cnt_sat      : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);
   signal s_lng_cnt_sel      : std_logic_vector(REGIONS-1 downto 0);
   signal s_frame_lng_eof    : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH_INT-1 downto 0);
   signal s_frame_lng        : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH_INT-1 downto 0);
   signal s_frame_lng_sat    : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);
   signal s_frame_lng_ovf    : std_logic_vector(REGIONS-1 downto 0);

   signal s_reg2_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal s_reg2_meta        : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
   signal s_reg2_sof_pos     : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
   signal s_reg2_eof_pos     : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
   signal s_reg2_sof         : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg2_eof         : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg2_inc_frame   : std_logic_vector(REGIONS-1 downto 0);
   signal s_reg2_src_rdy     : std_logic;
   signal s_reg2_frame_lng   : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);
   signal s_reg2_temp_lng    : uns_array_t(REGIONS-1 downto 0)(LNG_WIDTH-1 downto 0);
   signal s_reg2_frame_ovf   : std_logic_vector(REGIONS-1 downto 0);

begin

   assert (LNG_WIDTH >= WORD_LNG_WIDTH)
      report "MFB_FRAME_LNG: Minimum value of LNG_WIDTH is: log2(REGIONS*REGION_SIZE*BLOCK_SIZE+1)!"
      severity failure;

   -- ==========================================================================
   -- 0. REGISTERS STAGE
   -- ==========================================================================

   reg0_g : if REG_BITMAP(0) generate
      reg0_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
               s_reg0_data    <= RX_DATA;
               s_reg0_meta    <= RX_META;
               s_reg0_sof_pos <= RX_SOF_POS;
               s_reg0_eof_pos <= RX_EOF_POS;
               s_reg0_sof     <= RX_SOF;
               s_reg0_eof     <= RX_EOF;
            end if;
         end if;
      end process;

      reg0_vld_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_reg0_src_rdy <= '0';
            elsif (TX_DST_RDY = '1') then
               s_reg0_src_rdy <= RX_SRC_RDY;
            end if;
         end if;
      end process;
   end generate;

   no_reg0_g : if not REG_BITMAP(0) generate
      s_reg0_data    <= RX_DATA;
      s_reg0_meta    <= RX_META;
      s_reg0_sof_pos <= RX_SOF_POS;
      s_reg0_eof_pos <= RX_EOF_POS;
      s_reg0_sof     <= RX_SOF;
      s_reg0_eof     <= RX_EOF;
      s_reg0_src_rdy <= RX_SRC_RDY;
   end generate;

   -- ==========================================================================
   -- 1. LOGIC STAGE
   -- ==========================================================================

   sof_pos_arr_g : for r in 0 to REGIONS-1 generate
      sof_pos_uns_g : if REGION_SIZE > 1 generate
         s_sof_pos_arr(r) <= s_reg0_sof_pos((r+1)*SOF_POS_SIZE-1 downto r*SOF_POS_SIZE);
         sof_pos_uns_down_zeros_g : if BLOCK_SIZE > 1 generate
            s_sof_pos_uns(r) <= unsigned(s_sof_pos_arr(r)) & DOWN_ZEROS;
         else generate
            s_sof_pos_uns(r) <= unsigned(s_sof_pos_arr(r));
         end generate;
      end generate;
      sof_pos_uns_rs1_g : if REGION_SIZE = 1 generate
         s_sof_pos_uns(r) <= (others => '0');
      end generate;
   end generate;

   pos_arr_g : for r in 0 to REGIONS-1 generate
      s_eof_pos_arr(r) <= s_reg0_eof_pos((r+1)*EOF_POS_SIZE-1 downto r*EOF_POS_SIZE);
      s_eof_lng(r)     <= resize(unsigned(s_eof_pos_arr(r)),EOF_POS_SIZE+1) + 1;

      s_cnt_add_sof(r) <= to_unsigned(REGION_COUNT_ITEMS,EOF_POS_SIZE+1) - s_sof_pos_uns(r);
      s_cnt_add_wf(r)  <= s_eof_lng(r) - s_sof_pos_uns(r);
   end generate;

   -- --------------------------------------------------------------------------
   --  FRAME STATE LOGIC
   -- --------------------------------------------------------------------------

   inc_frame_g : for r in 0 to REGIONS-1 generate
      s_inc_frame(r+1) <= (s_reg0_sof(r) and not s_reg0_eof(r) and not s_inc_frame(r)) or
                          (s_reg0_sof(r) and s_reg0_eof(r) and s_inc_frame(r)) or
                          (not s_reg0_sof(r) and not s_reg0_eof(r) and s_inc_frame(r));
   end generate;

   inc_frame_last_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_inc_frame(0) <= '0';
         elsif (s_reg0_src_rdy = '1' and TX_DST_RDY = '1') then
            s_inc_frame(0) <= s_inc_frame(REGIONS);
         end if;
      end if;
   end process;

   -- ==========================================================================
   -- 1. REGISTERS STAGE
   -- ==========================================================================

   reg1_g : if REG_BITMAP(1) generate
      reg1_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
               s_reg1_data        <= s_reg0_data;
               s_reg1_meta        <= s_reg0_meta;
               s_reg1_sof_pos     <= s_reg0_sof_pos;
               s_reg1_eof_pos     <= s_reg0_eof_pos;
               s_reg1_sof         <= s_reg0_sof;
               s_reg1_eof         <= s_reg0_eof;
               s_reg1_cnt_add_sof <= s_cnt_add_sof;
               s_reg1_cnt_add_wf  <= s_cnt_add_wf;
               s_reg1_eof_lng     <= s_eof_lng;
               s_reg1_inc_frame   <= s_inc_frame(REGIONS-1 downto 0);
            end if;
         end if;
      end process;

      reg1_vld_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_reg1_src_rdy <= '0';
            elsif (TX_DST_RDY = '1') then
               s_reg1_src_rdy <= s_reg0_src_rdy;
            end if;
         end if;
      end process;
   end generate;

   no_reg1_g : if not REG_BITMAP(1) generate
      s_reg1_data        <= s_reg0_data;
      s_reg1_meta        <= s_reg0_meta;
      s_reg1_sof_pos     <= s_reg0_sof_pos;
      s_reg1_eof_pos     <= s_reg0_eof_pos;
      s_reg1_sof         <= s_reg0_sof;
      s_reg1_eof         <= s_reg0_eof;
      s_reg1_src_rdy     <= s_reg0_src_rdy;
      s_reg1_cnt_add_sof <= s_cnt_add_sof;
      s_reg1_cnt_add_wf  <= s_cnt_add_wf;
      s_reg1_eof_lng     <= s_eof_lng;
      s_reg1_inc_frame   <= s_inc_frame(REGIONS-1 downto 0);
   end generate;

   -- ==========================================================================
   -- 2. LOGIC STAGE
   -- ==========================================================================

   -- last lenght register
   last_lng_cnt_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            s_last_lng_cnt_reg <= (others => '0');
         elsif (s_reg1_src_rdy = '1' and TX_DST_RDY = '1') then
            s_last_lng_cnt_reg <= resize(s_lng_cnt_sat(REGIONS-1),LNG_WIDTH_INT);
         end if;
      end if;
   end process;

   -- Serial implementation of lng_cnt logic
   serial_g : if IMPLEMENTATION = "serial" generate
      s_cnt_no_sof_add(0) <= s_last_lng_cnt_reg + REGION_COUNT_ITEMS;
      cnt_add_g : for r in 1 to REGIONS-1 generate
         s_cnt_no_sof_add(r) <= s_lng_cnt(r-1) + REGION_COUNT_ITEMS;
      end generate;

      lng_cnt_g : for r in 0 to REGIONS-1 generate
         s_lng_cnt(r) <= resize(s_reg1_cnt_add_sof(r),LNG_WIDTH_INT) when (s_reg1_sof(r) = '1') else s_cnt_no_sof_add(r);
      end generate;
   end generate;

   -- Parallel implementation of lng_cnt logic
   parallel_g : if IMPLEMENTATION = "parallel" generate
      lng_cnt_paraller_g : for r in 0 to REGIONS-1 generate
         s_lng_cnt_sel(r) <= (or s_reg1_sof(r downto 0));

         lng_logic_p : process (s_reg1_sof, s_reg1_cnt_add_sof, s_last_lng_cnt_reg, s_lng_cnt_sel)
            variable v_lng_cnt : unsigned(WORD_LNG_WIDTH-1 downto 0);
         begin
            v_lng_cnt := (others => '0');
            for i in 0 to r loop
               if (s_reg1_sof(i) = '1') then
                  v_lng_cnt := resize(s_reg1_cnt_add_sof(i),WORD_LNG_WIDTH);
               else
                  v_lng_cnt := v_lng_cnt + REGION_COUNT_ITEMS;
               end if;
            end loop;
            if (s_lng_cnt_sel(r) = '1') then
               s_lng_cnt(r) <= resize(v_lng_cnt,LNG_WIDTH_INT);
            else
               s_lng_cnt(r) <= s_last_lng_cnt_reg + v_lng_cnt;
            end if;
         end process;
      end generate;
   end generate;

   -- Frame lenght of bigger frames (no whoole frame in one word)
   s_frame_lng_eof(0) <= s_last_lng_cnt_reg + s_reg1_eof_lng(0);
   frame_lng_eof_g : for r in 1 to REGIONS-1 generate
      s_frame_lng_eof(r) <= s_lng_cnt(r-1) + s_reg1_eof_lng(r);
   end generate;

   -- Output frame lenght valid when is SRC_RDY and EOF
   frame_lng_g : for r in 0 to REGIONS-1 generate
      s_frame_lng(r) <= s_frame_lng_eof(r) when (s_reg1_inc_frame(r) = '1') else
                        resize(s_reg1_cnt_add_wf(r),LNG_WIDTH_INT);
   end generate;

   -- simple saturation logic
   sat_on_g: if SATURATION generate
      sat_g : for r in 0 to REGIONS-1 generate
         s_lng_cnt_sat(r)   <= (others => '1') when (s_lng_cnt(r)(LNG_WIDTH) = '1')   else s_lng_cnt(r)(LNG_WIDTH-1 downto 0);
         s_frame_lng_sat(r) <= (others => '1') when (s_frame_lng(r)(LNG_WIDTH) = '1') else s_frame_lng(r)(LNG_WIDTH-1 downto 0);
         s_frame_lng_ovf(r) <= s_frame_lng(r)(LNG_WIDTH);
      end generate;
   end generate;

   sat_off_g: if not SATURATION generate
      s_lng_cnt_sat   <= s_lng_cnt;
      s_frame_lng_sat <= s_frame_lng;
      s_frame_lng_ovf <= (others => '0');
   end generate;

   -- ==========================================================================
   -- 2. REGISTERS STAGE
   -- ==========================================================================

   reg2_g : if REG_BITMAP(2) generate
      reg2_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
               s_reg2_data        <= s_reg1_data;
               s_reg2_meta        <= s_reg1_meta;
               s_reg2_sof_pos     <= s_reg1_sof_pos;
               s_reg2_eof_pos     <= s_reg1_eof_pos;
               s_reg2_sof         <= s_reg1_sof;
               s_reg2_eof         <= s_reg1_eof;
               s_reg2_inc_frame   <= s_reg1_inc_frame;
               s_reg2_frame_lng   <= s_frame_lng_sat;
               s_reg2_temp_lng    <= s_lng_cnt_sat;
               s_reg2_frame_ovf   <= s_frame_lng_ovf;
            end if;
         end if;
      end process;

      reg2_vld_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_reg2_src_rdy <= '0';
            elsif (TX_DST_RDY = '1') then
               s_reg2_src_rdy <= s_reg1_src_rdy;
            end if;
         end if;
      end process;
   end generate;

   no_reg2_g : if not REG_BITMAP(2) generate
      s_reg2_data        <= s_reg1_data;
      s_reg2_meta        <= s_reg1_meta;
      s_reg2_sof_pos     <= s_reg1_sof_pos;
      s_reg2_eof_pos     <= s_reg1_eof_pos;
      s_reg2_sof         <= s_reg1_sof;
      s_reg2_eof         <= s_reg1_eof;
      s_reg2_inc_frame   <= s_reg1_inc_frame;
      s_reg2_frame_lng   <= s_frame_lng_sat;
      s_reg2_temp_lng    <= s_lng_cnt_sat;
      s_reg2_frame_ovf   <= s_frame_lng_ovf;
      s_reg2_src_rdy     <= s_reg1_src_rdy;
   end generate;

   -- ==========================================================================
   -- OUTPUTS ASSIGNMENT
   -- ==========================================================================

   RX_DST_RDY <= TX_DST_RDY;

   TX_DATA    <= s_reg2_data;
   TX_META    <= s_reg2_meta;
   TX_SOF_POS <= s_reg2_sof_pos;
   TX_EOF_POS <= s_reg2_eof_pos;
   TX_SOF     <= s_reg2_sof;
   TX_EOF     <= s_reg2_eof;
   TX_COF     <= s_reg2_inc_frame; -- In this region continue frame from previous regions
   TX_SRC_RDY <= s_reg2_src_rdy;

   lng_out_g : for r in 0 to REGIONS-1 generate
      TX_TEMP_LNG((r+1)*LNG_WIDTH-1 downto r*LNG_WIDTH)  <= std_logic_vector(s_reg2_temp_lng(r));
      TX_FRAME_LNG((r+1)*LNG_WIDTH-1 downto r*LNG_WIDTH) <= std_logic_vector(s_reg2_frame_lng(r));
   end generate;

   TX_FRAME_OVF <= s_reg2_frame_ovf;

end architecture;
