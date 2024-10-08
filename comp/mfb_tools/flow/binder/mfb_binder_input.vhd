-- mfb_binder_input.vhd: Binder for multi MFB merging
-- Copyright (C) 2018 CESNET
-- Author(s): Michal Suchanek <xsucha12@stud.feec.vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_BINDER_INPUT is
   generic(
      -- Number of regions of output MFB bus, for input MFB bus is REGIONS = 1.
      REGIONS           : integer := 4;
      -- MFB parameters common for input and output buses.
      REGION_SIZE       : integer := 8;
      BLOCK_SIZE        : integer := 8;
      ITEM_WIDTH        : integer := 8;
      META_WIDTH        : integer := 8;
      -- Others parameters
      FIFO_RAM_TYPE     : string  := "AUTO";
      FIFO_DEPTH        : integer := 512/REGIONS;
      FIFO_AFULL_OFFSET : integer := 1;
      DEVICE            : string  := "ULTRASCALE"
   );
   port(
      -- CLOCK AND RESET
      CLK                 : in  std_logic;
      RST                 : in  std_logic;
      -- RX MULTI MFB INTERFACE
      RX_DATA             : in  std_logic_vector(REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_META             : in  std_logic_vector(META_WIDTH-1 downto 0);
      RX_SOF_POS          : in  std_logic_vector(max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS          : in  std_logic_vector(max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF              : in  std_logic;
      RX_EOF              : in  std_logic;
      RX_SRC_RDY          : in  std_logic;
      RX_DST_RDY          : out std_logic;
      RX_FIFO_AFULL       : out std_logic;
      -- TX MFB INTERFACE
      TX_DATA             : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_META             : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS          : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS          : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF              : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF              : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY          : out std_logic;
      TX_DST_RDY          : in  std_logic;
      -- FRAME STATE
      -- In this word continues the previously unfinished frame.
      TX_ONGOING_FRAME    : out std_logic;
      -- Last frame in this word is unfinished.
      TX_UNFINISHED_FRAME : out std_logic
   );
end MFB_BINDER_INPUT;

architecture behavioral of MFB_BINDER_INPUT is

   constant REGION_WIDTH   : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_WIDTH  : natural := max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH  : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant RX_MFB_WIDTH   : natural := REGION_WIDTH+META_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+2;
   constant FIFO_WIDTH     : natural := REGIONS*RX_MFB_WIDTH;
   constant BLOCK_SIZE_GND : std_logic_vector(log2(BLOCK_SIZE)-1 downto 0) := (others => '0');

   signal s_sof_pos_block     : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
   signal s_rx_shared_word    : std_logic;
   signal s_correct_end_comb  : std_logic;
   signal s_correct_end_reg   : std_logic;

   -- MFB COUTNER
   signal s_region_cnt        : unsigned(log2(REGIONS)-1 downto 0);
   signal s_region_cnt_zero   : std_logic;

   -- IDLE COUNTER
   signal s_idle_cnt          : unsigned(2 downto 0);
   signal s_idle_cnt_ce       : std_logic;
   signal s_idle_cnt_rst      : std_logic;
   signal s_idle_cnt_max      : std_logic;

   signal s_force_write_ready : std_logic;
   signal s_force_write       : std_logic;
   signal s_write             : std_logic;
   signal s_write_demuxed     : std_logic_vector(REGIONS-1 downto 0);

   signal s_rx_sof_masked     : std_logic;
   signal s_rx_eof_masked     : std_logic;
   signal s_rx_din            : std_logic_vector(RX_MFB_WIDTH-1 downto 0);
   signal s_din_reg_en        : std_logic_vector(REGIONS-1 downto 0);
   signal s_din_reg           : slv_array_t(REGIONS-1 downto 0)(RX_MFB_WIDTH-1 downto 0);

   -- FIFO
   signal s_fifo_din          : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal s_fifo_wr           : std_logic;
   signal s_fifo_full         : std_logic;
   signal s_fifo_afull        : std_logic;
   signal s_fifo_dout         : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal s_fifo_dout_arr     : slv_array_t(REGIONS-1 downto 0)(RX_MFB_WIDTH-1 downto 0);
   signal s_fifo_rd           : std_logic;
   signal s_fifo_vld          : std_logic;
   signal s_fifo_empty        : std_logic;
   signal s_fifo_status       : std_logic_vector(log2(FIFO_DEPTH) downto 0);

   -- TX
   signal s_mfb_fifo_data     : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
   signal s_mfb_fifo_meta     : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
   signal s_mfb_fifo_sof_pos  : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
   signal s_mfb_fifo_eof_pos  : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal s_mfb_fifo_sof      : std_logic_vector(REGIONS-1 downto 0);
   signal s_mfb_fifo_eof      : std_logic_vector(REGIONS-1 downto 0);

   -- FRAME STATUS
   signal s_inc_frame         : std_logic_vector(REGIONS downto 0);

begin

   s_sof_pos_block <= RX_SOF_POS & BLOCK_SIZE_GND;
   -- Checks if shared word is present
   s_rx_shared_word <= '1' when unsigned(s_sof_pos_block) > unsigned(RX_EOF_POS) else '0';

   -- --------------------------------------------------------------------------
   -- CORRECT END LOGIC
   -- --------------------------------------------------------------------------
   -- Checks if frame is ended correctly. Used in forced end.
   s_correct_end_comb <= (RX_EOF and not RX_SOF) or (RX_EOF and RX_SOF and not s_rx_shared_word);

   correct_end_reg : process (CLK)
   begin
     if rising_edge(CLK) then
        if (RST = '1') then
            s_correct_end_reg <= '0';
        elsif (RX_SRC_RDY = '1' and RX_DST_RDY = '1') then
            s_correct_end_reg <= s_correct_end_comb;
        end if;
     end if;
   end process;

   -- --------------------------------------------------------------------------
   -- REGION COUNTER
   -- --------------------------------------------------------------------------
   -- Switches between TX regions
   region_cnt_p : process (CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1') then
            s_region_cnt <= (others => '0');
         elsif (s_write = '1') then
            if (s_region_cnt = REGIONS-1) then
               s_region_cnt <= (others => '0');
            else
               s_region_cnt <= s_region_cnt + 1;
            end if;
         end if;
      end if;
   end process;

   s_region_cnt_zero <= '1' when (s_region_cnt = 0) else '0';

   -- --------------------------------------------------------------------------
   -- IDLE COUNTER
   -- --------------------------------------------------------------------------
   -- Forces an end on current input after not recieving any frames
   -- for defined number of counts
   s_idle_cnt_ce  <= not RX_SRC_RDY and not s_fifo_full;
   s_idle_cnt_max <= '1' when (to_integer(s_idle_cnt) = 7) else '0';
   s_idle_cnt_rst <= not s_force_write_ready;

   process (CLK)
   begin
      if rising_edge(CLK) then
         if (RST = '1' or s_idle_cnt_rst = '1') then
            s_idle_cnt <= (others => '0');
         elsif (s_idle_cnt_ce = '1') then
            if (s_idle_cnt_max = '0') then
               s_idle_cnt <= s_idle_cnt + 1;
            end if;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   -- WRITE LOGIC
   -- --------------------------------------------------------------------------

   s_force_write_ready <= s_correct_end_reg and not s_region_cnt_zero and not RX_SRC_RDY;
   s_force_write <= s_force_write_ready and s_idle_cnt_max;

   s_write <= (RX_SRC_RDY or s_force_write) and not s_fifo_full;

   write_demuxed_p : process (s_region_cnt,s_write)
   begin
      s_write_demuxed <= (others => '0');
      s_write_demuxed(to_integer(s_region_cnt)) <= s_write;
   end process;

   -- --------------------------------------------------------------------------
   -- INPUT DATA REGISTERS
   -- --------------------------------------------------------------------------

   s_rx_sof_masked <= RX_SOF and not s_force_write;
   s_rx_eof_masked <= RX_EOF and not s_force_write;
   s_rx_din <= RX_DATA & RX_META & RX_SOF_POS & RX_EOF_POS & s_rx_sof_masked & s_rx_eof_masked;

   din_reg_on_g : if REGIONS > 1 generate
      din_reg_g : for i in 0 to REGIONS-2 generate
         s_din_reg_en(i) <= s_write_demuxed(i);
         din_reg_p : process (CLK)
         begin
            if rising_edge(CLK) then
               if (s_din_reg_en(i) = '1') then
                  s_din_reg(i) <= s_rx_din;
               end if;
            end if;
         end process;
      end generate;
   end generate;

   -- last register is fake, it is input word
   s_din_reg(REGIONS-1)    <= s_rx_din;
   s_din_reg_en(REGIONS-1) <= s_write_demuxed(REGIONS-1);

   -- --------------------------------------------------------------------------
   -- INPUT FIFOX
   -- --------------------------------------------------------------------------

   s_fifo_din <= slv_array_ser(s_din_reg,REGIONS,RX_MFB_WIDTH);
   s_fifo_wr  <= s_write_demuxed(REGIONS-1);

   fifox_i : entity work.FIFOX
   generic map(
      DATA_WIDTH          => FIFO_WIDTH,
      ITEMS               => FIFO_DEPTH,
      RAM_TYPE            => FIFO_RAM_TYPE,
      DEVICE              => DEVICE,
      ALMOST_FULL_OFFSET  => FIFO_AFULL_OFFSET,
      ALMOST_EMPTY_OFFSET => 1
   )
   port map(
      CLK    => CLK,
      RESET  => RST,
      --  WRITE INTERFACE
      DI     => s_fifo_din,
      WR     => s_fifo_wr,
      FULL   => s_fifo_full,
      AFULL  => s_fifo_afull,
      STATUS => s_fifo_status,
      --  READ INTERFACE
      DO     => s_fifo_dout,
      RD     => s_fifo_rd,
      EMPTY  => s_fifo_empty,
      AEMPTY => open
   );

   s_fifo_vld <= not s_fifo_empty;
   RX_DST_RDY <= not s_fifo_full;
   RX_FIFO_AFULL <= s_fifo_afull;

   s_fifo_rd <= s_fifo_vld and TX_DST_RDY;
   s_fifo_dout_arr <= slv_array_downto_deser(s_fifo_dout,REGIONS,RX_MFB_WIDTH);

   -- --------------------------------------------------------------------------
   -- OUTPUT SIGNALS
   -- --------------------------------------------------------------------------

   mfb_fifo_output_g : for r in 0 to REGIONS-1 generate
      s_mfb_fifo_eof(r)     <= s_fifo_dout_arr(r)(0);
      s_mfb_fifo_sof(r)     <= s_fifo_dout_arr(r)(1);
      s_mfb_fifo_eof_pos(r) <= s_fifo_dout_arr(r)(EOF_POS_WIDTH+2-1 downto 2);
      s_mfb_fifo_sof_pos(r) <= s_fifo_dout_arr(r)(SOF_POS_WIDTH+EOF_POS_WIDTH+2-1 downto EOF_POS_WIDTH+2);
      s_mfb_fifo_meta(r)    <= s_fifo_dout_arr(r)(META_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+2-1 downto SOF_POS_WIDTH+EOF_POS_WIDTH+2);
      s_mfb_fifo_data(r)    <= s_fifo_dout_arr(r)(RX_MFB_WIDTH-1 downto META_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+2);
   end generate;

   TX_EOF     <= s_mfb_fifo_eof;
   TX_SOF     <= s_mfb_fifo_sof;
   TX_EOF_POS <= slv_array_ser(s_mfb_fifo_eof_pos,REGIONS,EOF_POS_WIDTH);
   TX_SOF_POS <= slv_array_ser(s_mfb_fifo_sof_pos,REGIONS,SOF_POS_WIDTH);
   TX_META    <= slv_array_ser(s_mfb_fifo_meta,REGIONS,META_WIDTH);
   TX_DATA    <= slv_array_ser(s_mfb_fifo_data,REGIONS,REGION_WIDTH);
   TX_SRC_RDY <= s_fifo_vld;

   -- --------------------------------------------------------------------------
   -- FRAME STATE LOGIC
   -- --------------------------------------------------------------------------
   -- Checks present incomplete frames
   incomplete_frame_g : for r in 0 to REGIONS-1 generate
      s_inc_frame(r+1) <= (s_mfb_fifo_sof(r) and not s_mfb_fifo_eof(r) and not s_inc_frame(r)) or
                          (s_mfb_fifo_sof(r) and s_mfb_fifo_eof(r) and s_inc_frame(r)) or
                          (not s_mfb_fifo_sof(r) and not s_mfb_fifo_eof(r) and s_inc_frame(r));
   end generate;

   -- INCOMPLETE FRAME
   incomplete_frame_last_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            s_inc_frame(0) <= '0';
         elsif ((s_fifo_vld = '1') and (TX_DST_RDY = '1')) then
            s_inc_frame(0) <= s_inc_frame(REGIONS);
         end if;
      end if;
   end process;

   TX_ONGOING_FRAME    <= s_inc_frame(0);
   TX_UNFINISHED_FRAME <= s_inc_frame(REGIONS);

end architecture;
