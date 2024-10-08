-- mfb_frame_recorder.vhd: Record frames and send it via MI32
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MFB_FRAME_RECORDER is
   generic(
      REGIONS     : natural := 4;
      REGION_SIZE : natural := 8;
      BLOCK_SIZE  : natural := 8;
      ITEM_WIDTH  : natural := 8;
      FIFO_DEPTH  : natural := 512
   );
   port(
      -- CLOCK AND RESET
      CLK        : in  std_logic;
      RST        : in  std_logic;
      -- MI32 INTERFACE
      MI_DWR     : in  std_logic_vector(31 downto 0);
      MI_ADDR    : in  std_logic_vector(31 downto 0);
      MI_BE      : in  std_logic_vector(3 downto 0); -- Don't support yet!
      MI_RD      : in  std_logic;
      MI_WR      : in  std_logic;
      MI_ARDY    : out std_logic;
      MI_DRD     : out std_logic_vector(31 downto 0);
      MI_DRDY    : out std_logic;
      -- TX MFB INTERFACE
      RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY : in  std_logic;
      RX_DST_RDY : out std_logic
   );
end MFB_FRAME_RECORDER;

architecture FULL of MFB_FRAME_RECORDER is

   constant DATA_WIDTH       : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_WIDTH    : natural := REGIONS*max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH    : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant MI_DATA_ITEMS    : natural := DATA_WIDTH/32;
   constant MI_DRD_MUX_WIDTH : natural := log2(MI_DATA_ITEMS+5);

   type mfb_bus_t is record
      data    : std_logic_vector(DATA_WIDTH-1 downto 0);
      sof_pos : std_logic_vector(SOF_POS_WIDTH-1 downto 0);
      eof_pos : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
      sof     : std_logic_vector(REGIONS-1 downto 0);
      eof     : std_logic_vector(REGIONS-1 downto 0);
      src_rdy : std_logic;
      dst_rdy : std_logic;
   end record;

   signal s_fifo_in                 : mfb_bus_t;
   signal s_fifo_out                : mfb_bus_t;
   signal s_fifo_status             : std_logic_vector(log2(FIFO_DEPTH) downto 0);

   signal s_fifo2mi_flow_ctrl       : std_logic_vector(31 downto 0);
   signal s_fifo2mi_flow_ctrl_sel   : std_logic;

   signal s_drd_premuxed            : std_logic_vector((MI_DATA_ITEMS+5)*32-1 downto 0);
   signal s_drd_sel                 : std_logic_vector(MI_DRD_MUX_WIDTH-1 downto 0);
   signal s_drd_muxed               : std_logic_vector(31 downto 0);

   signal s_sreg                    : std_logic_vector(31 downto 0);

   signal s_creg                    : std_logic_vector(31 downto 0);
   signal s_creg_we                 : std_logic;
   signal s_creg_sel                : std_logic;

   signal s_creg_fifo_in_en         : std_logic;
   signal s_creg_fifo_out_force_en  : std_logic;

begin

   assert (DATA_WIDTH < 4097) report "Unsupported MFB configuration! The maximum allowed data width is 4096 bits! Now it is " & integer'image(DATA_WIDTH) & " bits." severity failure;
   assert (log2(FIFO_DEPTH) < 16) report "Unsupported FIFO depth! The maximum allowed FIFO depth is 32768 items! Now it is " & integer'image(FIFO_DEPTH) & " items." severity failure;

   -- --------------------------------------------------------------------------
   --  MI32 ADDRESS DECODER
   -- --------------------------------------------------------------------------

   MI_ARDY <= MI_RD or MI_WR;

   s_fifo2mi_flow_ctrl_sel <= '1' when (MI_ADDR(9 downto 2) = X"02") else '0';

   s_creg_sel <= '1' when (MI_ADDR(9 downto 2) = X"01") else '0';
   s_creg_we  <= s_creg_sel and MI_WR;

   s_fifo2mi_flow_ctrl(31 downto 2*REGIONS+1)      <= (others=>'0');
   s_fifo2mi_flow_ctrl(2*REGIONS downto REGIONS+1) <= s_fifo_out.sof;
   s_fifo2mi_flow_ctrl(REGIONS downto 1)           <= s_fifo_out.eof;
   s_fifo2mi_flow_ctrl(0)                          <= s_fifo_out.src_rdy;

   s_drd_premuxed(31 downto 0)    <= s_sreg;
   s_drd_premuxed(63 downto 32)   <= s_creg;
   s_drd_premuxed(95 downto 64)   <= s_fifo2mi_flow_ctrl;
   s_drd_premuxed(127 downto 96)  <= (96+SOF_POS_WIDTH-1 downto 96 => s_fifo_out.sof_pos, others => '0');
   s_drd_premuxed(159 downto 128) <= (128+EOF_POS_WIDTH-1 downto 128 => s_fifo_out.eof_pos, others => '0');

   s_drd_premuxed_g : for i in 0 to MI_DATA_ITEMS-1 generate
      s_drd_premuxed((i+5+1)*32-1 downto (i+5)*32) <= s_fifo_out.data((i+1)*32-1 downto i*32);
   end generate;

   s_drd_sel <= MI_ADDR(MI_DRD_MUX_WIDTH+2-1 downto 2);

   drd_mux_i : entity work.GEN_MUX
   generic map(
      DATA_WIDTH => 32,
      MUX_WIDTH  => MI_DATA_ITEMS+5
   )
   port map(
      DATA_IN  => s_drd_premuxed,
      SEL      => s_drd_sel,
      DATA_OUT => s_drd_muxed
   );

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         MI_DRD <= s_drd_muxed;
      end if;
   end process;

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            MI_DRDY <= '0';
         else
            MI_DRDY <= MI_RD;
         end if;
      end if;
   end process;

   -- --------------------------------------------------------------------------
   --  MI32 STATUS REGISTER (0x0000)
   -- --------------------------------------------------------------------------

   sreg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         s_sreg <= (others=>'0'); -- init value
         s_sreg(0) <= s_fifo_in.dst_rdy;
         s_sreg(1) <= s_fifo_out.src_rdy;
         s_sreg(2) <= RX_SRC_RDY;
         s_sreg(3) <= RX_DST_RDY;
         s_sreg(log2(FIFO_DEPTH)+8 downto 8) <= s_fifo_status;
         s_sreg(31 downto 24) <= std_logic_vector(to_unsigned(MI_DATA_ITEMS,8));
      end if;
   end process;

   -- --------------------------------------------------------------------------
   --  MI32 CONTROL REGISTER (0x0004)
   -- --------------------------------------------------------------------------

   creg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            s_creg <= (others=>'0');
         elsif (s_creg_we = '1') then
            s_creg <= MI_DWR;
         end if;
      end if;
   end process;

   s_creg_fifo_in_en        <= s_creg(0);
   s_creg_fifo_out_force_en <= s_creg(2);

   -- --------------------------------------------------------------------------
   --  MFB FIFO BRAM
   -- --------------------------------------------------------------------------

   mfb_fifo_bram_i : entity work.MFB_FIFO_BRAM
   generic map (
      REGIONS      => REGIONS,
      REGION_SIZE  => REGION_SIZE,
      BLOCK_SIZE   => BLOCK_SIZE,
      ITEM_WIDTH   => ITEM_WIDTH,
      FIFO_DEPTH   => FIFO_DEPTH
   )
   port map (
      CLK         => CLK,
      RST         => RST,
      -- RX
      RX_DATA     => s_fifo_in.data,
      RX_SOF_POS  => s_fifo_in.sof_pos,
      RX_EOF_POS  => s_fifo_in.eof_pos,
      RX_SOF      => s_fifo_in.sof,
      RX_EOF      => s_fifo_in.eof,
      RX_SRC_RDY  => s_fifo_in.src_rdy,
      RX_DST_RDY  => s_fifo_in.dst_rdy,
      -- TX
      TX_DATA     => s_fifo_out.data,
      TX_SOF_POS  => s_fifo_out.sof_pos,
      TX_EOF_POS  => s_fifo_out.eof_pos,
      TX_SOF      => s_fifo_out.sof,
      TX_EOF      => s_fifo_out.eof,
      TX_SRC_RDY  => s_fifo_out.src_rdy,
      TX_DST_RDY  => s_fifo_out.dst_rdy,
      -- STATUS
      FIFO_STATUS => s_fifo_status
   );

   s_fifo_out.dst_rdy <= s_creg_fifo_out_force_en or (s_fifo2mi_flow_ctrl_sel and MI_RD);

   -- --------------------------------------------------------------------------
   --  ASSIGNMENT
   -- --------------------------------------------------------------------------

   s_fifo_in.data    <= RX_DATA;
   s_fifo_in.sof_pos <= RX_SOF_POS;
   s_fifo_in.eof_pos <= RX_EOF_POS;
   s_fifo_in.sof     <= RX_SOF;
   s_fifo_in.eof     <= RX_EOF;
   s_fifo_in.src_rdy <= RX_SRC_RDY and s_creg_fifo_in_en;
   RX_DST_RDY        <= s_fifo_in.dst_rdy and s_creg_fifo_in_en;

end architecture;
