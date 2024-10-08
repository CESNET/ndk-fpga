-- mfb_frame_player.vhd: TODO
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MFB_FRAME_PLAYER is
   generic(
      REGIONS     : natural := 4;
      REGION_SIZE : natural := 8;
      BLOCK_SIZE  : natural := 8;
      ITEM_WIDTH  : natural := 8;
      FIFO_DEPTH  : natural := 512 -- maximum depth is 32768 items
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
      TX_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY : out std_logic;
      TX_DST_RDY : in  std_logic
   );
end MFB_FRAME_PLAYER;

architecture FULL of MFB_FRAME_PLAYER is

   constant DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant MI_DATA_ITEMS : natural := DATA_WIDTH/32;

   type mfb_bus_t is record
      data    : std_logic_vector(DATA_WIDTH-1 downto 0);
      sof_pos : std_logic_vector(SOF_POS_WIDTH-1 downto 0);
      eof_pos : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
      sof     : std_logic_vector(REGIONS-1 downto 0);
      eof     : std_logic_vector(REGIONS-1 downto 0);
      src_rdy : std_logic;
   end record;

   signal cnt : unsigned(log2(MI_DATA_ITEMS)-1 downto 0);

   signal s_mi2fifo                 : mfb_bus_t;
   signal s_fifo_in                 : mfb_bus_t;
   signal s_fifo_out                : mfb_bus_t;
   signal s_fifo_out_reg            : mfb_bus_t;

   signal s_fifo_in_src_rdy_en      : std_logic;
   signal s_fifo_in_dst_rdy         : std_logic;
   signal s_fifo_out_src_rdy_en     : std_logic;
   signal s_fifo_out_dst_rdy_en     : std_logic;
   signal s_fifo_out_reg_vld        : std_logic;

   signal s_fifo_status             : std_logic_vector(log2(FIFO_DEPTH) downto 0);

   signal s_mi2fifo_vld_reg_we      : std_logic;
   signal s_mi2fifo_vld_reg_sel     : std_logic;

   signal s_mi2fifo_sof_pos_reg_we  : std_logic;
   signal s_mi2fifo_sof_pos_reg_sel : std_logic;

   signal s_mi2fifo_eof_pos_reg_we  : std_logic;
   signal s_mi2fifo_eof_pos_reg_sel : std_logic;

   signal s_mi2fifo_data_reg_we     : std_logic;
   signal s_mi2fifo_data_reg_sel    : std_logic;

   signal s_sreg                    : std_logic_vector(31 downto 0);

   signal s_creg                    : std_logic_vector(31 downto 0);
   signal s_creg_we                 : std_logic;
   signal s_creg_sel                : std_logic;

   signal s_creg_fifo_in_en         : std_logic;
   signal s_creg_fifo_out_force_en  : std_logic;
   signal s_creg_fifo_out_en        : std_logic;
   signal s_creg_fifo_in_sel        : std_logic;

begin

   assert (DATA_WIDTH < 4097) report "Unsupported MFB configuration! The maximum allowed data width is 4096 bits! Now it is " & integer'image(DATA_WIDTH) & " bits." severity failure;
   assert (log2(FIFO_DEPTH) < 16) report "Unsupported FIFO depth! The maximum allowed FIFO depth is 32768 items! Now it is " & integer'image(FIFO_DEPTH) & " items." severity failure;

   -- --------------------------------------------------------------------------
   --  MI32 ADDRESS DECODER
   -- --------------------------------------------------------------------------

   MI_ARDY <= MI_RD or MI_WR;

   -- register select signals
   s_creg_sel <= '1' when (MI_ADDR(4 downto 0) = "00100") else '0';
   s_mi2fifo_vld_reg_sel     <= '1' when (MI_ADDR(4 downto 0) = "01000") else '0';
   s_mi2fifo_sof_pos_reg_sel <= '1' when (MI_ADDR(4 downto 0) = "01100") else '0';
   s_mi2fifo_eof_pos_reg_sel <= '1' when (MI_ADDR(4 downto 0) = "10000") else '0';

   -- register write enable signals
   s_creg_we <= s_creg_sel and MI_WR;
   s_mi2fifo_vld_reg_we     <= s_mi2fifo_vld_reg_sel and MI_WR;
   s_mi2fifo_sof_pos_reg_we <= s_mi2fifo_sof_pos_reg_sel and MI_WR;
   s_mi2fifo_eof_pos_reg_we <= s_mi2fifo_eof_pos_reg_sel and MI_WR;

   -- mi2fifo data register select and write enable signals
   -- s_mi2fifo_data_reg_sel_g : for i in 0 to MI_DATA_ITEMS-1 generate
      s_mi2fifo_data_reg_sel <= '1' when (MI_ADDR(4 downto 0) = "10100") else '0';
      s_mi2fifo_data_reg_we <= s_mi2fifo_data_reg_sel and MI_WR;
   -- end generate;

      process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (s_mi2fifo_data_reg_we = '1') then
               cnt <= cnt + 1;
            end if;
            if (RST = '1') or (s_mi2fifo_vld_reg_we = '1') then
               cnt <= (others => '0');
            end if;
         end if;
      end process;

   process (CLK)
   begin
      if (rising_edge(CLK)) then
         case(MI_ADDR(4 downto 0)) is
            when "00000" => --X"00"
               MI_DRD <= s_sreg;
            when "00100" => --X"04"
               MI_DRD <= s_creg;
            when others =>
               MI_DRD <= X"DEAAAAAD";
         end case;
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
         s_sreg(0) <= s_fifo_in_dst_rdy;
         s_sreg(1) <= s_fifo_out.src_rdy;
         s_sreg(2) <= TX_DST_RDY;
         s_sreg(3) <= s_fifo_out_reg.src_rdy;
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

   s_creg_fifo_in_en  <= s_creg(0);
   s_creg_fifo_out_en <= s_creg(1);
   s_creg_fifo_out_force_en <= s_creg(2);
   s_creg_fifo_in_sel <= s_creg(3);

   -- --------------------------------------------------------------------------
   --  MI2FIFO REGISTERS (write only, 0x0008+)
   -- --------------------------------------------------------------------------

   -- mi2fifo_vld_reg = 0x0008
   mi2fifo_vld_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         s_mi2fifo.src_rdy <= '0'; -- auto reset
         if (s_mi2fifo_vld_reg_we = '1') then
            s_mi2fifo.sof     <= MI_DWR(2*REGIONS downto REGIONS+1);
            s_mi2fifo.eof     <= MI_DWR(REGIONS downto 1);
            s_mi2fifo.src_rdy <= MI_DWR(0);
         end if;
      end if;
   end process;

   -- mi2fifo_sof_pos_reg = 0x000C
   mi2fifo_sof_pos_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (s_mi2fifo_sof_pos_reg_we = '1') then
            s_mi2fifo.sof_pos <= MI_DWR(SOF_POS_WIDTH-1 downto 0);
         end if;
      end if;
   end process;

   -- mi2fifo_eof_pos_reg = 0x0010
   mi2fifo_eof_pos_reg_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (s_mi2fifo_eof_pos_reg_we = '1') then
            s_mi2fifo.eof_pos <= MI_DWR(EOF_POS_WIDTH-1 downto 0);
         end if;
      end if;
   end process;

   -- mi2fifo_reg = 0x0014
   mi2fifo_reg_g : for i in 0 to MI_DATA_ITEMS-1 generate
      mi2fifo_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (cnt = i) then
               s_mi2fifo.data((i+1)*32-1 downto i*32) <= MI_DWR;
            end if;
         end if;
      end process;
   end generate;

   -- --------------------------------------------------------------------------
   --  FIFO INPUT
   -- --------------------------------------------------------------------------

   s_fifo_in.data     <= s_mi2fifo.data    when (s_creg_fifo_in_sel = '0') else s_fifo_out_reg.data;
   s_fifo_in.sof_pos  <= s_mi2fifo.sof_pos when (s_creg_fifo_in_sel = '0') else s_fifo_out_reg.sof_pos;
   s_fifo_in.eof_pos  <= s_mi2fifo.eof_pos when (s_creg_fifo_in_sel = '0') else s_fifo_out_reg.eof_pos;
   s_fifo_in.sof      <= s_mi2fifo.sof     when (s_creg_fifo_in_sel = '0') else s_fifo_out_reg.sof;
   s_fifo_in.eof      <= s_mi2fifo.eof     when (s_creg_fifo_in_sel = '0') else s_fifo_out_reg.eof;
   s_fifo_in.src_rdy  <= s_mi2fifo.src_rdy when (s_creg_fifo_in_sel = '0') else s_fifo_out_reg_vld;

   s_fifo_in_src_rdy_en <= s_fifo_in.src_rdy and s_creg_fifo_in_en;

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
      RX_SRC_RDY  => s_fifo_in_src_rdy_en,
      RX_DST_RDY  => s_fifo_in_dst_rdy,
      -- TX
      TX_DATA     => s_fifo_out.data,
      TX_SOF_POS  => s_fifo_out.sof_pos,
      TX_EOF_POS  => s_fifo_out.eof_pos,
      TX_SOF      => s_fifo_out.sof,
      TX_EOF      => s_fifo_out.eof,
      TX_SRC_RDY  => s_fifo_out.src_rdy,
      TX_DST_RDY  => s_fifo_out_dst_rdy_en,
      -- STATUS
      FIFO_STATUS => s_fifo_status
   );

   s_fifo_out_src_rdy_en <= s_fifo_out.src_rdy and s_creg_fifo_out_en and not s_creg_fifo_out_force_en;
   s_fifo_out_dst_rdy_en <= (s_creg_fifo_out_en and TX_DST_RDY) or s_creg_fifo_out_force_en;

   -- --------------------------------------------------------------------------
   --  FIFO OUTPUTS REGISTERS
   -- --------------------------------------------------------------------------

   fifo_out_reg_vld_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RST = '1') then
            s_fifo_out_reg.src_rdy <= '0';
         elsif (TX_DST_RDY = '1') then
            s_fifo_out_reg.src_rdy <= s_fifo_out_src_rdy_en;
         end if;
      end if;
   end process;

   fifo_out_regs_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (TX_DST_RDY = '1') then
            s_fifo_out_reg.data    <= s_fifo_out.data;
            s_fifo_out_reg.sof_pos <= s_fifo_out.sof_pos;
            s_fifo_out_reg.eof_pos <= s_fifo_out.eof_pos;
            s_fifo_out_reg.sof     <= s_fifo_out.sof;
            s_fifo_out_reg.eof     <= s_fifo_out.eof;
         end if;
      end if;
   end process;

   s_fifo_out_reg_vld <= TX_DST_RDY and s_fifo_out_reg.src_rdy;

   -- --------------------------------------------------------------------------
   --  ASSIGNMENT OF OUTPUTS PORTS
   -- --------------------------------------------------------------------------

   TX_DATA    <= s_fifo_out_reg.data;
   TX_SOF_POS <= s_fifo_out_reg.sof_pos;
   TX_EOF_POS <= s_fifo_out_reg.eof_pos;
   TX_SOF     <= s_fifo_out_reg.sof;
   TX_EOF     <= s_fifo_out_reg.eof;
   TX_SRC_RDY <= s_fifo_out_reg.src_rdy;

end architecture;
