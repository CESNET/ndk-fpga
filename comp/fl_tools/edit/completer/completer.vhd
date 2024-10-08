-- completer.vhd: Completer unit for FlowMon
-- Copyright (C) 2007 CESNET
-- Author: Martin Louda <sandin@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- log2 function
use work.math_pack.all;
-- package with FL records
use work.fl_pkg.all;
-- package with LB records
use work.mi32_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity completer is
   generic(
      -- defines completed data size in bytes
      -- allowed values are: 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024
      DATA_SIZE   : integer := 128;
      -- width of data part of the word
      DATA_WIDTH  : integer := 32;
      -- width of address part of the word
      ADDR_WIDTH  : integer := 16;
      -- input fl bus data width
      FL_IN_WIDTH : integer := 32;
      -- first word alignment (address/data)
      -- address occupies upper bits of input word when ALIGN_OLD is set to
      -- true (see documentation)
      ALIGN_OLD   : boolean := false;
      -- erase (fill with zeroes) data from memory after reading it
      -- set to false for debugging purposes (see documentation)
      ERASE       : boolean := true
   );
   port(
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input interface - data & address
      IN_DATA        : in  std_logic_vector(FL_IN_WIDTH-1 downto 0);
      IN_REM         : in  std_logic_vector(log2(FL_IN_WIDTH/8)-1 downto 0);
      IN_SOF_N       : in  std_logic;
      IN_EOF_N       : in  std_logic;
      IN_SOP_N       : in  std_logic;
      IN_EOP_N       : in  std_logic;
      IN_SRC_RDY_N   : in  std_logic;
      IN_DST_RDY_N   : out std_logic;

      -- Output interface - sequenced data
      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_REM        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      OUT_SOF_N      : out std_logic;
      OUT_EOF_N      : out std_logic;
      OUT_SOP_N      : out std_logic;
      OUT_EOP_N      : out std_logic;
      OUT_SRC_RDY_N  : out std_logic;
      OUT_DST_RDY_N  : in  std_logic;

      -- SW memory interface
      MI             : inout t_mi32
   );
end entity completer;

-- ------------------------------------------------------------------------
--                        Architecture declaration
-- ------------------------------------------------------------------------
architecture full of completer is

   constant MEM_ADDR_WIDTH : integer := LOG2((DATA_SIZE*16)/DATA_WIDTH);
   constant BLK_ADDR_WIDTH : integer := MEM_ADDR_WIDTH - 1;
   constant CNT_IN_WIDTH   : integer := LOG2(DATA_WIDTH + ADDR_WIDTH) + 1;

   constant ZEROES      : std_logic_vector(BLK_ADDR_WIDTH-1 downto 0)
      := (others => '0');
   constant ONES        : std_logic_vector(BLK_ADDR_WIDTH-1 downto 0)
      := (others => '1');
   constant DATA_ZEROES : std_logic_vector(DATA_WIDTH-1 downto 0)
      := (others => '0');

   signal uh_mem_addr   : std_logic_vector(MEM_ADDR_WIDTH-1 downto 0);
   signal uh_addr       : std_logic_vector(BLK_ADDR_WIDTH-1 downto 0);
   signal uh_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal uh_wr         : std_logic;
   signal uh_rdy        : std_logic;

   signal sw_rd      : std_logic;
   signal sw_do      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sw_do_dv   : std_logic;
   signal sw_addr    : std_logic_vector(BLK_ADDR_WIDTH-1 downto 0);

   signal mem_rd     : std_logic;
   signal mem_addr   : std_logic_vector(MEM_ADDR_WIDTH-1 downto 0);
   signal mem_do     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mem_do_dv  : std_logic;
   signal sig_erase  : std_logic;

   signal wr_block   : std_logic := '0';
   signal rd_block   : std_logic := '0';
   signal wr_done    : std_logic := '0';
   signal rd_done    : std_logic := '0';

   -- write/read port control signals
   signal wr_0       : std_logic := '0';
   signal wr_1       : std_logic := '0';
   signal rd_0       : std_logic := '0';
   signal rd_1       : std_logic := '0';

   signal cnt_addr      : std_logic_vector(BLK_ADDR_WIDTH-1 downto 0);
   signal reg_cnt_addr  : std_logic_vector(BLK_ADDR_WIDTH-1 downto 0)
      := (others => '0');
   signal reg_cnt_start : std_logic;
   signal reg_cnt_stop  : std_logic;
   signal cnt_stop      : std_logic;

   -- SW control
   signal sw_read       : std_logic := '0';

   -- Input data register logic signals
   signal reg_data      : std_logic_vector(DATA_WIDTH+ADDR_WIDTH+FL_IN_WIDTH-1
      downto 0);
   signal cnt_input     : std_logic_vector(CNT_IN_WIDTH-1 downto 0) :=
      conv_std_logic_vector(FL_IN_WIDTH, CNT_IN_WIDTH);
   signal got_data      : std_logic := '0';
   signal sig_uh_data   : std_logic_vector(
      DATA_WIDTH+ADDR_WIDTH+2*FL_IN_WIDTH-1 downto 0);

   -- FSM states
   type fsm_states is (
      init, wr_1_rd_0, wr_0_rd_1, wr_1_wait, wr_0_wait, rd_1_wait,
      rd_0_wait
   );
   signal curr_state, next_state : fsm_states;

-- ------------------------------------------------------------------------
--                        Architecture body
-- ------------------------------------------------------------------------
begin

   assert (DATA_SIZE = 1) or (DATA_SIZE = 2) or (DATA_SIZE = 4)
      or (DATA_SIZE = 8) or (DATA_SIZE = 16) or (DATA_SIZE = 32)
      or (DATA_SIZE = 64) or (DATA_SIZE = 128) or (DATA_SIZE = 256)
      or (DATA_SIZE = 512) or (DATA_SIZE = 1024)
      report "COMPLETER: Unsupported DATA_SIZE generic."
      severity error;
   assert (DATA_SIZE*8 > DATA_WIDTH) or (DATA_SIZE*8 = DATA_WIDTH)
      report "COMPLETER: DATA_SIZE*8 must be equal or greater than DATA_WIDTH."
      severity error;
   assert (ADDR_WIDTH > BLK_ADDR_WIDTH) or (ADDR_WIDTH = BLK_ADDR_WIDTH)
      report "COMPLETER: ADDR_WIDTH too small - impossible to address whole memory."
      severity error;
   assert (FL_IN_WIDTH = 8) or (FL_IN_WIDTH = 16) or (FL_IN_WIDTH = 32)
      or (FL_IN_WIDTH = 64) or (FL_IN_WIDTH = 128)
      report "COMPLETER: Unsupported FL_IN_WIDTH."
      severity error;
   assert (DATA_WIDTH = 8) or (DATA_WIDTH = 16) or (DATA_WIDTH = 32)
      or (DATA_WIDTH = 64) or (DATA_WIDTH = 128) or (DATA_WIDTH = 256)
      report "COMPLETER: Unsupported DATA_WIDTH."
      severity error;
   assert (ADDR_WIDTH < FL_IN_WIDTH)
      report "COMPLETER: ADDR_WIDTH must be less than FL_IN_WIDTH."
      severity error;

   IN_DST_RDY_N   <= not uh_rdy;
   uh_rdy         <= (wr_0 or wr_1) and not sw_read;
   uh_wr          <= got_data and (wr_0 or wr_1);
   wr_done        <= not IN_SRC_RDY_N and not IN_EOF_N and uh_rdy;

   -- blockram port A address: HFE output write or sw read
   uh_mem_addrp: process(sw_read, wr_block, uh_addr, rd_block, sw_addr)
   begin
      if (sw_read = '0') then
         uh_mem_addr <= wr_block & uh_addr;
      else
         uh_mem_addr <= rd_block & sw_addr;
      end if;
   end process;

   GEN_ALIGN_NEW: if (ALIGN_OLD = false) generate

      -- blockram port A data
      uh_datap: process(cnt_input, IN_DATA, reg_data, got_data, sig_uh_data)
      begin
         sig_uh_data <= (others => '0');
         if (got_data = '0') then
            uh_data  <= (others => '0');
         else
            if (conv_integer(cnt_input) = FL_IN_WIDTH) then
               if (DATA_WIDTH + ADDR_WIDTH > FL_IN_WIDTH) then
                  uh_data <= (others => '0');
               else
                  uh_data <= IN_DATA(DATA_WIDTH+ADDR_WIDTH-1 downto ADDR_WIDTH);
               end if;
            else
               sig_uh_data(conv_integer(cnt_input)-ADDR_WIDTH-1 downto 0) <=
                  IN_DATA &
                  reg_data(conv_integer(cnt_input)-FL_IN_WIDTH-1 downto
                  ADDR_WIDTH);
--                uh_data <= sig_uh_data(DATA_WIDTH+ADDR_WIDTH-1 downto ADDR_WIDTH);
               uh_data <= sig_uh_data(DATA_WIDTH-1 downto 0);
            end if;
         end if;
      end process;

      -- decoded address
      uh_addrp: process(cnt_input, IN_DATA, reg_data, got_data)
      begin
         if (got_data = '0') then
            uh_addr <= (others => '0');
         else
            if (conv_integer(cnt_input) = FL_IN_WIDTH) then
               uh_addr <= IN_DATA(BLK_ADDR_WIDTH-1 downto 0);
            else
               uh_addr <= reg_data(BLK_ADDR_WIDTH-1 downto 0);
            end if;
         end if;
      end process;

   end generate;

   GEN_ALIGN_OLD: if (ALIGN_OLD = true) generate

      -- blockram port A data
      uh_datap: process(cnt_input, IN_DATA, reg_data, got_data, sig_uh_data)
      begin
         sig_uh_data <= (others => '0');
         if (got_data = '0') then
            uh_data  <= (others => '0');
         else
            if (conv_integer(cnt_input) = FL_IN_WIDTH) then
               if (DATA_WIDTH + ADDR_WIDTH > FL_IN_WIDTH) then
                  uh_data <= (others => '0');
               else
                  uh_data <= IN_DATA(DATA_WIDTH-1 downto 0);
               end if;
            else
               if (conv_integer(cnt_input) = 2*FL_IN_WIDTH) then
                  sig_uh_data(conv_integer(cnt_input)-ADDR_WIDTH-1 downto 0) <=
                     IN_DATA &
                     reg_data(FL_IN_WIDTH-ADDR_WIDTH-1 downto 0);
               else
                  sig_uh_data(conv_integer(cnt_input)-ADDR_WIDTH-1 downto 0) <=
                     IN_DATA &
                     reg_data(conv_integer(cnt_input)-FL_IN_WIDTH-1 downto
                     FL_IN_WIDTH) &
                     reg_data(FL_IN_WIDTH-ADDR_WIDTH-1 downto 0);
               end if;
--                sig_uh_data(conv_integer(cnt_input)-ADDR_WIDTH-1 downto 0) <=
--                   IN_DATA &
--                   reg_data(conv_integer(cnt_input)-FL_IN_WIDTH-1 downto
--                   FL_IN_WIDTH) &
--                   reg_data(conv_integer(cnt_input)-FL_IN_WIDTH-1 downto
--                   ADDR_WIDTH);
--                uh_data <= sig_uh_data(DATA_WIDTH+ADDR_WIDTH-1 downto ADDR_WIDTH);
               uh_data <= sig_uh_data(DATA_WIDTH-1 downto 0);
            end if;
         end if;
      end process;

      -- decoded address
      uh_addrp: process(cnt_input, IN_DATA, reg_data, got_data)
      begin
         if (got_data = '0') then
            uh_addr <= (others => '0');
         else
            if (conv_integer(cnt_input) = FL_IN_WIDTH) then
               uh_addr <= IN_DATA(FL_IN_WIDTH-ADDR_WIDTH+BLK_ADDR_WIDTH-1
                  downto FL_IN_WIDTH-ADDR_WIDTH);
            else
               uh_addr <= reg_data(FL_IN_WIDTH-ADDR_WIDTH+BLK_ADDR_WIDTH-1
                  downto FL_IN_WIDTH-ADDR_WIDTH);
            end if;
         end if;
      end process;

   end generate;

   -- ---------------------------------------------------------------------
   --                     Input data register logic
   -- ---------------------------------------------------------------------

   -- all data registered?
   got_datap: process(cnt_input, IN_SRC_RDY_N, uh_rdy)
   begin
      if (IN_SRC_RDY_N = '1' or uh_rdy = '0') then
         got_data <= '0';
      elsif (conv_integer(cnt_input) < ADDR_WIDTH+DATA_WIDTH) then
         got_data <= '0';
      else
         got_data <= '1';
      end if;
   end process;

   -- input data & address register
   reg_datap: process(CLK)
   begin
      if (CLK'event and CLk = '1') then
         if (IN_SRC_RDY_N = '0' and wr_done = '0') then
            reg_data <= (others => '0');
            reg_data(conv_integer(cnt_input)-1 downto
               conv_integer(cnt_input)-FL_IN_WIDTH) <= IN_DATA;
         end if;
      end if;
   end process;

   -- input data counter
   cnt_inputp: process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt_input <= conv_std_logic_vector(FL_IN_WIDTH, CNT_IN_WIDTH);
         elsif (IN_SRC_RDY_N = '0' and uh_rdy = '1') then
            if (conv_integer(cnt_input) < ADDR_WIDTH+DATA_WIDTH) then
               cnt_input <= cnt_input + FL_IN_WIDTH;
            else
               cnt_input <= conv_std_logic_vector(FL_IN_WIDTH, CNT_IN_WIDTH);
            end if;
         end if;
      end if;
   end process;

   -- ---------------------------------------------------------------------
   --                     Data memory block
   -- ---------------------------------------------------------------------

   DP_BMEM_I: entity work.dp_bmem
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      ITEMS          => DATA_SIZE*8*2/DATA_WIDTH,
      WRITE_MODE_A   => "READ_FIRST",
      WRITE_MODE_B   => "READ_FIRST"
   )
   port map(
      --
      CLKA        => CLK,
      PIPE_ENA    => '1',
      REA         => sw_rd,
      WEA         => uh_wr,
      ADDRA       => uh_mem_addr,
      DIA         => uh_data,
      DOA_DV      => sw_do_dv,
      DOA         => sw_do,
      --
      CLKB        => CLK,
      PIPE_ENB    => '1',
      REB         => mem_rd,
      WEB         => sig_erase,
      ADDRB       => mem_addr,
      DIB         => DATA_ZEROES,
      DOB_DV      => mem_do_dv,
      DOB         => mem_do
   );

   GEN_ERASE_T: if (ERASE = true) generate
      sig_erase <= mem_rd;
   end generate;

   GEN_ERASE_F: if (ERASE = false) generate
      sig_erase <= '0';
   end generate;

   -- ---------------------------------------------------------------------
   --                     Memory block swap logic
   -- ---------------------------------------------------------------------

   wr_blockp: process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            wr_block <= '0';
         elsif (wr_done = '1') then
            wr_block <= not wr_block;
         end if;
      end if;
   end process;

   rd_blockp: process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            rd_block <= '0';
         elsif (rd_done = '1') then
            rd_block <= not rd_block;
         end if;
      end if;
   end process;

   -- ---------------------------------------------------------------------
   --                     Memory read/write control FSM
   -- ---------------------------------------------------------------------

   sync_logic : process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            curr_state <= init;
         else
            curr_state <= next_state;
         end if;
      end if;
   end process sync_logic;

   -------------------------------------------------------
   next_state_logic : process(curr_state, wr_done, rd_done)
   begin
      next_state <= curr_state;
      case (curr_state) is

         -- write to block 0, don't read
         when init =>
            if (wr_done = '1') then
               next_state <= wr_1_rd_0;
            end if;

         -- write to block 1, read from block 0
         when wr_1_rd_0 =>
            if (rd_done = '1' and wr_done = '1') then
               next_state <= wr_0_rd_1;
            elsif (rd_done = '1') then
               next_state <= wr_1_wait;
            elsif (wr_done = '1') then
               next_state <= rd_0_wait;
            end if;

         -- write to block 1, don't read
         when wr_1_wait =>
            if (wr_done = '1') then
               next_state <= wr_0_rd_1;
            end if;

         -- read from block 0, don't write
         when rd_0_wait =>
            if (rd_done = '1') then
               next_state <= wr_0_rd_1;
            end if;

         -- write to block 0, read from block 1
         when wr_0_rd_1 =>
            if (rd_done = '1' and wr_done = '1') then
               next_state <= wr_1_rd_0;
            elsif (rd_done = '1') then
               next_state <= wr_0_wait;
            elsif (wr_done = '1') then
               next_state <= rd_1_wait;
            end if;

         -- write to block 0, don't read
         when wr_0_wait =>
            if (wr_done = '1') then
               next_state <= wr_1_rd_0;
            end if;

         -- read from block 1, don't write
         when rd_1_wait =>
            if (rd_done = '1') then
               next_state <= wr_1_rd_0;
            end if;

         when others =>
            next_state <= init;
      end case;
   end process next_state_logic;

   -------------------------------------------------------
   output_logic : process(curr_state)
   begin
      wr_0  <= '0';
      wr_1  <= '0';
      rd_0  <= '0';
      rd_1  <= '0';
      case (curr_state) is

         -- write to block 0, don't read
         when init =>
            wr_0  <= '1';

         -- write to block 1, read from block 0
         when wr_1_rd_0 =>
            wr_1  <= '1';
            rd_0  <= '1';

         -- write to block 1, don't read
         when wr_1_wait =>
            wr_1  <= '1';

         -- read from block 0, don't write
         when rd_0_wait =>
            rd_0  <= '1';

         -- write to block 0, read from block 1
         when wr_0_rd_1 =>
            wr_0  <= '1';
            rd_1  <= '1';

         -- write to block 0, don't read
         when wr_0_wait =>
            wr_0  <= '1';

         -- read from block 1, don't write
         when rd_1_wait =>
            rd_1  <= '1';

         when others => null;
      end case;
   end process output_logic;

   -- ---------------------------------------------------------------------
   --                     Memory output - UH
   -- ---------------------------------------------------------------------

   mem_addr       <= rd_block & cnt_addr;
   mem_rd         <= not OUT_DST_RDY_N and (rd_0 or rd_1);
   OUT_SRC_RDY_N  <= not mem_do_dv;
   OUT_DATA       <= mem_do;
   OUT_REM        <= (others => '1');
   OUT_SOF_N      <= not (mem_do_dv and reg_cnt_start);
   OUT_SOP_N      <= not (mem_do_dv and reg_cnt_start);
   OUT_EOF_N      <= not (mem_do_dv and reg_cnt_stop);
   OUT_EOP_N      <= not (mem_do_dv and reg_cnt_stop);
   rd_done        <= cnt_stop;

   -- cnt_addr counter
   cnt_addrp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_addr <= (others => '0');
         elsif (mem_rd = '1') then
            cnt_addr <= cnt_addr + 1;
         end if;
      end if;
   end process;

   reg_cnt_addrp: process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_cnt_addr <= (others => '0');
         else
            reg_cnt_addr <= cnt_addr;
         end if;
      end if;
   end process;

   reg_cnt_startp: process(reg_cnt_addr)
   begin
      if (reg_cnt_addr = ZEROES) then
         reg_cnt_start <= '1';
      else
         reg_cnt_start <= '0';
      end if;
   end process;

   reg_cnt_stopp: process(reg_cnt_addr)
   begin
      if (reg_cnt_addr = ONES) then
         reg_cnt_stop <= '1';
      else
         reg_cnt_stop <= '0';
      end if;
   end process;

   cnt_stopp: process(cnt_addr)
   begin
      if (cnt_addr = ONES) then
         cnt_stop <= '1';
      else
         cnt_stop <= '0';
      end if;
   end process;

   -- ---------------------------------------------------------------------
   --                     SW part - read from memory
   -- ---------------------------------------------------------------------

   -- MI32 output signals
   MI.ARDY              <= MI.RD or MI.WR;
   MI.DRDY              <= sw_do_dv;
   sw_addr              <= MI.ADDR(BLK_ADDR_WIDTH-1 downto 0);

   GEN_MIDRD_32_L: if (DATA_WIDTH < 32) generate
      MI.DRD(31 downto DATA_WIDTH)  <= (others => '0');
      MI.DRD(DATA_WIDTH-1 downto 0) <= sw_do;
   end generate;

   GEN_MIDRD_32_E: if (DATA_WIDTH = 32) generate
      MI.DRD   <= sw_do;
   end generate;

   GEN_MIDRD_32_G: if (DATA_WIDTH > 32) generate
      MI.DRD <= sw_do(31 downto 0);
   end generate;

   -- get control / release control
   sw_readp: process (RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            sw_read <= '0';
         elsif (MI.WR = '1') then
            sw_read <= MI.DWR(0);
         end if;
      end if;
   end process;

   sw_addr_decp: process(MI.RD)
   begin
      sw_rd <= '0';
      if (MI.RD = '1') then
         sw_rd <= '1';
      end if;
   end process;

   -- ---------------------------------------------------------------------

end architecture full;
