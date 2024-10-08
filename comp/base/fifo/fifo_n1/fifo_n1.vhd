-- fifo_n1.vhd: FIFO - m x n bit with multiple write ports
--                  - synchronous read/write
-- Copyright (C) 2017 CESNET
-- Author(s): Vaclav Hummel vaclav.hummel@cesnet.cz
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FIFO_N1 is

   -- Pipeline 0 signals ------------------------------------------------------
   -- Input pipe
   signal pipe0_in_dst_rdy     : std_logic;
   signal pipe0_out_deser      : std_logic_vector(WRITE_PORTS*DATA_WIDTH+WRITE_PORTS-1 downto 0);
   signal pipe0_data_out_deser      : std_logic_vector(WRITE_PORTS*DATA_WIDTH-1 downto 0);
   signal pipe0_data_out            : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal pipe0_data_we             : std_logic_vector(WRITE_PORTS-1 downto 0);
   signal pipe0_out_src_rdy    : std_logic;
   signal pipe0_out_src_rdy_slv: std_logic_vector(0 downto 0);
   signal pipe0_out_dst_rdy    : std_logic;

   -- Pipeline 1 signals ------------------------------------------------------
   -- Sum of WE
   signal sum_we                  : std_logic_vector(log2(WRITE_PORTS+1)-1 downto 0);

   -- N-one detector
   signal n_one_addrs          : slv_array_t(0 to WRITE_PORTS-1)(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal n_one_addrs_vld      : std_logic_vector(WRITE_PORTS-1 downto 0);

   -- Data registers
   signal reg1_sum_we             : std_logic_vector(log2(WRITE_PORTS+1)-1 downto 0);
   signal reg1_n_one_addrs          : slv_array_t(0 to WRITE_PORTS-1)(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal reg1_data          : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal reg1_we               : std_logic_vector(WRITE_PORTS-1 downto 0);

   -- Control registers
   signal reg1_vld               : std_logic;
   signal reg1_empty             : std_logic;

   -- Pipeline 2 signals ------------------------------------------------------
   -- Input multiplexer
   signal in_mux_sel           : slv_array_t(0 to WRITE_PORTS-1)(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal in_mux_sel_deser     : std_logic_vector(WRITE_PORTS*max(log2(WRITE_PORTS),1)-1 downto 0);
   signal in_mux_out           : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);

   -- Memory WE
   signal reg2_memory_we_in      : std_logic_vector(WRITE_PORTS-1 downto 0);
   signal reg2_memory_we_shifted : std_logic_vector(WRITE_PORTS-1 downto 0);

   -- Memory selection counter
   signal memory_sel_sum           : std_logic_vector(log2(2*WRITE_PORTS)-1 downto 0);
   signal memory_sel_sum_ov        : std_logic_vector(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal memory_sel_sum_ov_ext    : std_logic_vector(max(log2(WRITE_PORTS+1),1)-1 downto 0);
   signal cnt2_memory_sel_ov       : std_logic;

   -- Data registers
   signal reg2_sum_we             : std_logic_vector(log2(WRITE_PORTS+1)-1 downto 0);
   signal reg2_in_mux_out       : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal reg2_memory_we       : std_logic_vector(WRITE_PORTS-1 downto 0);
   signal cnt2_memory_sel          : std_logic_vector(max(log2(WRITE_PORTS),1)-1 downto 0);

   -- Control registers
   signal reg2_vld               : std_logic;
   signal reg2_empty             : std_logic;

   -- Pipeline 3 signals ------------------------------------------------------
   -- Memory
   signal cnt3_memory_wr_pointer : slv_array_t(0 to WRITE_PORTS-1)(log2(ITEMS)-1 downto 0);
   signal memory_full            : std_logic;
   signal memory_empty           : std_logic;

   -- Free space counter
   signal cnt3_free_space         : std_logic_vector(log2(WRITE_PORTS*ITEMS+1)-1 downto 0);

   -- Control registers
   signal reg3_vld               : std_logic;
   signal reg3_empty             : std_logic;

   -- Pipeline 4 signals ------------------------------------------------------
   -- Output data path
   signal out_mux_in           : slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
   signal out_mux_sel          : std_logic_vector(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal out_mux_out          : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- Read pointer
   signal cnt4_memory_rd_pointer_low   : std_logic_vector(max(log2(WRITE_PORTS),1)-1 downto 0);
   signal cnt4_memory_rd_pointer_high  : std_logic_vector(log2(ITEMS)-1 downto 0);

   -- Output pipe
   signal pipe4_in_dst_rdy    : std_logic;
   signal pipe4_out_src_rdy   : std_logic;
   signal reg4_empty_slv      : std_logic_vector(0 downto 0);

begin
-- ----------------------------------------------------------------------------
--                      Pipeline 0
-- ----------------------------------------------------------------------------

   fifo_n1g: if WRITE_PORTS /= 1 generate

   -- Input Pipe
   pipe0_i: entity work.pipe
   generic map(
      DEVICE => DEVICE,
      DATA_WIDTH => WRITE_PORTS*DATA_WIDTH+WRITE_PORTS,
      USE_OUTREG => true,
      FAKE_PIPE => not DI_PIPE
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK => CLK,
      RESET => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA => slv_array_ser(DATA_IN, WRITE_PORTS, DATA_WIDTH) & WE,
      IN_SRC_RDY => or (WE),
      IN_DST_RDY => pipe0_in_dst_rdy,

      -- Output interface -----------------------------------------------------
      OUT_DATA => pipe0_out_deser,
      OUT_SRC_RDY => pipe0_out_src_rdy,
      OUT_DST_RDY => pipe0_out_dst_rdy
   );

   FULL <= not pipe0_in_dst_rdy;

   pipe0_data_out_deser <= pipe0_out_deser(WRITE_PORTS*DATA_WIDTH+WRITE_PORTS-1 downto WRITE_PORTS);
   pipe0_data_out <= slv_array_to_deser(pipe0_data_out_deser, WRITE_PORTS, DATA_WIDTH);
   pipe0_data_we <= pipe0_out_deser(WRITE_PORTS-1 downto 0);


-- ----------------------------------------------------------------------------
--                      Pipeline 1
-- ----------------------------------------------------------------------------

   -- Sum of WE
   sum_wep: process(pipe0_data_we)
      variable a : unsigned(max(log2(WRITE_PORTS+1),1)-1 downto 0);
   begin
      a := (others => '0');
      for i in 0 to WRITE_PORTS-1 loop
         a := a + unsigned(pipe0_data_we(i downto i));
      end loop;
      sum_we <= std_logic_vector(a);
   end process;

   -- N-one detector
   n_oneg: for i in 0 to WRITE_PORTS-1 generate
      n_onei: entity work.N_ONE
      generic map(
         --! \brief Data width of input vector
         DATA_WIDTH => WRITE_PORTS
      )
      port map(

         --! \name Clock & reset interface
         --! --------------------------------------------------------------------------
         --! \brief Common clock
         CLK => CLK,
         --! \brief Common reset
         RESET => RESET,

         --! \name Input vector
         --! --------------------------------------------------------------------------
         D => pipe0_data_we,

         --! \name N one number
         --! -------------------------------------------------------------------------
         N => std_logic_vector(to_unsigned(i, max(log2(WRITE_PORTS),1))),

         --! \name Output address
         --! --------------------------------------------------------------------------
         A => n_one_addrs(i),
         --! \brief Valid bit
         VLD => n_one_addrs_vld(i)

      );
   end generate;

   -- Control register
   reg1_vldp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg1_vld <= '0';
         elsif (reg1_empty = '1') then
            reg1_vld <= pipe0_out_src_rdy;
         end if;
      end if;
   end process;

   reg1_empty <= (not reg1_vld) or reg2_empty;
   pipe0_out_dst_rdy <= reg1_empty;

   -- Register
   reg1_sum_wep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg1_empty = '1') then
            reg1_sum_we <= sum_we;
         end if;
      end if;
   end process;

   -- Register
   reg1_n_one_addrsp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg1_empty = '1') then
            reg1_n_one_addrs <= n_one_addrs;
         end if;
      end if;
   end process;

   -- Register
   reg1_data_inp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg1_empty = '1') then
            reg1_data <= pipe0_data_out;
         end if;
      end if;
   end process;

   -- Register
   reg1_wep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg1_empty = '1') then
            reg1_we <= pipe0_data_we;
         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                      Pipeline 2
-- ----------------------------------------------------------------------------
   -- Input multiplexer -------------------------------------------------------
   in_muxg: for i in 0 to WRITE_PORTS-1 generate
      in_muxi: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => DATA_WIDTH,
         MUX_WIDTH => WRITE_PORTS
      )
      port map(
         DATA_IN => slv_array_ser(reg1_data, WRITE_PORTS, DATA_WIDTH),
         SEL => in_mux_sel(i),
         DATA_OUT => in_mux_out(i)
      );
   end generate;

   -- Input multiplexer selection process
   barrel_shifteri: entity work.BARREL_SHIFTER_GEN
   generic map(
      -- input/output data width in BLOCKs
      BLOCKS => WRITE_PORTS,
      -- size of one block in bits
      BLOCK_SIZE => max(log2(WRITE_PORTS),1),
      -- NOTE: data_width = blocks*block_size

      -- set true to shift left, false to shift right
      SHIFT_LEFT => true
   )
   port map(
      DATA_IN => slv_array_ser(reg1_n_one_addrs, WRITE_PORTS, (max(log2(WRITE_PORTS),1))),
      DATA_OUT => in_mux_sel_deser,
      SEL => cnt2_memory_sel
   );

   in_mux_sel <= slv_array_to_deser(in_mux_sel_deser, WRITE_PORTS, (max(log2(WRITE_PORTS),1)));

   -- Memory WE
   reg2_memory_we_ing: for i in 0 to WRITE_PORTS-1 generate
      reg2_memory_we_in(i) <= '1' when (i < to_integer(unsigned(reg1_sum_we))) else
                       '0';
   end generate;

   barrel_shifter_wei: entity work.BARREL_SHIFTER_GEN
   generic map(
      -- input/output data width in BLOCKs
      BLOCKS => WRITE_PORTS,
      -- size of one block in bits
      BLOCK_SIZE => 1,
      -- NOTE: data_width = blocks*block_size

      -- set true to shift left, false to shift right
      SHIFT_LEFT => true
   )
   port map(
      DATA_IN => reg2_memory_we_in,
      DATA_OUT => reg2_memory_we_shifted,
      SEL => cnt2_memory_sel
   );

   -- Control register
   reg2_vldp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg2_vld <= '0';
         elsif (reg2_empty = '1') then
            reg2_vld <= reg1_vld;
         end if;
      end if;
   end process;

   reg2_empty <= (not reg2_vld) or reg3_empty;

   -- Memory selection counter, counter mod WRITE_PORTS
   memory_sel_sum <= std_logic_vector(to_unsigned(to_integer(unsigned(cnt2_memory_sel)) +
                                                 to_integer(unsigned(reg1_sum_we)), log2(2*WRITE_PORTS)));

   memory_sel_sum_ov_ext <= std_logic_vector(unsigned(cnt2_memory_sel) + unsigned(reg1_sum_we) - to_unsigned(WRITE_PORTS, max(log2(WRITE_PORTS+1),1)));
   memory_sel_sum_ov <= memory_sel_sum_ov_ext(max(log2(WRITE_PORTS),1)-1 downto 0);

   cnt2_memory_sel_ov <= '1' when (to_integer(unsigned(memory_sel_sum)) >= WRITE_PORTS) else
                    '0';

   cnt2_memory_selp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt2_memory_sel <= std_logic_vector(to_unsigned(0, max(log2(WRITE_PORTS),1)));
         elsif (reg2_empty = '1' and reg1_vld = '1') then
            if (cnt2_memory_sel_ov = '1') then
               cnt2_memory_sel <= memory_sel_sum_ov(max(log2(WRITE_PORTS),1)-1 downto 0);
            else
               cnt2_memory_sel <= memory_sel_sum(max(log2(WRITE_PORTS),1)-1 downto 0);
            end if;
         end if;
      end if;
   end process;

   -- Register
   reg_in_mux_outp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg2_empty = '1') then
            reg2_in_mux_out <= in_mux_out;
         end if;
      end if;
   end process;

   -- Register
   reg2_memory_wep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg2_empty = '1') then
            reg2_memory_we <= reg2_memory_we_shifted;
         end if;
      end if;
   end process;

   -- Register
   reg2_sum_wep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (reg2_empty = '1') then
            reg2_sum_we <= reg1_sum_we;
         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                      Pipeline 3
-- ----------------------------------------------------------------------------

   -- Memory ------------------------------------------------------------------
   memoryg: for i in 0 to WRITE_PORTS-1 generate
      memoryi : entity work.SDP_DISTMEM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         ITEMS          => ITEMS
      )
      port map (
         WCLK        => CLK,
         ADDRA       => cnt3_memory_wr_pointer(i),
         DI          => reg2_in_mux_out(i),
         WE          => reg2_memory_we(i) and reg2_vld and reg3_empty,
         ADDRB       => cnt4_memory_rd_pointer_high,
         DOB         => out_mux_in(i)
      );
   end generate;


   -- Write interface ---------------------------------------------------------
   -- Free space counter
   cnt3_free_spacep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt3_free_space <= std_logic_vector(to_unsigned(WRITE_PORTS*ITEMS, log2(WRITE_PORTS*ITEMS+1)));
         else
            cnt3_free_space <= std_logic_vector(to_unsigned(to_integer(unsigned(cnt3_free_space)) - to_integer(unsigned(reg2_sum_we and reg2_vld and reg3_empty)) +
                                                            to_integer(unsigned(reg4_empty_slv and reg3_vld)), log2(WRITE_PORTS*ITEMS+1)));
         end if;
      end if;
   end process;

   -- FULL signal
   memory_full <= '1' when(to_integer(unsigned(cnt3_free_space)) < to_integer(unsigned(reg2_sum_we))) else
           '0';
   reg3_empty <= not memory_full;

   -- AFULL signal
   AFULL <= '1' when(to_integer(unsigned(cnt3_free_space)) < ALMOST_FULL_OFFSET) else
            '0';
   -- EMPTY signal
   memory_empty <= '1' when(to_integer(unsigned(cnt3_free_space)) = WRITE_PORTS*ITEMS) else
            '0';
   reg3_vld <= not memory_empty;
   -- AEMPTY signal
   AEMPTY <= '1' when(to_integer(unsigned(cnt3_free_space)) > WRITE_PORTS*ITEMS-ALMOST_EMPTY_OFFSET) else
             '0';

   -- Write pointers
   cnt3_memory_wr_pointerg: for i in 0 to WRITE_PORTS-1 generate
      cnt3_memory_wr_pointerp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               cnt3_memory_wr_pointer(i) <= (others => '0');
            elsif (reg2_memory_we(i) = '1' and reg2_vld = '1' and reg3_empty = '1') then
               if (to_integer(unsigned(cnt3_memory_wr_pointer(i))) = ITEMS-1) then
                  cnt3_memory_wr_pointer(i) <= (others => '0');
               else
                  cnt3_memory_wr_pointer(i) <= std_logic_vector(unsigned(cnt3_memory_wr_pointer(i)) + to_unsigned(1,1));
               end if;
            end if;
         end if;
      end process;
   end generate;

-- ----------------------------------------------------------------------------
--                      Pipeline 4
-- ----------------------------------------------------------------------------

   -- Read interface ----------------------------------------------------------

   -- Output multiplexer
   out_muxi: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      MUX_WIDTH => WRITE_PORTS
   )
   port map(
      DATA_IN => slv_array_ser(out_mux_in, WRITE_PORTS, DATA_WIDTH),
      SEL => out_mux_sel,
      DATA_OUT => out_mux_out
   );


   -- Read pointer low
   cnt4_memory_rd_pointer_lowp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt4_memory_rd_pointer_low <= (others => '0');
         elsif (reg3_vld = '1' and pipe4_in_dst_rdy = '1') then
            if (to_integer(unsigned(cnt4_memory_rd_pointer_low)) = WRITE_PORTS-1) then
               cnt4_memory_rd_pointer_low <= (others => '0');
            else
               cnt4_memory_rd_pointer_low <= std_logic_vector(unsigned(cnt4_memory_rd_pointer_low) + to_unsigned(1,1));
            end if;
         end if;
      end if;
   end process;

   out_mux_sel <= cnt4_memory_rd_pointer_low;

   -- Read pointer high
   cnt4_memory_rd_pointer_highp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt4_memory_rd_pointer_high <= (others => '0');
         elsif (reg3_vld = '1' and pipe4_in_dst_rdy = '1' and to_integer(unsigned(cnt4_memory_rd_pointer_low)) = WRITE_PORTS-1) then
            if (to_integer(unsigned(cnt4_memory_rd_pointer_high)) = ITEMS-1) then
               cnt4_memory_rd_pointer_high <= (others => '0');
            else
               cnt4_memory_rd_pointer_high <= std_logic_vector(unsigned(cnt4_memory_rd_pointer_high) + to_unsigned(1,1));
            end if;
         end if;
      end if;
   end process;

   -- Output Pipe
   pipe4_i: entity work.pipe
   generic map(
      DEVICE => DEVICE,
      DATA_WIDTH => DATA_WIDTH,
      USE_OUTREG => true,
      FAKE_PIPE => not DO_PIPE
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK => CLK,
      RESET => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA => out_mux_out,
      IN_SRC_RDY => reg3_vld,
      IN_DST_RDY => pipe4_in_dst_rdy,

      -- Output interface -----------------------------------------------------
      OUT_DATA => DATA_OUT,
      OUT_SRC_RDY => pipe4_out_src_rdy,
      OUT_DST_RDY => RE
   );

   EMPTY <= not pipe4_out_src_rdy;
   reg4_empty_slv(0) <= pipe4_in_dst_rdy;

   end generate;

   fifo_11g: if WRITE_PORTS = 1 generate

-- Input Pipe
   pipe0_i: entity work.pipe
   generic map(
      DEVICE => DEVICE,
      DATA_WIDTH => WRITE_PORTS*DATA_WIDTH+WRITE_PORTS,
      USE_OUTREG => true,
      FAKE_PIPE => not DI_PIPE
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK => CLK,
      RESET => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA => slv_array_ser(DATA_IN, WRITE_PORTS, DATA_WIDTH) & WE,
      IN_SRC_RDY => or (WE),
      IN_DST_RDY => pipe0_in_dst_rdy,

      -- Output interface -----------------------------------------------------
      OUT_DATA => pipe0_out_deser,
      OUT_SRC_RDY => pipe0_out_src_rdy,
      OUT_DST_RDY => reg3_empty
   );

   pipe0_out_src_rdy_slv(0) <= pipe0_out_src_rdy;

   FULL <= not pipe0_in_dst_rdy;

   pipe0_data_out_deser <= pipe0_out_deser(WRITE_PORTS*DATA_WIDTH+WRITE_PORTS-1 downto WRITE_PORTS);
   pipe0_data_out <= slv_array_to_deser(pipe0_data_out_deser, WRITE_PORTS, DATA_WIDTH);
   pipe0_data_we <= pipe0_out_deser(WRITE_PORTS-1 downto 0);

-- ----------------------------------------------------------------------------
--                      Pipeline 3
-- ----------------------------------------------------------------------------

   -- Memory ------------------------------------------------------------------
   memoryg: for i in 0 to WRITE_PORTS-1 generate
      memoryi : entity work.SDP_DISTMEM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         ITEMS          => ITEMS
      )
      port map (
         WCLK        => CLK,
         ADDRA       => cnt3_memory_wr_pointer(i),
         DI          => pipe0_data_out(i),
         WE          => pipe0_out_src_rdy and reg3_empty,
         ADDRB       => cnt4_memory_rd_pointer_high,
         DOB         => out_mux_in(i)
      );
   end generate;

   -- Write interface ---------------------------------------------------------
   -- Free space counter
   cnt3_free_spacep: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt3_free_space <= std_logic_vector(to_unsigned(WRITE_PORTS*ITEMS, log2(WRITE_PORTS*ITEMS+1)));
         else
            cnt3_free_space <= std_logic_vector(to_unsigned(to_integer(unsigned(cnt3_free_space)) - to_integer(unsigned(pipe0_out_src_rdy_slv and reg3_empty)) +
                                                            to_integer(unsigned(reg4_empty_slv and reg3_vld)), log2(WRITE_PORTS*ITEMS+1)));
         end if;
      end if;
   end process;

   -- FULL signal
   memory_full <= '1' when(to_integer(unsigned(cnt3_free_space)) = 0) else
           '0';
   reg3_empty <= not memory_full;

   -- AFULL signal
   AFULL <= '1' when(to_integer(unsigned(cnt3_free_space)) < ALMOST_FULL_OFFSET) else
            '0';
   -- EMPTY signal
   memory_empty <= '1' when(to_integer(unsigned(cnt3_free_space)) = WRITE_PORTS*ITEMS) else
            '0';
   reg3_vld <= not memory_empty;

   -- AEMPTY signal
   AEMPTY <= '1' when(to_integer(unsigned(cnt3_free_space)) > WRITE_PORTS*ITEMS-ALMOST_EMPTY_OFFSET) else
             '0';

   -- Write pointers
   cnt3_memory_wr_pointerg: for i in 0 to WRITE_PORTS-1 generate
      cnt3_memory_wr_pointerp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               cnt3_memory_wr_pointer(i) <= (others => '0');
            elsif (pipe0_out_src_rdy_slv(i) = '1' and reg3_empty = '1') then
               if (to_integer(unsigned(cnt3_memory_wr_pointer(i))) = ITEMS-1) then
                  cnt3_memory_wr_pointer(i) <= (others => '0');
               else
                  cnt3_memory_wr_pointer(i) <= std_logic_vector(unsigned(cnt3_memory_wr_pointer(i)) + to_unsigned(1,1));
               end if;
            end if;
         end if;
      end process;
   end generate;

-- ----------------------------------------------------------------------------
--                      Pipeline 4
-- ----------------------------------------------------------------------------

   -- Read interface ----------------------------------------------------------

   -- Read pointer high
   cnt4_memory_rd_pointer_highp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt4_memory_rd_pointer_high <= (others => '0');
         elsif (reg3_vld = '1' and pipe4_in_dst_rdy = '1') then
            if (to_integer(unsigned(cnt4_memory_rd_pointer_high)) = ITEMS-1) then
               cnt4_memory_rd_pointer_high <= (others => '0');
            else
               cnt4_memory_rd_pointer_high <= std_logic_vector(unsigned(cnt4_memory_rd_pointer_high) + to_unsigned(1,1));
            end if;
         end if;
      end if;
   end process;

   -- Output Pipe
   pipe4_i: entity work.pipe
   generic map(
      DEVICE => DEVICE,
      DATA_WIDTH => DATA_WIDTH,
      USE_OUTREG => true,
      FAKE_PIPE => not DO_PIPE
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK => CLK,
      RESET => RESET,

      -- Input interface ------------------------------------------------------
      IN_DATA => slv_array_ser(out_mux_in, WRITE_PORTS, DATA_WIDTH),
      IN_SRC_RDY => reg3_vld,
      IN_DST_RDY => pipe4_in_dst_rdy,

      -- Output interface -----------------------------------------------------
      OUT_DATA => DATA_OUT,
      OUT_SRC_RDY => pipe4_out_src_rdy,
      OUT_DST_RDY => RE
   );

   EMPTY <= not pipe4_out_src_rdy;
   reg4_empty_slv(0) <= pipe4_in_dst_rdy;

   end generate;


end architecture behavioral;
