-- flu2fl_top.vhd: Top level architecture for FLU to FL converter
-- Copyright (C) 2012 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of flu2fl is
   constant SOP_STEP    : integer := DATA_WIDTH/(2**SOP_POS_WIDTH);
   constant EOP_STEP    : integer := 8;

   -- input registers
   signal data_reg         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sop_reg          : std_logic;
   signal eop_reg          : std_logic;
   signal sop_pos_reg      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal eop_pos_reg      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   -- abstract signals declarations
   signal data_field       : std_logic_vector(DATA_WIDTH*2-1 downto 0);
   signal sop1             : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
   signal sop2             : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
   signal eop1             : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
   signal eop2             : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
   signal eop_sel          : std_logic_vector(log2(DATA_WIDTH/8) downto 0);
   signal sop1_v           : std_logic;
   signal sop2_v           : std_logic;
   signal eop1_v           : std_logic;
   signal eop2_v           : std_logic;
   signal eop_out          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal detect_eop       : std_logic; -- inside sliding window (Output word)
   signal detect_sop       : std_logic; -- inside input word
   signal end_sent         : std_logic;
   signal end_sending      : std_logic;
   signal full             : std_logic;

   -- sliding window end border
   signal offset           : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal offset_we        : std_logic;
   signal offset_new       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   -- Input pipeline
   signal in_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_sop        : std_logic;
   signal in_eop        : std_logic;
   signal in_src_rdy    : std_logic;
   signal in_dst_rdy    : std_logic;

   -- Output pipeline
   signal out_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_drem     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal out_src_rdy_n: std_logic;
   signal out_dst_rdy_n: std_logic;
   signal out_sof_n    : std_logic;
   signal out_eof_n    : std_logic;
   signal out_sop_n    : std_logic;
   signal out_eop_n    : std_logic;

begin
   -- input registers
   in_reg_control_i : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            sop_reg <= '0';
            eop_reg <= '0';
         elsif in_src_rdy = '1' and in_dst_rdy = '1' then
            sop_reg     <= in_sop;
            eop_reg     <= in_eop;
         end if;
      end if;
   end process;

   in_reg_data_i : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if in_src_rdy = '1' and in_dst_rdy = '1' then
            data_reg    <= in_data;
            sop_pos_reg <= in_sop_pos;
            eop_pos_reg <= in_eop_pos;
         end if;
      end if;
   end process;

   -- offset register
   offset_reg_i : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            offset <= (log2(DATA_WIDTH/8)-1 downto 0 => '0');
         elsif offset_we = '1' then
            offset <= offset_new;
         end if;
      end if;
   end process;

   -- abstract signals definitions
   data_field <= in_data & data_reg;
   sop1       <= '1' & in_sop_pos  & (log2(SOP_STEP/EOP_STEP)-1 downto 0 => '0');
   eop1       <= '1' & in_eop_pos;
   sop2       <= '0' & sop_pos_reg & (log2(SOP_STEP/EOP_STEP)-1 downto 0 => '0');
   eop2       <= '0' & eop_pos_reg;
   sop1_v     <= in_sop and in_src_rdy and in_dst_rdy;
   eop1_v     <= in_eop and in_src_rdy and in_dst_rdy;
   sop2_v     <= sop_reg;
   eop2_v     <= eop_reg;
   detect_eop <= '1' when (eop1_v='1' and eop1<('1' & offset)) or (eop2_v='1' and eop2>=('0' & offset)) else '0';
   detect_sop  <= sop1_v;
   end_sending <= not(out_eof_n or out_dst_rdy_n or out_src_rdy_n);
   eop_sel     <= eop2 when (eop2>=('0' & offset) and eop2_v='1') else eop1;
   eop_out     <= eop_sel(log2(DATA_WIDTH/8)-1 downto 0) - offset;

   -- output signals (FL) mapping
   out_data   <= data_field(DATA_WIDTH+conv_integer(offset)*8-1 downto conv_integer(offset)*8);
   out_drem   <= (others => '1') when detect_eop='0' else eop_out;
   out_eof_n  <= not detect_eop;
   out_eop_n  <= not detect_eop;
   out_sof_n  <= not (sop2_v and end_sent);
   out_sop_n  <= not (sop2_v and end_sent);
   in_dst_rdy    <= ((not out_dst_rdy_n) or not full) and (end_sent or not sop2_v);
   out_src_rdy_n <= not((in_src_rdy or detect_eop) and full and (not end_sent or sop2_v));
   offset_we     <= (end_sent and not (sop2_v and full)) or end_sending;
   offset_new    <= sop1(log2(DATA_WIDTH/8)-1 downto 0) when sop1_v='1' else
                    sop2(log2(DATA_WIDTH/8)-1 downto 0);

   end_sent_i : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' or end_sending='1' then
            end_sent <= '1';
         elsif out_sof_n='0' and out_dst_rdy_n='0' and out_src_rdy_n='0' then
            end_sent <= '0';
         end if;
      end if;
   end process;

   full_i : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            full <= '0';
         elsif in_dst_rdy='1' and in_src_rdy='1' then
            full <= '1';
         elsif out_dst_rdy_n='0' and out_src_rdy_n='0' and not (sop2_v='1' and end_sent='0') then
            full <= '0';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------------
   -- PIPES
   -- -------------------------------------------------------------------------------
   -- Input Pipe (FLU)
   in_pipe_i : entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      USE_OUTREG     => IN_PIPE_OUTREG,
      PIPE_TYPE      => IN_PIPE_TYPE,
      FAKE_PIPE      => not IN_PIPE_EN
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      -- Output interf
      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,
      -- Input interf
      TX_DATA       => in_data,
      TX_SOP_POS    => in_sop_pos,
      TX_EOP_POS    => in_eop_pos,
      TX_SOP        => in_sop,
      TX_EOP        => in_eop,
      TX_SRC_RDY    => in_src_rdy,
      TX_DST_RDY    => in_dst_rdy
   );


   -- Output Pipe (FL)
   use_inpipe_gen : if OUT_PIPE_EN generate
   out_pipe_i : entity work.FL_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      PIPE_TYPE      => OUT_PIPE_TYPE,
      USE_OUTREG     => OUT_PIPE_OUTREG
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      -- Input inter
      RX_SOF_N       => out_sof_n,
      RX_SOP_N       => out_sop_n,
      RX_EOP_N       => out_eop_n,
      RX_EOF_N       => out_eof_n,
      RX_SRC_RDY_N   => out_src_rdy_n,
      RX_DST_RDY_N   => out_dst_rdy_n,
      RX_DATA        => out_data,
      RX_REM         => out_drem,
      -- Output interf
      TX_SOF_N       => TX_SOF_N,
      TX_SOP_N       => TX_SOP_N,
      TX_EOP_N       => TX_EOP_N,
      TX_EOF_N       => TX_EOF_N,
      TX_SRC_RDY_N   => TX_SRC_RDY_N,
      TX_DST_RDY_N   => TX_DST_RDY_N,
      TX_DATA        => TX_DATA,
      TX_REM         => TX_DREM
   );
   end generate;
   no_use_inpipe_gen : if not OUT_PIPE_EN generate
      TX_SOF_N       <= out_sof_n;
      TX_SOP_N       <= out_sop_n;
      TX_EOP_N       <= out_eop_n;
      TX_EOF_N       <= out_eof_n;
      TX_SRC_RDY_N   <= out_src_rdy_n;
      TX_DATA        <= out_data;
      TX_DREM         <= out_drem;
      out_dst_rdy_n  <= TX_DST_RDY_N;
   end generate;
end architecture;
