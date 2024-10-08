-- flu2axi.vhd: Top level entity for FLU to AXI converter
-- Copyright (C) 2014 CESNET
-- Author(s): Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity flu2axi is
   generic(
      --! data width of input FLU and output AXI interfaces
      DATA_WIDTH 	: integer := 512;
      --! sop_pos whidth of input FLU (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	: integer := 3;
      --! use input pipe
      IN_PIPE_EN           : boolean := false;
      --! use output register of input pipe
      IN_PIPE_OUTREG       : boolean := false;
      --! use output pipe
      OUT_PIPE_EN          : boolean := false;
      --! use output register of input pipe
      OUT_PIPE_OUTREG      : boolean := false
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;

      --! Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      --! AXI output interface
      TX_TDATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_TKEEP      : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      TX_TVALID     : out std_logic;
      TX_TLAST      : out std_logic;
      TX_TREADY     : in std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                    Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of flu2axi is

   --! TX_TKEEP width
   constant tkeep_width : integer := DATA_WIDTH/8;

   --! Input pipeline
   signal in_pipe_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_pipe_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_pipe_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_pipe_sop        : std_logic;
   signal in_pipe_eop        : std_logic;
   signal in_pipe_src_rdy    : std_logic;
   signal in_pipe_dst_rdy    : std_logic;

   --! Output pipeline
   signal   out_pipe_tdata    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal   out_pipe_tkeep    : std_logic_vector(tkeep_width-1 downto 0);
   signal   out_pipe_tlast    : std_logic;
   signal   out_pipe_tready   : std_logic;
   signal   out_pipe_tvalid   : std_logic;
   --! Data width of AXI pipe
   constant axi_pipe_width    : integer := DATA_WIDTH+(DATA_WIDTH/8)+1;
   --! Signals for merging data to AXI pipe
   signal   out_pipe_axi_data_in : std_logic_vector(axi_pipe_width-1 downto 0);
   signal   out_pipe_axi_data_out : std_logic_vector(axi_pipe_width-1 downto 0);

   --! Extended RX_SOP_POS
   signal ext_sop_pos : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

begin

   ext_sop_pos  <= in_pipe_sop_pos & (log2(DATA_WIDTH/8)-SOP_POS_WIDTH-1 downto 0 => '0')
   when
      SOP_POS_WIDTH<log2(DATA_WIDTH/8)
   else
      in_pipe_sop_pos;

   --! Input Pipe (FLU)
   in_pipe_i : entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      USE_OUTREG     => OUT_PIPE_OUTREG,
      FAKE_PIPE      => not IN_PIPE_EN
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      --! Input interface
      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,
      --! Output interface
      TX_DATA       => in_pipe_data,
      TX_SOP_POS    => in_pipe_sop_pos,
      TX_EOP_POS    => in_pipe_eop_pos,
      TX_SOP        => in_pipe_sop,
      TX_EOP        => in_pipe_eop,
      TX_SRC_RDY    => in_pipe_src_rdy,
      TX_DST_RDY    => in_pipe_dst_rdy
   );

   --! Connection and conversion
   out_pipe_tdata 	<= in_pipe_data;
   out_pipe_tvalid 	<= in_pipe_src_rdy;
   out_pipe_tlast	   <= in_pipe_eop;
   in_pipe_dst_rdy 	<= out_pipe_tready;

-- ----------------------------------------------------------------------------
--                       TX_TKEEP SET

   process (in_pipe_sop, in_pipe_eop, in_pipe_eop_pos, ext_sop_pos)

      --! Variables for converson std_logic_vector signals to integer
      variable var_eop_pos     : integer;
      variable var_ext_sop_pos : integer;
   begin

      var_eop_pos 	:= conv_integer(in_pipe_eop_pos);
      var_ext_sop_pos 	:= conv_integer(ext_sop_pos);

      out_pipe_tkeep <= (others => '1');

      --! Packet ends in this transaction
      if (in_pipe_sop = '0' and in_pipe_eop = '1') then
         for i in 0 to tkeep_width-1 loop
            if i <= var_eop_pos then
               out_pipe_tkeep(i) <= '1';
            else
               out_pipe_tkeep(i) <= '0';
            end if;
         end loop;

      --! Packet starts in this transaction
      elsif (in_pipe_sop = '1' and in_pipe_eop = '0') then
         for i in 0 to tkeep_width-1 loop
            if i < var_ext_sop_pos then
               out_pipe_tkeep(i) <= '0';
            else
               out_pipe_tkeep(i) <= '1';
            end if;
         end loop;

      --! Packets ends and starts in this transaction
      elsif (in_pipe_sop = '1' and in_pipe_eop = '1') then

         --! SOP before EOP
         if (in_pipe_eop_pos >= ext_sop_pos) then
            for i in 0 to tkeep_width-1 loop
               if i < var_ext_sop_pos then
                  out_pipe_tkeep(i) <= '0';
               elsif (i >= var_ext_sop_pos) and (i <= var_eop_pos) then
                  out_pipe_tkeep(i) <= '1';
               elsif i> var_eop_pos then
                  out_pipe_tkeep(i) <= '0';
               end if;
            end loop;
         --! EOP before SOP
         else
            for i in 0 to tkeep_width-1 loop
               if i <= var_eop_pos then
                  out_pipe_tkeep(i) <= '1';
               elsif (i < var_ext_sop_pos) and (i > var_eop_pos) then
                  out_pipe_tkeep(i) <= '0';
               elsif i >= var_ext_sop_pos then
                  out_pipe_tkeep(i) <= '1';
               end if;
            end loop;
         end if;
      --! If EOP and SOP = '0'
      else
         out_pipe_tkeep <= (others => '1');
      end if;
   end process;

--                       TX_TKEEP SET
-- ----------------------------------------------------------------------------

   --! Merging data to AXI pipe
   out_pipe_axi_data_in <= out_pipe_tdata & out_pipe_tkeep & out_pipe_tlast;

   --! Output Pipe
   out_pipe_i : entity work.PIPE
   generic map(
      DATA_WIDTH     => axi_pipe_width,
      USE_OUTREG     => OUT_PIPE_OUTREG,
      FAKE_PIPE      => not OUT_PIPE_EN
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      --! Input interface
      IN_DATA      => out_pipe_axi_data_in,
      IN_SRC_RDY   => out_pipe_tvalid,
      IN_DST_RDY   => out_pipe_tready,
      --! Output interface
      OUT_DATA     => out_pipe_axi_data_out,
      OUT_SRC_RDY  => TX_TVALID,
      OUT_DST_RDY  => TX_TREADY
   );
   TX_TDATA <= out_pipe_axi_data_out(axi_pipe_width-1 downto (DATA_WIDTH/8)+1);
   TX_TKEEP <= out_pipe_axi_data_out((DATA_WIDTH/8) downto 1);
   TX_TLAST <= out_pipe_axi_data_out(0);

end architecture;

