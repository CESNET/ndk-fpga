-- axi2flu.vhd: Top level entity for AXI to FLU converter
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
entity axi2flu is
generic(
   -- data width of input AXI and output FLU interfaces
   DATA_WIDTH : integer := 512;
   --! sop_pos width of output FLU interface (max value = log2(DATA_WIDTH/8))
   --! If other value then log2(DATA_WIDTH/8), start of packet position in TKEEP must
   --! take values with step (DATA_WIDTH/8)/(2^SOP_POS_WIDTH)
   SOP_POS_WIDTH : integer := 6;
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

   --! Common interface
   CLK            : in std_logic;
   RESET          : in std_logic;

   --! AXI input interface
   RX_TDATA      : in std_logic_vector(DATA_WIDTH-1 downto 0);
   RX_TKEEP      : in std_logic_vector((DATA_WIDTH/8)-1 downto 0);
   RX_TVALID     : in std_logic;
   RX_TLAST      : in std_logic;
   RX_TREADY     : out std_logic;

   --! Frame Link Unaligned output interface
   TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
   TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   TX_SOP        : out std_logic;
   TX_EOP        : out std_logic;
   TX_SRC_RDY    : out std_logic;
   TX_DST_RDY    : in std_logic
);
end entity;
-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of axi2flu is

   --! Constant for data width of AXI pipe
   constant   axi_pipe_width : integer := DATA_WIDTH+(DATA_WIDTH/8)+1;
   --! RX_TKEEP width
   constant   tkeep_width    : integer  := DATA_WIDTH/8;
   --! Width of signals out_eop_pos and out_sop_pos
   constant   pos_width      : integer  := log2(DATA_WIDTH/8);

   --! Input pipeline
   signal   in_pipe_tdata    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal   in_pipe_tkeep    : std_logic_vector(tkeep_width-1 downto 0);
   signal   in_pipe_tlast    : std_logic;
   signal   in_pipe_tready   : std_logic;
   signal   in_pipe_tvalid   : std_logic;
   --! Signals for merging data into AXI pipie
   signal   in_pipe_axi_data_in : std_logic_vector(axi_pipe_width-1 downto 0);
   signal   in_pipe_axi_data_out : std_logic_vector(axi_pipe_width-1 downto 0);

   --! Output pipeline
   signal   out_pipe_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal   out_pipe_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal   out_pipe_eop_pos    : std_logic_vector(pos_width-1 downto 0);
   signal   out_pipe_sop        : std_logic;
   signal   out_pipe_eop        : std_logic;
   signal   out_pipe_src_rdy    : std_logic;
   signal   out_pipe_dst_rdy    : std_logic;

   --! Signal for detection EOP when next packet starts in next transaction
   signal	eop_int 	: std_logic;
   --! If '1' then in last transaction has ended packet and hasn't started new
   signal	reg_eop_int 	: std_logic;

   --! Internal signals
   signal	out_sop		: std_logic;
   signal	out_sop_pos	: std_logic_vector(pos_width-1 downto 0);
   signal	out_eop_pos	: std_logic_vector(pos_width-1 downto 0);
   --! Signal for detection if RX_TKEEP = (others=>'1')
   signal   whole_last  : std_logic;

begin

   --! Merging data into AXI pipe
   in_pipe_axi_data_in <= RX_TDATA & RX_TKEEP & RX_TLAST;

   --! Input Pipe
   in_pipe_i : entity work.PIPE
   generic map(
      DATA_WIDTH     => axi_pipe_width,
      USE_OUTREG     => IN_PIPE_OUTREG,
      FAKE_PIPE      => not IN_PIPE_EN
   )
   port map(

      CLK         => CLK,
      RESET       => RESET,
      --! Input interface
      IN_DATA      => in_pipe_axi_data_in,
      IN_SRC_RDY   => RX_TVALID,
      IN_DST_RDY   => RX_TREADY,
      --! Output interface
      OUT_DATA     => in_pipe_axi_data_out,
      OUT_SRC_RDY  => in_pipe_tvalid,
      OUT_DST_RDY  => in_pipe_tready
   );
   in_pipe_tdata <= in_pipe_axi_data_out(axi_pipe_width-1 downto (DATA_WIDTH/8)+1);
   in_pipe_tkeep <= in_pipe_axi_data_out((DATA_WIDTH/8) downto 1);
   in_pipe_tlast <= in_pipe_axi_data_out(0);


   --! Connection and conversion
   out_pipe_data    <= in_pipe_tdata;
   out_pipe_src_rdy <= in_pipe_tvalid;
   in_pipe_tready   <= out_pipe_dst_rdy;
   out_pipe_eop     <= in_pipe_tlast;
   out_pipe_sop     <= out_sop;
   out_pipe_sop_pos <= out_sop_pos(pos_width-1 downto pos_width-SOP_POS_WIDTH);
   out_pipe_eop_pos <= out_eop_pos;

   process(CLK,RESET)
   begin
      if (rising_edge(CLK)) then
         if RESET='1' then
            reg_eop_int <= '1';
         else
            reg_eop_int <= eop_int;
         end if;
      end if;
   end process;


-- ----------------------------------------------------------------------------
--                        TX_SOP SET

   process(in_pipe_tvalid,in_pipe_tkeep,out_pipe_dst_rdy,in_pipe_tlast,reg_eop_int, out_eop_pos)
   begin
      --! If transaction
      if (in_pipe_tvalid and out_pipe_dst_rdy)='1' then
         --! If last transaction and end of packet is on the last byte
         if(in_pipe_tlast='1' and out_eop_pos=(tkeep_width-1)) then
            eop_int <= '1';
         else
            eop_int  <= in_pipe_tlast and not in_pipe_tkeep(tkeep_width-1);
         end if;
      else
         eop_int  <= reg_eop_int;
      end if;
   end process;

   --! Detection if RX_TKEEP = (others => '1')
   process(in_pipe_tkeep)
   begin
      whole_last <= '1';
      for i in 0 to tkeep_width-1 loop
         if in_pipe_tkeep(i)='0' then
            whole_last <= '0';
         end if;
      end loop;
   end process;
   --! out_sop='1' when in previous transaction has ended packet and doesn't start new
   --! or in current transaction ended packet and started new
   out_sop <= reg_eop_int or (in_pipe_tlast and in_pipe_tkeep(tkeep_width-1) and not whole_last);

--                          TX_SOP SET
-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------
--                  TX_SOP_POS AND TX_EOP_POS SET

   process(in_pipe_tkeep, whole_last)
   begin
         out_sop_pos <= (others => '0');
         out_eop_pos <= (others => '0');
         for i in 1 to tkeep_width-1 loop
            --! If start of packet on first byte
            if (i=1 and in_pipe_tkeep(0)='1') then
               out_sop_pos <= conv_std_logic_vector(i-1, pos_width);
            --! Detect start of packet in other cases
            elsif (in_pipe_tkeep(i)='1' and in_pipe_tkeep(i-1)='0') then
               out_sop_pos <= conv_std_logic_vector(i, pos_width);
            end if;
            --! If end of packet on last byte and (SOP='0' or packet starts on first byte)
            if (whole_last='1') then
               out_eop_pos <= conv_std_logic_vector(tkeep_width-1, pos_width);
            --! If end of packet on last byte and SOP='1'
            elsif (in_pipe_tkeep(tkeep_width-1)='1' and in_pipe_tkeep(0)='0') then
               out_eop_pos <= conv_std_logic_vector(tkeep_width-1, pos_width);
            --! Detect end of packet in other cases
            elsif (in_pipe_tkeep(i)='0' and in_pipe_tkeep(i-1)='1') then
               out_eop_pos <= conv_std_logic_vector(i-1, pos_width);
            end if;
         end loop;
   end process;

--                  TX_SOP_POS AND TX_EOP_POS SET
-- ----------------------------------------------------------------------------

   -- Output Pipe (FLU)
   out_pipe_i : entity work.FLU_PIPE
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,
      USE_OUTREG     => OUT_PIPE_OUTREG,
      FAKE_PIPE      => not OUT_PIPE_EN
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      -- Input interf
      RX_DATA       => out_pipe_data,
      RX_SOP_POS    => out_pipe_sop_pos,
      RX_EOP_POS    => out_pipe_eop_pos,
      RX_SOP        => out_pipe_sop,
      RX_EOP        => out_pipe_eop,
      RX_SRC_RDY    => out_pipe_src_rdy,
      RX_DST_RDY    => out_pipe_dst_rdy,
      -- Output interf
      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY
   );
end architecture;
