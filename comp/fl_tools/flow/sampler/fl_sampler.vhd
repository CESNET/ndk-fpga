-- header_rearranger_full.vhd: Full architecture of HEADER REARRANGER unit.
-- Copyright (C) 2008 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use WORK.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: FL SAMPLER
-- ----------------------------------------------------------------------------
entity FL_SAMPLER is
    generic(
       DATA_WIDTH  :   integer:=128;
       MAX_RATE    :   integer:=16 -- Maximum Rate 1:N
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK            : in  std_logic;

      -- global synchronous reset
      RESET          : in  std_logic;

	  -- Sampling RATE 1:N
	  RATE           : in std_logic_vector(log2(MAX_RATE)  - 1 downto 0);
	  -- Discarded packet? (1 = yes, 0 = no)
	  PCKT_DISCARD    : out std_logic;


      -- RX Framelink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX FrameLink interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      TX_REM        : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      TX_SOF_N      : out std_logic;
      TX_EOF_N      : out std_logic;
      TX_SOP_N      : out std_logic;
      TX_EOP_N      : out std_logic;
      TX_SRC_RDY_N  : out std_logic;
      TX_DST_RDY_N  : in  std_logic
   );
end entity FL_SAMPLER;

-- ----------------------------------------------------------------------------
--  Architecture: FL SAMPLER
-- ----------------------------------------------------------------------------
architecture full of FL_SAMPLER is

signal cnt_packet          : std_logic_vector(3 downto 0);
signal mx_dst_rdy_n        : std_logic;
signal tx_src_rdy_n_sig    : std_logic;
signal in_packet           : std_logic;
signal in_packet_reg       : std_logic;

begin
ip_reg : process(RESET, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         in_packet_reg <= '0';
      else
         in_packet_reg <= in_packet;
      end if;
   end if;
end process;

process(RX_EOF_N, RX_SOF_N, RX_SRC_RDY_N, mx_dst_rdy_n)
begin
   if RX_EOF_N = '0' and RX_SRC_RDY_N = '0' and mx_dst_rdy_n = '0' then
      in_packet <= '0';
   elsif RX_SOF_N = '0' and RX_SRC_RDY_N = '0' and mx_dst_rdy_n = '0' then
      in_packet <= '1';
   else
      in_packet <= in_packet_reg;
   end if;
end process;


-------------------------------------------------------------------------------
-- Discarded packet signal register
discard_generator: process(RESET, CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         PCKT_DISCARD <= '0';
      elsif RX_EOF_N = '0' and RX_SRC_RDY_N = '0' and mx_dst_rdy_n = '0' and tx_src_rdy_n_sig = '1' then
         PCKT_DISCARD <= '1';
      else
         PCKT_DISCARD <= '0';
      end if;
   end if;
end process;

-------------------------------------------------------------------------------
-- Passed packet counter
cnt_packetp: process(RESET, CLK)
begin
  if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_packet <= (others => '0');
      else
          if ((cnt_packet = RATE) and (RX_EOF_N = '0') and (RX_SRC_RDY_N = '0') and (mx_dst_rdy_n = '0')) or ((cnt_packet > RATE) and (in_packet = '0')) then
             cnt_packet <= (others => '0');
          else
		     if (RX_EOF_N = '0') and (RX_SRC_RDY_N = '0') and (mx_dst_rdy_n = '0') then
               cnt_packet <= cnt_packet + 1 ;
			 end if;
          end if;
       end if;
    end if;
end process;

-------------------------------------------------------------------------------
-- TX_DST_RDY_N multiplexer
mx_dst_rdy_np: process(cnt_packet,  TX_DST_RDY_N)
begin
   case cnt_packet is
     when conv_std_logic_vector(0,LOG2(MAX_RATE)) => mx_dst_rdy_n <= TX_DST_RDY_N;
     when others => mx_dst_rdy_n <= '0';
    end case;
end process;

RX_DST_RDY_N <= mx_dst_rdy_n ;

-------------------------------------------------------------------------------
-- TX_SRC_RDY_N multiplexer
mx_src_rdy_np: process(cnt_packet,  RX_SRC_RDY_N)
begin
   case cnt_packet is
     when conv_std_logic_vector(0,LOG2(MAX_RATE)) => tx_src_rdy_n_sig <= RX_SRC_RDY_N;
     when others => tx_src_rdy_n_sig <= '1';
    end case;
end process;
TX_SRC_RDY_N <= tx_src_rdy_n_sig;

-------------------------------------------------------------------------------
-- Maping other ports
TX_SOF_N <= RX_SOF_N;
TX_SOP_N <= RX_SOP_N;
TX_EOP_N <= RX_EOP_N;
TX_EOF_N <= RX_EOF_N;
TX_DATA  <= RX_DATA;
TX_REM   <= RX_REM;


end architecture full;
