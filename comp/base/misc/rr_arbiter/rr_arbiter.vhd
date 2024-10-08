--
-- arbitr_rr.vhd: Round robin priority decoder
-- Copyright (C) 2006 CESNET
-- Author(s): Patrik Beck <beck@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
-------------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity RR_ARBITER is
   generic(
      PORTS                 : integer := 2
   );
   port(
      -- ============
      -- FPGA control
      -- ============

      -- 100  MHz FPGA clock
      CLK                   : in  std_logic;
      -- Reset
      RESET                 : in  std_logic;
      -- Enable
      ENABLE                : in  std_logic;

      -- ===============
      -- Input Interface
      -- ===============

      RQ                    : in  std_logic_vector(PORTS-1 downto 0);
      -- ================
      -- Output Interface
      -- ================

      ACK                   : out std_logic_vector(PORTS-1 downto 0)
   );
end entity RR_ARBITER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture RR_ARBITER_ARCH of RR_ARBITER is

   -- priority counter registers
   signal priority_reg     : std_logic_vector(PORTS-1 downto 0);
   signal change_priority  : std_logic;
   signal sig_idle         : std_logic;

   signal ack_we           : std_logic;
   signal sig_ack          : std_logic_vector(PORTS-1 downto 0);

   signal sig_arb_w        : std_logic_vector(PORTS-1 downto 0);
   type t_sig_arb_ack is array(0 to PORTS-1) of std_logic_vector(PORTS-1 downto 0);
   signal sig_arb_ack      : t_sig_arb_ack;
   signal sig_arb_ack_out  : t_sig_arb_ack;
   signal sig_arb_rq       : t_sig_arb_ack;

begin

sig_idle <= '1' when RQ = conv_std_logic_vector(0, PORTS) else '0';

change_priority <= ENABLE and not sig_idle;

-- register priority_reg0 ------------------------------------------------------
priority_regp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         priority_reg <= conv_std_logic_vector(1, PORTS);
      elsif (ack_we = '1') then
         priority_reg <= sig_ack;
      end if;
   end if;
end process;

ACK <= sig_ack when ENABLE = '1' else (others => '0');

ARB_G: for i in 0 to PORTS-1 generate
   A_UNIT : entity work.RR_ARBITER_UNIT
      generic map(
         PORTS       => PORTS
      )
      port map(
         RQ          => sig_arb_rq(i),
         CHNG        => change_priority,
         GARANT      => priority_reg(i),

         ACK         => sig_arb_ack_out(i),
         ACK_W       => sig_arb_w(i)
      );
end generate;

ack_we <= '0' when sig_arb_w = conv_std_logic_vector(0, PORTS) else '1';

RQ_MAP1: for i in 0 to PORTS-1 generate

   RQ_MAP2: for j in i + 1 to i + PORTS generate
      sig_arb_rq(i)(j - (i + 1)) <= RQ(j REM PORTS);
      sig_arb_ack(j REM PORTS)(i) <= sig_arb_ack_out(i)(j - (i + 1));
   end generate;

end generate;

ACK_MAP1: for i in 0 to PORTS-1 generate
   sig_ack(i) <= '0' when sig_arb_ack(i) = conv_std_logic_vector(0, PORTS) else '1';
end generate;

end architecture RR_ARBITER_ARCH;

