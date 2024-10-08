--
-- arbitr_unitvhd: Round-robin arbitration unit
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
entity RR_ARBITER_UNIT is
   generic(
      -- minimum is 2
      PORTS                 : integer := 2
   );
   port(
      -- =============
      -- port requerst
      -- =============

      -- request from port
      RQ                    : in std_logic_vector(PORTS-1 downto 0);
      -- change the writer (next writer in round)
      CHNG                  : in std_logic;
      -- this unit is responsible for choosing next writer
      GARANT                : in std_logic;

      -- acknowledgement vector
      ACK                   : out std_logic;
      -- write the ack. vector_vector(PORTS-1 downto 0);
      ACK_W                 : out std_logic

      );
end entity RR_ARBITER_UNIT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture RR_ARBITER_UNIT_ARCH of RR_ARBITER_UNIT is

   type t_sig_ack is array(0 to PORTS-1) of std_logic_vector(PORTS-1 downto 0);
   signal sig_ack : t_sig_ack;

begin

ACK_W <= GARANT and chng;

sig_ack(0) <= RQ;

MASK_G1: for i in 0 to PORTS-2 generate

   MASK_G2: for j in 0 to i generate
      sig_ack(i + 1)(j) <= sig_ack(i)(j);
   end generate;

   MASK_G3: for j in i + 1 to PORTS-1 generate
      sig_ack(i + 1)(j) <= sig_ack(i)(j) and not sig_ack(0)(i);
   end generate;

end generate;

ACK <= (others => '0') when GARANT='0' else sig_ack(PORTS-1);

end architecture RR_ARBITER_UNIT_ARCH;

