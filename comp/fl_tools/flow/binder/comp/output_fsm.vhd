-- output_fsm.vhd: FrameLink Binder Output Block FSM architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- Binder declarations
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_OUTPUT_FSM is
   generic(
      -- Queue choosing policy
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      EOF            : in  std_logic;
      QUEUE_RDY      : in  std_logic;
      EMPTY          : in  std_logic;

      -- output signals
      SET_VALID      : out std_logic;
      CLR_VALID      : out std_logic;
      CLR_READY      : out std_logic;
      NEXT_QUEUE     : out std_logic
   );
end entity FLB_OUTPUT_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_OUTPUT_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( CHOOSE_QUEUE, FIRST_WORD, BUSY );

   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin


   -- ------------------ Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= CHOOSE_QUEUE;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, EOF, QUEUE_RDY, EMPTY)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when CHOOSE_QUEUE =>
         if (QUEUE_RDY = '1') then
            next_state <= FIRST_WORD;
         else
            next_state <= CHOOSE_QUEUE;
         end if;

      -- ---------------------------------------------
      when BUSY =>
         if (EOF = '1' and (QUEUE_RDY = '0' or EMPTY = '1')) then
            next_state <= CHOOSE_QUEUE;
         elsif (EOF = '1') then
            next_state <= FIRST_WORD;
         else
            next_state <= BUSY;
         end if;

      -- ---------------------------------------------
      when FIRST_WORD =>
         if (EOF = '1' and (QUEUE_RDY = '0' or EMPTY = '1')) then
            next_state <= CHOOSE_QUEUE;
         elsif (EOF = '1') then
            next_state <= FIRST_WORD;
         elsif (EMPTY = '1') then
            next_state <= CHOOSE_QUEUE;
         else
            next_state <= BUSY;
         end if;

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process(present_state, QUEUE_RDY, EOF, EMPTY)
   begin

      -- ---------------------------------------------
      -- Initial values
      SET_VALID      <= '0';
      CLR_VALID      <= '0';
      CLR_READY      <= '0';
      NEXT_QUEUE     <= '0';

      case (present_state) is

      -- ---------------------------------------------
      when CHOOSE_QUEUE =>
         SET_VALID      <= QUEUE_RDY;
         NEXT_QUEUE     <= QUEUE_RDY;
         CLR_READY      <= QUEUE_RDY;

      -- ---------------------------------------------
      when BUSY =>
         NEXT_QUEUE     <= EOF and QUEUE_RDY and (not EMPTY);
         CLR_VALID      <= EOF and ((not QUEUE_RDY) or EMPTY);

         if (QUEUE_CHOOSING = round_robin) then
            CLR_READY      <= EOF;
         else
            CLR_READY      <= EOF and EMPTY;
         end if;

      -- ---------------------------------------------
      when FIRST_WORD =>
         NEXT_QUEUE     <= EOF and QUEUE_RDY and (not EMPTY);
         --CLR_VALID      <= EOF and ((not QUEUE_RDY) or EMPTY);
         CLR_VALID      <= (EOF and (not QUEUE_RDY)) or EMPTY;

         if (QUEUE_CHOOSING = round_robin) then
            CLR_READY      <= EOF;
         else
            CLR_READY      <= EOF and EMPTY;
         end if;

      end case;
   end process output_logic;

end architecture full;
