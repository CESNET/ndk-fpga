-- align_frame_fsm.vhd: FrameLink Binder Align frame FSM
-- Copyright (C) 2008 CESNET
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_ALIGN_FRAME_FSM is
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      DV             : in  std_logic;
      CNT_ROW_MAX    : in  std_logic;
      EOP            : in  std_logic;
      FIFO_FULL      : in  std_logic;

      -- output signals
      INSERT_IDLE    : out std_logic
   );
end entity FLB_ALIGN_FRAME_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_ALIGN_FRAME_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( BUSY, ALIGN_EOP );

   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin

   -- ------------------ Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= BUSY;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, DV, CNT_ROW_MAX, EOP, FIFO_FULL)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when BUSY =>
         if ( EOP = '1' and CNT_ROW_MAX = '0' and FIFO_FULL = '0' and DV = '1') then
            next_state <= ALIGN_EOP;
         else
            next_state <= BUSY;
         end if;

      -- ---------------------------------------------
      when ALIGN_EOP =>
         if ( CNT_ROW_MAX = '1' and FIFO_FULL = '0' ) then
            next_state <= BUSY;
         else
            next_state <= ALIGN_EOP;
         end if;

   end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, DV, FIFO_FULL, EOP )
   begin

      -- ---------------------------------------------
      -- Initial values
      INSERT_IDLE       <= '0';

      case (present_state) is

      -- ---------------------------------------------
      when BUSY =>
         null;

      -- ---------------------------------------------
      when ALIGN_EOP =>
         INSERT_IDLE    <= '1';

      end case;
   end process output_logic;

end architecture full;
