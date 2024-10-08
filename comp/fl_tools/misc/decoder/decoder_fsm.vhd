-- decoder_fsm.vhd: main FSM
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_DEC_FSM is
   generic(
      HEADER      : boolean;
      FOOTER      : boolean
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- input signals
      EOP         : in  std_logic;
      EOF         : in  std_logic;

      -- output signals
      PART        : out std_logic_vector(1 downto 0)
   );
end entity FL_DEC_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_DEC_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_HEADER, S_PAYLOAD, S_FOOTER );

   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin

   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK)
   begin
      if (RESET = '1') then
         if (HEADER) then
            present_state <= S_HEADER;
         else
            present_state <= S_PAYLOAD;
         end if;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, EOP, EOF)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_HEADER =>
         if (EOP = '1') then
            next_state <= S_PAYLOAD;
         else
            next_state <= S_HEADER;
         end if;

      -- ---------------------------------------------
      when S_PAYLOAD =>
         if (EOF = '1') then
            if (HEADER) then
               next_state <= S_HEADER;
            else
               next_state <= S_PAYLOAD;
            end if;
         elsif (EOP = '1') then
            if (FOOTER) then
               next_state <= S_FOOTER;
            else
               next_state <= S_PAYLOAD;
            end if;
         else
            next_state <= S_PAYLOAD;
         end if;

      -- ---------------------------------------------
      when S_FOOTER =>
         if (EOP = '1') then
            if (HEADER) then
               next_state <= S_HEADER;
            else
               next_state <= S_PAYLOAD;
            end if;
         else
            next_state <= S_FOOTER;
         end if;

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state )
   begin

      -- ---------------------------------------------
      -- Initial values
      PART           <= "00";

      case (present_state) is

      -- ---------------------------------------------
      when S_HEADER =>
         PART        <= "00";

      -- ---------------------------------------------
      when S_PAYLOAD =>
         PART        <= "01";

      -- ---------------------------------------------
      when S_FOOTER =>
         PART        <= "10";

      end case;
   end process output_logic;

end architecture full;
