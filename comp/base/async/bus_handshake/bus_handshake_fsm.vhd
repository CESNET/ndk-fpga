--!
--! bus_handshake_fsm.vhd: FSM for BUS Handshake
--! Copyright (C) 2014 CESNET
--! Author(s): Jakub Cabal <cabal@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!
--! TODO:

library IEEE;
use IEEE.std_logic_1164.all;

   --! -------------------------------------------------------------------------
   --!                      Entity declaration
   --! -------------------------------------------------------------------------

entity BUS_HANDSHAKE_FSM is
   Port (
      CLK       : in  STD_LOGIC;    --! Clock
      RST       : in  STD_LOGIC;    --! Reset
      ACK       : in  STD_LOGIC;    --! Signal ACK
      EVENT     : in  STD_LOGIC;    --! Signal EVENT
      READY     : out STD_LOGIC     --! Signal READY
   );
end BUS_HANDSHAKE_FSM;

   --! -------------------------------------------------------------------------
   --!                      Architecture declaration
   --! -------------------------------------------------------------------------

architecture FULL of BUS_HANDSHAKE_FSM is

   --! -------------------------------------------------------------------------
   --!                      SIGNALS
   --! -------------------------------------------------------------------------

   type state is (st0,st1);
   signal present_st : state := st0;
   signal next_st    : state;

--! -------------------------------------------------------------------------
begin
--! -------------------------------------------------------------------------

   --! Present State register
   present_state_reg: process(CLK)
      begin
      if (rising_edge(CLK)) then
         if (RST='1') then
            present_st <= st0;
         else
            present_st <= next_st;
         end if;
      end if;
   end process;

   --! Next State logic
   next_state_logic: process (present_st, ACK, EVENT)
   begin
      case present_st is

         --! STATE st0
         when st0 =>

            if (EVENT = '1') then
               next_st <= st1;
            else
               next_st <= st0;
            end if;

         --! STATE st1
         when st1 =>

            if (ACK = '1') then
               next_st <= st0;
            else
               next_st <= st1;
            end if;

         --! Others STATE
         when others => null;

      end case;
   end process;

   --! Output logic
   output_logic: process (present_st)
   begin
      case present_st is

         --! STATE st0
         when st0 =>

            READY <= '1';

         --! STATE st1
         when st1 =>

            READY <= '0';

         --! Others STATE
         when others => null;

      end case;
   end process;

end architecture FULL;
