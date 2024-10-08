--
-- sh_fifo_fsm.vhd: Shift-registers FIFO FSM
--
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Mikusek <petr.mikusek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sh_fifo_fsm is
   port (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      WE             : in  std_logic;
      RE             : in  std_logic;
      CMP_FULL       : in  std_logic;
      CMP_EMPTY      : in  std_logic;

      FULL           : out std_logic;
      EMPTY          : out std_logic;
      CNT_ADDR_CE    : out std_logic;
      CNT_ADDR_DIR   : out std_logic;
      SHREG_CE       : out std_logic
   );
end entity sh_fifo_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sh_fifo_fsm is

   type t_state is (S_RELAY, S_EMPTY, S_FULL);
   -- don't change state order! optimized generation of empty and full signals

   signal present_state, next_state : t_state := S_EMPTY;

begin -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   sync_fsm: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            present_state <= S_EMPTY;
         else
            present_state <= next_state;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   next_state_logic: process(present_state, WE, RE, CMP_FULL, CMP_EMPTY)
   begin
      case (present_state) is
      -- ------------------------------
      when S_EMPTY =>
         next_state <= S_EMPTY;
         if (WE = '1') then
            next_state <= S_RELAY;
         end if;
      -- ------------------------------
      when S_RELAY =>
         next_state <= S_RELAY;
         if (WE = '1' and RE = '0' and CMP_FULL = '1') then
            next_state <= S_FULL;
         elsif (WE = '0' and RE = '1' and CMP_EMPTY = '1') then
            next_state <= S_EMPTY;
         end if;
      -- ------------------------------
      when S_FULL =>
         next_state <= S_FULL;
         if (RE = '1') then
            next_state <= S_RELAY;
         end if;
      -- ------------------------------
      when others =>
         next_state <= S_EMPTY;
      -- ------------------------------
      end case;
   end process;

   -- -------------------------------------------------------------------------
   output_logic: process(present_state, WE, RE, CMP_EMPTY)
   begin
      FULL           <= '0';
      EMPTY          <= '1';
      CNT_ADDR_CE    <= '0';
      CNT_ADDR_DIR   <= not RE; -- down ('0') for reading or relaying
      SHREG_CE       <= '0';

      case (present_state) is
      -- ------------------------------
      when S_EMPTY =>
         FULL           <= '0';
         EMPTY          <= '1';
         CNT_ADDR_CE    <= '0';
         SHREG_CE       <= WE;
      -- ------------------------------
      when S_RELAY =>
         FULL           <= '0';
         EMPTY          <= '0';
         CNT_ADDR_CE    <= WE xor RE;
         SHREG_CE       <= WE;

         if (WE = '0' and RE = '1' and CMP_EMPTY = '1') then
            CNT_ADDR_CE <= '0';
         end if;
      -- ------------------------------
      when S_FULL =>
         FULL           <= '1';
         EMPTY          <= '0';
         CNT_ADDR_CE    <= RE;
         SHREG_CE       <= '0';
      -- ------------------------------
      when others =>
         null;
      -- ------------------------------
      end case;
   end process;

end architecture behavioral;
