-- frame_counter.vhd: Frame Counter komponent
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_FRAME_COUNTER is
   generic(
      COUNTER_WIDTH  : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      INC            : in std_logic;
      DEC            : in std_logic;

      -- output interface
      FRAME_RDY      : out std_logic
   );
end entity FLB_FRAME_COUNTER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FLB_FRAME_COUNTER is
   -- constants
   constant CNT_FRAMES_CMP1 : std_logic_vector(COUNTER_WIDTH-1 downto 0)
                           := (others => '0');
   constant CNT_FRAMES_CMP2 : std_logic_vector(COUNTER_WIDTH-1 downto 0)
                           := conv_std_logic_vector(1, COUNTER_WIDTH);

   -- counters
   signal cnt_frames       : std_logic_vector(COUNTER_WIDTH-1 downto 0);
   signal cnt_frames_ce    : std_logic;
   signal cnt_frames_dir   : std_logic;

   -- registers
   signal reg_frame_rdy    : std_logic;
   signal reg_frame_rdy_we : std_logic;
   signal reg_frame_rdy_in : std_logic;

begin
   -- output signals
   reg_frame_rdy_in <= INC and (not DEC);
   reg_frame_rdy_we <=
         '1' when ((cnt_frames = CNT_FRAMES_CMP1) and INC = '1')
         or ((cnt_frames = CNT_FRAMES_CMP2) and DEC = '1' and INC = '0')
         else '0';

   -- counter control signals
   cnt_frames_ce  <= INC xor DEC;
   cnt_frames_dir <= INC;

   -- output signals
   FRAME_RDY      <= reg_frame_rdy;

   -- ------------------ counter cnt_frames -----------------------------------
   cnt_framesp: process (CLK)
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then
            cnt_frames <= (others => '0');
         elsif cnt_frames_ce = '1' then
            if cnt_frames_dir = '1' then
               cnt_frames <= cnt_frames + 1;
            else
               cnt_frames <= cnt_frames - 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------ register cnt_frames -----------------------------------
   reg_frame_rdyp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_frame_rdy <= '0';
         elsif (reg_frame_rdy_we = '1') then
            reg_frame_rdy <= reg_frame_rdy_in;
         end if;
      end if;
   end process;

end architecture behavioral;

