-- watchdog_arch.vhd: watchdog architecture
-- Copyright (C) 2015 CESNET
-- Author(s): Adam Piecek <xpiece00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--


library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

architecture watchdog of WATCHDOG is
-- output signal of D-type flip-flop register
signal reg_keep_alive   : std_logic;
-- output signal of comparator under edge_det_t process
signal comp_out         : std_logic;
-- reset signal going to couter
signal rst              : std_logic;
--! output value of counter
signal counter_out      : std_logic_vector(COUNTER_WIDTH-1 downto 0);
--! maximum value of counter
signal limit            : std_logic_vector(COUNTER_WIDTH-1 downto 0);
--! input signal to counter
signal ce               : std_logic;
--! the comparison result of the counter and limit signal
signal comp_limit_out   : std_logic;
--! destination and source components are ready to recieve/send the DATA
signal flow_rdy         : std_logic;

   begin
      edge_det_t : if EDGE_DETECT generate
         --! D-type flip-flop
         reg_d : process(CLK)
         begin
            if (CLK'event) and (CLK='1') then
               reg_keep_alive <= KEEP_ALIVE;
            end if;
         end process;

         --! comparator
         comp_out <= '1' when (not KEEP_ALIVE) = reg_keep_alive else '0';

         rst <= RESET or comp_out;
      end generate;

      edge_det_f : if EDGE_DETECT = false generate
         rst <= RESET or KEEP_ALIVE;
      end generate;

     --! set maximum value of counter
     limit <= std_logic_vector(to_unsigned(COUNT-1,limit'length));
      --! counter
      cnt : process(CLK)
      begin
         if (CLK'event) and (CLK='1') then
            if rst = '1' then
               counter_out <= (others => '0');
            elsif ce = '1' then
               counter_out <= counter_out + '1';
            end if;
         end if;
      end process;

      COUNTER  <= counter_out;
      comp_limit_out <= '1' when counter_out = limit else '0';

      timing_t : if TIMING generate
         --! counter counts regardless of if adjacent components are ready
         ce <= (not comp_limit_out);
      end generate;

      timing_f : if TIMING = false generate
         --! if counter hasn't reached the limit and if adjacent components are ready
         --! then counter may be enabled
         flow_rdy <= SRC_RDY_IN and DST_RDY_OUT;
         ce <= (not comp_limit_out) and flow_rdy;
      end generate;


      LOCKED <= comp_limit_out;

      SRC_RDY_OUT <= (not comp_limit_out) and SRC_RDY_IN;
      DST_RDY_IN <= (not comp_limit_out) and DST_RDY_OUT;

      DATA_OUT <= DATA_IN;

   end;
