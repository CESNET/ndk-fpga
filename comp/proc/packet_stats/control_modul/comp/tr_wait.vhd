-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity WAIT_TR is
   generic(
      ADDRESS_WIDTH  : integer := 10;
      CNT_WIDTH      : integer := 10
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      TR_NUM         : in  std_logic_vector(CNT_WIDTH-1 downto 0);

      IN_ADDR        : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      IN_RM          : in  std_logic;
      IN_RM_ALL      : in  std_logic;
      IN_NEXT        : out std_logic;

      OUT_ADDR       : out std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      OUT_RM         : out std_logic;
      OUT_RM_ALL     : out std_logic;
      OUT_NEXT       : in std_logic
   );
end entity;

architecture FULL of WAIT_TR is
   signal mem_rdy          : std_logic;
   signal cnt_zero         : std_logic;

   signal pipe_IN_ADDR     : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal pipe_IN_RM       : std_logic;
   signal pipe_IN_RM_ALL   : std_logic;

   signal tr_next          : std_logic;
   signal pipe_tr_next     : std_logic;
   signal cnt_rdy          : std_logic;
   signal cnt_end          : std_logic;
begin

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if(RESET = '1') then
            pipe_tr_next <= '1';
            pipe_IN_RM   <= '0';
         else
            pipe_tr_next  <= tr_next;
            if(tr_next = '1') then
               pipe_IN_ADDR   <= IN_ADDR;
               pipe_IN_RM     <= IN_RM;
               pipe_IN_RM_ALL <= IN_RM_ALL;
            end if;
         end if;
      end if;
   end process;

   IN_NEXT <= tr_next;

   process(pipe_tr_next, pipe_IN_RM, cnt_end, OUT_NEXT)
   begin
      tr_next <= pipe_tr_next;
      if(pipe_IN_RM = '1' and pipe_tr_next = '1') then
         tr_next <= '0';
      end if;
      if(cnt_end = '1' and OUT_NEXT = '1') then
         tr_next <= '1';
      end if;
   end process;

   cnt_rdy <= pipe_IN_RM and pipe_tr_next;
   cnt_wait_i : entity work.CNT_WAIT
   generic map(
      CNT_WIDTH => CNT_WIDTH
   )
   port map(
      CLK       => CLK,
      RESET     => RESET,
      TR_NUM    => TR_NUM,
      TR_RDY    => cnt_rdy,
      CNT_END   => cnt_end
   );

   OUT_ADDR <= pipe_IN_ADDR;
   OUT_RM_ALL <= pipe_IN_RM_ALL;
   OUT_RM <= cnt_end and pipe_IN_RM;

end architecture;

