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

entity FILTER_TR is
   generic(
      ADDRESS_WIDTH : integer := 10
   );
   port(
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      FILTER_ADDR       : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      FILTER_RM         : in  std_logic;
      FILTER_RM_ALL     : in  std_logic;
      FILTER_NEXT       : out std_logic;

      RM_ADDRESS        : out std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      RM_RD_ENABLE      : out std_logic;
      RM_REQ            : out std_logic
    );
end entity;

architecture full of FILTER_TR is

   signal pipe_FILTER_ADDR    : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal pipe_FILTER_RM      : std_logic;
   signal pipe_FILTER_RM_ALL  : std_logic;

   signal tr_next             : std_logic;
   signal pipe_tr_next        : std_logic;

   signal one_req_address     : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal one_req_rd_enable   : std_logic;
   signal one_req_rm          : std_logic;

   signal cnt_en              : std_logic;
   signal cnt_value           : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal cnt_zero            : std_logic;

   signal other_req_address   : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal other_req_rd_enable : std_logic;
   signal other_req_rm        : std_logic;

   signal in_tr_enable        : std_logic;
begin

   in_tr_enable <= pipe_FILTER_RM and pipe_tr_next;

   one_req_address   <= pipe_FILTER_ADDR;
   one_req_rm        <= in_tr_enable when pipe_FILTER_RM_ALL = '0' else
                        '0';

   cnt_en   <= in_tr_enable and pipe_FILTER_RM_ALL;
   cnt_zero <= '1' when cnt_value = conv_std_logic_vector(0, cnt_value'length) else
               '0';

   FILTER_NEXT <= tr_next;

   process(pipe_tr_next, other_req_rm, cnt_en, in_tr_enable)
   begin
      tr_next <= pipe_tr_next;
      if(in_tr_enable = '1') then
         tr_next <= '0';
      end if;
      if(other_req_rm = '0' and cnt_en = '0') then
         tr_next <= '1';
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if(RESET = '1') then
            pipe_FILTER_RM <= '0';
            pipe_tr_next   <= '1';
         else
            pipe_FILTER_ADDR    <= FILTER_ADDR;
            pipe_FILTER_RM      <= FILTER_RM;
            pipe_FILTER_RM_ALL  <= FILTER_RM_ALL;
            pipe_tr_next        <= tr_next;
         end if;
      end if;
   end process;

   other_req_rd_enable  <= '0';
   other_req_address    <= cnt_value;

   process(CLK)
   begin
      if (CLK'event) and (CLK = '1') then
         if RESET = '1' then
            cnt_value <= (others => '0');
            other_req_rm <= '0';
         elsif(cnt_en = '1') then
            cnt_value <= (others => '1');
            other_req_rm <= '1';
         elsif(cnt_zero = '0') then
            cnt_value <= cnt_value - 1;
         else
            other_req_rm <= '0';
         end if;
      end if;
   end process;

   RM_ADDRESS <= one_req_address when other_req_rm = '0' else
                 other_req_address;
   RM_RD_ENABLE <= '0';
   RM_REQ <= one_req_rm when other_req_rm = '0' else
             '1';

end architecture;
