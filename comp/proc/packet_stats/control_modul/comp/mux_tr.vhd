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

entity MUX_TR is
   generic(
      ADDRESS_WIDTH     : integer := 10
   );
   port(
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      MI_RM_ADDR        : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      MI_RM_RD_ENABLE   : in  std_logic;
      MI_RM             : in  std_logic;
      MI_RM_ARDY        : out std_logic;

      SEL               : in  std_logic;

      FLT_RM_ADDR       : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      FLT_RM_RD_ENABLE  : in std_logic;
      FLT_RM_REQ        : in std_logic;

      RM_ADDRESS        : out std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      RM_RD_ENABLE      : out std_logic;
      RM_REQ            : out std_logic

    );
end entity;

architecture full of MUX_TR is
begin

   RM_ADDRESS <= FLT_RM_ADDR when SEL = '1' else
                 MI_RM_ADDR;

   RM_RD_ENABLE <= FLT_RM_RD_ENABLE when SEL = '1' else
                   MI_RM_RD_ENABLE;

   RM_REQ <= FLT_RM_REQ when SEL = '1' else
             MI_RM;

   MI_RM_ARDY <= not SEL;

end architecture;
