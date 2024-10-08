-- clk_gen.vhd: Clock generation entity
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Jan Korenek korenek@liberouter.org
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--       - Do the behavioral and after PAR tests
--       - Add to top level entity

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;


-- ----------------------------------------------------------------------
--         Entity : clk_gen
-- ----------------------------------------------------------------------
entity CLK_GEN is
   Port (
      -- =======
      -- Input
      -- =======

      -- Input clock freqvency (50MHz)
      CLK50_IN    : in  std_logic;
      -- Global reset signal
      RESET       : in  std_logic;
      -- =======
      -- Output
      -- =======

      -- 25MHz  output clock
      CLK25       : out std_logic;
      -- 25MHz  output clock (90' phase shift)
      CLK25_PH90  : out std_logic;
      -- 50MHz  output clock
      CLK50_OUT   : out std_logic;
      -- 50MHz  output clock (90' phase shift)
      CLK50_PH90  : out std_logic;
      -- 50MHz  output clock (180' phase shift)
      CLK50_PH180 : out std_logic;
      -- 100MHz output clock
      CLK100      : out std_logic;
      -- 100MHz output clock (180' phase shift)
      CLK100_PH180: out std_logic;
      -- 200MHz output clock
      CLK200      : out std_logic;
      LOCK        : out std_logic
   );
end clk_gen;

-- ----------------------------------------------------------------------
--         Architecture : behavioral
-- ----------------------------------------------------------------------
architecture full of CLK_GEN is

-- Component : Twice multiply freqvency
component clk2x_mod is
   port (
      CLK_IN      : in std_logic;
      RST         : in std_logic;
      CLK1X       : out std_logic;
      CLK1X_PH90  : out std_logic;
      CLK1X_PH180 : out std_logic;
      CLK2X       : out std_logic;
      CLK2X_PH180 : out std_logic;
      CLK2DV      : out std_logic;
      CLK2DV_PH90 : out std_logic;
      CLK4X       : out std_logic;
      LOCK        : out std_logic
   );
end component;

-- component clk4x_mod is
--    port (
--       CLK_IN    : in std_logic;
--       RST       : in std_logic;
--       CLK4X     : out std_logic;
--       LOCK      : out std_logic
--    );
-- end component;

signal clk50x100_lock : std_logic;
signal clk200_lock : std_logic;

-- ----------------------------------------------------------------------
begin

-- 100MHz generation component
CLK100_U : clk2x_mod
port map (
   CLK_IN      => CLK50_IN,
   RST         => RESET,
   CLK1X       => CLK50_OUT,
   CLK1X_PH90  => CLK50_PH90,
   CLK1X_PH180 => CLK50_PH180,
   CLK2X       => CLK100,
   CLK2X_PH180 => CLK100_PH180,
   CLK2DV      => CLK25,
   CLK2DV_PH90 => CLK25_PH90,
   CLK4X       => CLK200,
   LOCK        => clk50x100_lock
);

-- 200MHz generation component
-- CLK200_U : clk4x_mod
-- port map (
--    CLK_IN => CLK50_IN,
--    RST    => RESET,
--    CLK4X  => CLK200,
--    LOCK   => clk200_lock
-- );

LOCK <= clk50x100_lock; -- and clk200_lock;

end full;
-- ----------------------------------------------------------------------
