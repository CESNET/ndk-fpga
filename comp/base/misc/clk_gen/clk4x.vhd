-- clk4x.vhd: Clock generation entity
-- Copyright (C) 2003 CESNET
-- Author(s): Jan Korenek <korenek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
library IEEE;
use IEEE.std_logic_1164.all;
--
-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on

-- -----------------------------------------------------------------------
--                       Entity declaration
-- -----------------------------------------------------------------------
entity clk4x_mod is
port (
   CLK_IN    : in std_logic;
   RST       : in std_logic;
   CLK4X     : out std_logic;
   LOCK      : out std_logic
);
end clk4x_mod;

-- -----------------------------------------------------------------------
--                    Architecture declaration
-- -----------------------------------------------------------------------
architecture behavioral of clk4x_mod is

-- ------------------- Component declaration -----------------------------
component BUFG
port (
   I   : in std_logic;
   O   : out std_logic
);
end component;

component DCM
-- pragma translate_off
generic (
   DFS_FREQUENCY_MODE : string := "LOW";
   CLKFX_DIVIDE : integer := 1;
   CLKFX_MULTIPLY : integer := 4 ;
   STARTUP_WAIT : boolean := FALSE
);
-- pragma translate_on

port (
   CLKIN     : in  std_logic;
   CLKFB     : in  std_logic;
   DSSEN     : in  std_logic;
   PSINCDEC  : in  std_logic;
   PSEN      : in  std_logic;
   PSCLK     : in  std_logic;
   RST       : in  std_logic;
   CLK0      : out std_logic;
   CLK90     : out std_logic;
   CLK180    : out std_logic;
   CLK270    : out std_logic;
   CLK2X     : out std_logic;
   CLK2X180  : out std_logic;
   CLKDV     : out std_logic;
   CLKFX     : out std_logic;
   CLKFX180  : out std_logic;
   LOCKED    : out std_logic;
   PSDONE    : out std_logic;
   STATUS    : out std_logic_vector(7 downto 0)
);
end component;


-- Attributes
attribute DFS_FREQUENCY_MODE : string;
attribute CLKFX_DIVIDE : integer;
attribute CLKFX_MULTIPLY : integer;
attribute STARTUP_WAIT : string;

attribute DFS_FREQUENCY_MODE of U_DCM: label is "LOW";
attribute CLKFX_DIVIDE of U_DCM: label is 1;
attribute CLKFX_MULTIPLY of U_DCM: label is 4;
attribute STARTUP_WAIT of U_DCM: label is "FALSE";

-- Signal Declarations:
signal gnd : std_logic;
signal clk0_w: std_logic;
signal clk1x_w: std_logic;
signal clkfx_w: std_logic;
signal clkf_w: std_logic;

-- -----------------------------------------------------------------------
begin
gnd <= '0';
CLK4X <= clkf_w;

-- DCM Instantiation
U_DCM: DCM
port map (
   CLKIN =>    CLK_IN,
   CLKFB =>    clk1x_w,
   DSSEN =>    gnd,
   PSINCDEC => gnd,
   PSEN =>     gnd,
   PSCLK =>    gnd,
   RST =>      rst,
   CLK0 =>     clk0_w,
   CLKFX =>    clkfx_w,
   LOCKED =>   LOCK
);

-- BUFG Instantiation for CLKFX
U0_BUFG: BUFG
port map (
   I => clkfx_w,
   O => clkf_w
);

-- BUFG Instantiation
U2_BUFG: BUFG
port map (
   I => clk0_w,
   O => clk1x_w
);

end behavioral;
-- -----------------------------------------------------------------------

