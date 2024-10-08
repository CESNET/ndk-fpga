--   clk2x.vhd : Twice multiply clock generation
--   Copyright (C) 2003 CESNET
--   Author(s): Jan Korenek <korenek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO list :
--
--
--

library IEEE;
use IEEE.std_logic_1164.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on

-- ------------------------------------------------------------------------
--         Entity : BUFG_CLK2X_SUBM
-- ------------------------------------------------------------------------

entity CLK2X_MOD is
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
end clk2x_mod;

-- ------------------------------------------------------------------------
--         Architecture : BUFG_CLK2X_SUBM_arch
-- ------------------------------------------------------------------------

architecture behavioral of clk2x_mod is

-- Components Declarations:
component BUFG
   port (
      I   : in std_logic;
      O   : out std_logic
   );
end component;

component DCM
   -- pragma translate_off
   generic (
      DLL_FREQUENCY_MODE : string := "LOW";
      DUTY_CYCLE_CORRECTION : boolean := TRUE;
      STARTUP_WAIT : boolean := FALSE;
      CLKDV_DIVIDE : real := 2.0;
      CLKFX_MULTIPLY : integer := 4
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
attribute DLL_FREQUENCY_MODE     : string;
attribute DUTY_CYCLE_CORRECTION  : string;
attribute STARTUP_WAIT           : string;
attribute CLKDV_DIVIDE           : real;
attribute CLKIN_PERIOD           : real;
attribute CLKFX_MULTIPLY         : integer;

attribute DLL_FREQUENCY_MODE of U_DCM0: label is "LOW";
attribute DUTY_CYCLE_CORRECTION of U_DCM0: label is "TRUE";
attribute STARTUP_WAIT of U_DCM0: label is "FALSE";
attribute CLKDV_DIVIDE of U_DCM0: label is 2.0;
attribute CLKIN_PERIOD of U_DCM0: label is 20.0;
attribute CLKFX_MULTIPLY of U_DCM0: label is 4;

attribute DLL_FREQUENCY_MODE of U_DCM1: label is "LOW";
attribute DUTY_CYCLE_CORRECTION of U_DCM1: label is "TRUE";
attribute STARTUP_WAIT of U_DCM1: label is "FALSE";
attribute CLKDV_DIVIDE of U_DCM1: label is 2.0;


-- -----------------------------------------------------------------------
-- Signal Declarations:
constant gnd         : std_logic := '0';

signal dcm0_clk0_buf : std_logic;
signal dcm0_clk0     : std_logic;
signal dcm0_clk90    : std_logic;
signal dcm0_clk180   : std_logic;
signal dcm0_clk2x    : std_logic;
signal dcm0_clk2x180 : std_logic;
signal dcm0_clkdv    : std_logic;
signal dcm0_clkdv_buf: std_logic;
signal dcm0_clk4x    : std_logic;
signal dcm0_clk4x_buf: std_logic;
signal dcm0_lock     : std_logic;

signal reg1_dcm1rst  : std_logic;
signal reg2_dcm1rst  : std_logic;
signal reg3_dcm1rst  : std_logic;
signal dcm1_clk0_buf : std_logic;
signal dcm1_clk0     : std_logic;
signal dcm1_clk90    : std_logic;
signal dcm1_clk90_buf: std_logic;
signal dcm1_lock     : std_logic;

begin

-- ---------------- DCM0 Instantion ------------------
U_DCM0: DCM
   -- pragma translate_off
   generic map (
      DLL_FREQUENCY_MODE =>  "LOW",
      DUTY_CYCLE_CORRECTION => TRUE,
      STARTUP_WAIT =>  FALSE,
      CLKDV_DIVIDE => 2.0
   )
   -- pragma translate_on
   port map (
      CLKIN    => CLK_IN,
      CLKFB    => dcm0_clk0_buf,
      DSSEN    => gnd,
      PSINCDEC => gnd,
      PSEN     => gnd,
      PSCLK    => gnd,
      RST      => RST,
      CLK0     => dcm0_clk0,
      CLK90    => dcm0_clk90,
      CLK180   => dcm0_clk180,
      CLK2X    => dcm0_clk2x,
      CLK2X180 => dcm0_clk2x180,
      CLKFX    => dcm0_clk4x,
      CLKDV    => dcm0_clkdv,
      LOCKED   => dcm0_lock
   );

-- BUFG Instantiation
BUFG2X_U : BUFG
   port map (
      I => dcm0_clk2x,
      O => CLK2X
   );

-- BUFG Instantiation
BUFG2XPH180_U : BUFG
   port map (
      I => dcm0_clk2x180,
      O => CLK2X_PH180
   );

-- BUFG Instantiation
BUFG1X_U : BUFG
   port map (
      I => dcm0_clk0,
      O => dcm0_clk0_buf
   );

-- BUFG Instantiation
BUFG1XPH90_U : BUFG
   port map (
      I => dcm0_clk90,
      O => CLK1X_PH90
   );

-- BUFG Instantiation
BUFG1XPH180_U : BUFG
   port map (
      I => dcm0_clk180,
      O => CLK1X_PH180
   );

-- BUFG Instantiation
BUFDV_IN_U : BUFG
   port map (
      I => dcm0_clkdv,
      O => dcm0_clkdv_buf
   );

-- BUFG Instantiation
BUFFX_IN_U : BUFG
   port map (
      I => dcm0_clk4x,
      O => dcm0_clk4x_buf
   );


-- ---------------- DCM1 Instantion ------------------
-- reg_dcmrst register
process(RST, dcm0_clkdv_buf)
begin
   if (RST = '1') then
      reg1_dcm1rst <= '1';
      reg2_dcm1rst <= '1';
      reg3_dcm1rst <= '1';
   elsif (dcm0_clkdv_buf'event AND dcm0_clkdv_buf = '1') then
         reg1_dcm1rst <= not dcm0_lock;
         reg2_dcm1rst <= reg1_dcm1rst;
         reg3_dcm1rst <= reg2_dcm1rst;
   end if;
end process;

-- DCM Instantiation
U_DCM1: DCM
   -- pragma translate_off
   generic map (
      DLL_FREQUENCY_MODE =>  "LOW",
      DUTY_CYCLE_CORRECTION => TRUE,
      STARTUP_WAIT =>  FALSE,
      CLKDV_DIVIDE => 2.0
   )
   -- pragma translate_on
   port map (
      CLKIN =>    dcm0_clkdv_buf,
      CLKFB =>    dcm1_clk0_buf,
      DSSEN =>    gnd,
      PSINCDEC => gnd,
      PSEN =>     gnd,
      PSCLK =>    gnd,
      RST =>      reg3_dcm1rst,
      CLK0 =>     dcm1_clk0,
      CLK90=>     dcm1_clk90,
      LOCKED =>   dcm1_lock
   );

-- BUFG Instantiation
BUFDV_U : BUFG
   port map (
      I => dcm1_clk0,
      O => dcm1_clk0_buf
   );

-- BUFG Instantiation
BUFDV_PHU : BUFG
   port map (
      I => dcm1_clk90,
      O => dcm1_clk90_buf
   );

-- Interface mapping
CLK1X       <= dcm0_clk0_buf;
CLK2DV      <= dcm1_clk0_buf;
CLK2DV_PH90 <= dcm1_clk90_buf;
CLK4x       <= dcm0_clk4x_buf;
LOCK        <= dcm1_lock;

end behavioral;

