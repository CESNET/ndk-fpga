
--
-- DP_URAM_XILINX.vhd: Dual port UltraRAM component
-- Copyright (C) 2004 CESNET
-- Author(s): Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
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
use IEEE.numeric_std.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity DP_URAM_XILINX is
   generic(
          --! Select target device "BEHAVIORAL", "ULTRASCALE".
         DEVICE : string := "BEHAVIORAL";
         --! Input/output data width.
         DATA_WIDTH     : integer := 72;
         --! Address bus width.
         ADDRESS_WIDTH  : integer := 12;
         --! Enables additional output registers. WARNING! May cause request loss if PIPE_EN is '0'
         ADDITIONAL_REG   : integer := 0;
         --! Enable one additional internal register
         INTERNAL_OUT_REG   : boolean := true;
         --! Enable output register.
         EXTERNAL_OUT_REG : boolean := false;
         --! ENable reporting of uninitialized memory
         DEBUG_ASSERT_UNINITIALIZED : boolean := false
   );
   port(
   --UltraRAM common clock
      CLK : in std_logic;
   --! PORT A MAP.
      --! Output registers synchronous reset for Port A.
      RSTA : in std_logic := '0';
      --! Port A enable.
      PIPE_ENA : in std_logic;
      --! Port A read enable (implicit when PIPE_ENA = '1').
      REA : in std_logic := '1';
      --! Port A write enable.
      WEA : in std_logic;
      --! Port A address.
      ADDRA : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Port A write data.
      DIA : in std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Port A output data.
      DOA : out std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Port A output data validity.
      DOA_DV : out std_logic;

   --!PORT B MAP.
      --! Output registers synchronous reset for Port B.
      RSTB : in std_logic := '0';
      --! Port B enable.
      PIPE_ENB : in std_logic;
      --! Port B read enable (implicit when PIPE_ENB = '1').
      REB : in std_logic := '1';
         --! Port B write enable.
      WEB : in std_logic;
      --! Port B address.
      ADDRB : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Port B write data.
      DIB : in std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Port B output data.
      DOB : out std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Port B output data validity.
      DOB_DV : out std_logic

   );
end entity DP_URAM_XILINX;
