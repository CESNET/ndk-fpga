
--
-- SP_URAM_XILINX_ent.vhd: Signle port UltraRAM entity declaration
-- Copyright (C) 2018 CESNET
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SP_URAM_XILINX is
   generic(
   --! Select target device "BEHAVIORAL", "ULTRASCALE".
   DEVICE : string := "BEHAVIORAL";
   --! Input/output data width.
   DATA_WIDTH     : integer := 72;
   --! Address bus width.
   ADDRESS_WIDTH  : integer := 12;
   --! What operation will be performed first when both WE and RE are active?
   --! - WRITE_FIRST (default) | READ_FIRST | NO_CHANGE.
   WRITE_MODE     : string := "READ_FIRST";
   --! Enables adding additional registers on output. WARNING! May cause request loss if PIPE_EN is '0'
   ADDITIONAL_REG   : integer := 0;
   --! Enable output register.
   EXTERNAL_OUT_REG : boolean := false;
   --! Enable additional internal register
   INTERNAL_OUT_REG : boolean := true;
   --! Enable reporting of uninitilized memory
   DEBUG_ASSERT_UNINITIALIZED : boolean := false

   );
   port(
   -- Clock
   CLK       : in std_logic;
   -- Reset
   RST       : in std_logic := '1';
   -- Main memory enable
   PIPE_EN   : in std_logic;
   -- Read request
   RE        : in std_logic;
   -- Write enable
   WE        : in std_logic;
   -- Input address
   ADDR      : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   -- Input data
   DI        : in std_logic_vector(DATA_WIDTH-1 downto 0);
   -- Output data
   DO        : out std_logic_vector(DATA_WIDTH-1 downto 0);
   -- Output data validity signal
   DO_DV     : out std_logic
   );
end entity SP_URAM_XILINX;
