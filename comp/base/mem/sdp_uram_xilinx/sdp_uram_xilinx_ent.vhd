
--
-- SDP_URAM_XILINX.vhd: Simple dual port UltraRAM
-- Copyright (C) 2018 CESNET
-- Author(s): Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>--
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
entity SDP_URAM_XILINX is
   generic(
          --! Select target device "BEHAVIORAL", "ULTRASCALE".
         DEVICE : string := "BEHAVIORAL";
          --! A read operation is implicitly performed to address ADDR[A|B] combinatorially,
          --! regardless of RE[A|B] inputs. The data output is than registered each CLK[A|B]
          --! cycle that EN[A|B] is asserted.
         --! Input/output data width.
         DATA_WIDTH     : integer := 72;
         --! Address bus width.
         ADDRESS_WIDTH  : integer := 12;
          --! What operation will be performed first when both WE and RE are active?
         --! - WRITE_FIRST (default) | READ_FIRST | NO_CHANGE.
         WRITE_MODE   : string := "READ_FIRST";
         --! Number of pipeline stages in read data path; >= 1.
         ADDITIONAL_REG  : integer := 0;
         --! Enable output register.
         EXTERNAL_OUT_REG : boolean := false;
         --! Enable internal register
         INTERNAL_OUT_REG : boolean := false;
         --! Enable reporting of uninitialized memory
         DEBUG_ASSERT_UNINITIALIZED : boolean := false
          );
   port(
         --! Port A clock.
         CLK : in std_logic;
         --! Port A enable (implicit for this port).
         PIPE_EN : in std_logic := '1';
         --! Port A write enable.
         WEA : in std_logic;
         --! Port A address.
         ADDRA : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
         --! Port A write data.
         DIA : in std_logic_vector(DATA_WIDTH-1 downto 0);
         --! Port B clock.
         RSTB : in std_logic := '0';
         --! Port B enable.
         REB : in std_logic := '1';
         --! Port B address.
         ADDRB : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
         --! Port B output data.
         DOB : out std_logic_vector(DATA_WIDTH-1 downto 0);
         --! Port B output data validity.
         DOB_DV : out std_logic

   );
end entity SDP_URAM_XILINX;
