--!
--! \file  dp_bmem_V7_ent.vhd
--! \brief Dual port BRAM for Virtex 7 architecture, entity declaration
--! \author Pavel Benáček <benacek@cesnet.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! \brief Entity of dual port Virtex7 BRAM declaration
entity DP_BRAM_V7 is
   generic (
      --! Input data width
      DATA_WIDTH     : integer := 108;
      --! Address bus width
      ADDRESS_WIDTH  : integer := 10;
      --! Block Ram Type, only 18Kb,36Kb blocks
      BRAM_TYPE      : integer := 36;
      --! What operation will be performed first when both WE and RE are
      --! active? Only for behavioral simulation purpose.
      --! WRITE_FIRST(default) | READ_FIRST | NO_CHANGE
      WRITE_MODE_A   : string := "WRITE_FIRST";
      WRITE_MODE_B   : string := "WRITE_FIRST";
      --! Enable output register
      ENABLE_OUT_REG : boolean := false;
      --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      DEVICE         : string := "7SERIES";
      --! Asserts will report reading of uinitialized items from memory in verification
      DEBUG_ASSERT_UNINITIALIZED : boolean := false
   );
   port (
      --! \name Interface A
      --! Clock A
      CLKA   : in    std_logic;
      --! CLKA sync reset
      RSTA   : in    std_logic := '0';
      --! Pipe enable
      PIPE_ENA : in  std_logic;
      --! Read Enable
      REA    : in    std_logic;
      --! Write enable
      WEA    : in    std_logic;
      --! Address A
      ADDRA  : in    std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Data A In
      DIA    : in    std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data A Valid
      DOA_DV : out   std_logic;
      --! Data A Out
      DOA    : out   std_logic_vector(DATA_WIDTH-1 downto 0);

      --! \name Interface B
      --! Clock B
      CLKB   : in    std_logic;
      --! CLKB sync reset
      RSTB   : in    std_logic := '0';
      --! Pipe enable
      PIPE_ENB : in  std_logic;
      --! Read Enable
      REB    : in    std_logic;
      --! Write enable
      WEB    : in    std_logic;
      --! Address B
      ADDRB  : in    std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Data B In
      DIB    : in    std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data B Valid
      DOB_DV : out   std_logic;
      --! Data B out
      DOB    : out   std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity;
