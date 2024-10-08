--!
--! \file sdp_bmem_V7_ent.vhd
--! \brief Simple dual port BRAM for Virtex 7 architecture, entity declaration
--! \author Martin Spinler <spinler@cesnet.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! \brief Entity of simple dual port Virtex7 BRAM declaration
entity SDP_BRAM_V7 is
   generic (
      --! Input data width
      DATA_WIDTH     : integer := 1;
      --! Address bus width
      ADDRESS_WIDTH  : integer := 19;
      --! Block Ram Type, only 18Kb,36Kb blocks
      BRAM_TYPE      : integer := 36;
      --! Enable output register
      ENABLE_OUT_REG : boolean := false;
      --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      DEVICE         : string := "7SERIES"
   );
   port (
      --! CLK sync reset
      RST    : in    std_logic := '0';

      --! \name Interface A
      --! Clock A
      CLKA   : in    std_logic;
      --! Write enable
      WEA    : in    std_logic;
      --! Address A
      ADDRA  : in    std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Data A In
      DIA    : in    std_logic_vector(DATA_WIDTH-1 downto 0);

      --! \name Interface B
      --! Clock B
      CLKB   : in    std_logic;
      --! Pipe enable
      PIPE_ENB : in  std_logic;
      --! Read Enable
      REB    : in    std_logic;
      --! Address B
      ADDRB  : in    std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Data B Valid
      DOB_DV : out   std_logic;
      --! Data B out
      DOB    : out   std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity;
