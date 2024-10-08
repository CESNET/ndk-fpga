--!
--! \file sp_bram_xilinx_ent.vhd
--! \brief Single port BRAM for Xilinx devices, entity
--! \author Pavel Benáček <benacek@cesnet.cz>
--! \author Jan Kučera <jan.kucera@cesnet.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;


--! \brief Entity of single port Xilinx BRAM declaration
entity SP_BRAM_XILINX is
   generic (
      --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6", "ULTRASCALE".
      DEVICE : string := "ULTRASCALE";

      --! A read operation is implicitly performed to address ADDR combinatorially,
      --! regardless of RE inputs. The data output is than registered each CLK
      --! cycle that EN is asserted.

      --! Input/output data width.
      DATA_WIDTH     : integer := 108;

      --! Address bus width.
      ADDRESS_WIDTH  : integer := 10;

      --! Enable output register.
      ENABLE_OUT_REG : boolean := true;

      --! Asserts will report reading of uinitialized items from memory in verification.
      DEBUG_ASSERT_UNINITIALIZED : boolean := false;

      --! Block RAM type, 18Kb or 36Kb blocks.
      --! - Only for non ULTRASCALE devices (DEVICE /= "ULTRASCALE")!
      BRAM_TYPE      : integer := 36
   );
   port (
      --! Clock.
      CLK : in std_logic;
      --! Output register synchronous reset.
      RST : in std_logic := '0';
      --! Enable.
      PIPE_EN : in std_logic;
      --! Read enable (implicit when PIPE_ENA = '1').
      RE : in std_logic := '1';
      --! Write enable.
      WE : in std_logic;
      --! Address.
      ADDR : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      --! Write data.
      DI : in std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Output data.
      DO : out std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Output data validity.
      DO_DV : out std_logic
   );
end entity;
