--! pipe_ent.vhd
--!
--! \file
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

entity PIPE_DSP is
   generic (
      DATA_WIDTH  : integer := 48;
      --! enable fake pipe
      PIPE_EN     : boolean := true;
      --! use DSP slice or normal registers
      ENABLE_DSP  : boolean := true;
      --! number of registers
      NUM_REGS    : integer := 1
   );
   port (
      --! Clock input
      CLK         : in  std_logic;
      --! Reset input
      RESET       : in  std_logic;
      --! Data input
      DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data output
      DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);
      --! clock enbale for registers
      CE          : in  std_logic
   );
end entity;
