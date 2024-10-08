--! mul_dsp_ent.vhd
--!
--! \file
--! \brief entity of MUL_DSP with Virtex-7 DSP slice
--! \ Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! \brief DSP slice MUL_DSP entity
entity MUL_DSP is
   generic (
      --! Maximum 24 bits
      A_DATA_WIDTH   : integer := 10;
      --! N bits
      B_DATA_WIDTH   : integer := 32;
      --! Input pipeline registers (0, 1)
      REG_IN      : integer := 0;
      --! Output pipeline register (0, 1)
      REG_OUT     : integer := 0
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(A_DATA_WIDTH-1 downto 0);
      --! Data input
      B        : in  std_logic_vector(B_DATA_WIDTH-1 downto 0);
      --! Clock enable for pipeline
      CE       : in  std_logic;
      --! Data output
      P        : out std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0)
     );
end entity;

