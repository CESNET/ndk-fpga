-- qdr_bram_ent.vhd
--!
--! \file
--! \brief Small QDR composed of BRAM entity
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2014
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

--! \brief Package with log2 function.
use work.math_pack.all;

Library UNISIM;
use UNISIM.vcomponents.all;
library UNIMACRO;
use unimacro.Vcomponents.all;

--\name  Small QDR composed of BRAM module
entity QDR_BRAM is
   port (
      --! Resets and clocks ----------------------------------------------------
      CLK             : in  std_logic;
      RST             : in  std_logic;

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD           : in  std_logic;
      --! Address for data to write
      USER_WR_ADDR          : in  std_logic_vector(8 downto 0);
      --! Data to write
      USER_WR_DATA          : in  std_logic_vector(143 downto 0);
      --! Data write enable - active low
      USER_WR_BW_N          : in  std_logic_vector(144/9-1 downto 0);
      --! Valid bit for data to read
      USER_RD_CMD           : in  std_logic;
      --! Address for data to read
      USER_RD_ADDR          : in  std_logic_vector(8 downto 0);

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID         : out std_logic;
      --! Already read data
      USER_RD_DATA          : out std_logic_vector(143 downto 0)

   );
end entity;
