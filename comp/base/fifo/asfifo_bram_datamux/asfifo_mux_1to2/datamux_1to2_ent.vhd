-- datamux_1to2_ent.vhd
--!
--! \file
--! \brief Asynchronous fifo mutiplex in BRAMs for 7series FPGAs
--! \author Ondrej Dujiček <xdujic02@stud.feec.vutbr.cz>
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



--\name  Asfifo module
entity ASFIFO_MUX_1TO2 is
   generic(
      DEVICE                        : string := "7SERIES";
      ALMOST_FULL_OFFSET            : integer := 128;
      ALMOST_EMPTY_OFFSET           : integer := 128;
      OUTPUT_DATA_WIDTH             : integer := 512
   );


   port (
      --! Write interface, all signals synchronous to CLK_WR
      CLK_WR      : in  std_logic;
      RST_WR      : in  std_logic;
      WR          : in  std_logic;
      EOP 			: in  std_logic;
      DI          : in  std_logic_vector(OUTPUT_DATA_WIDTH/2-1 downto 0);
      FULL        : out std_logic;
      AFULL       : out std_logic;

      --! Read interface, all signals synchronous to CLK_RD
      CLK_RD      : in  std_logic;
      RST_RD      : in  std_logic;
      RD          : in  std_logic;
      DO          : out std_logic_vector(OUTPUT_DATA_WIDTH-1 downto 0);
      DO_VLD      : out std_logic;
      DO_VLD_H    : out std_logic;
      EMPTY       : out std_logic;
      AEMPTY      : out std_logic
   );
end entity ASFIFO_MUX_1TO2;
