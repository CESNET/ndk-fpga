-- hins_ent.vhd
--!
--! \file
--! \brief FLU header insert
--! \author Lukas Kekely <kekely@cesnet.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! Package with log2 function.
use work.math_pack.all;

--\name  FLU header insert entity
entity HINS is
   generic (
      --! \brief Data width of input and output FrameLinkUnaligned data.
      --! \details Must be greater than 8.
      DATA_WIDTH     : integer := 512;
      SOP_POS_WIDTH  : integer := 3;

      --! \brief Data width of input FrameLink header.
      HDR_WIDTH      : integer := 128
      );
   port (
      --! \name Resets and clocks
      --! Clock
      CLK              : in  std_logic;
      --! Reset
      RESET            : in  std_logic;

      --! \name Input FLU interface
      --! Input data
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Input position of packet start inside word
      RX_SOP_POS     : in  std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0);
      --! Input position of packet end inside word
      RX_EOP_POS     : in  std_logic_vector(max(1,log2(DATA_WIDTH/8))- 1 downto 0);
      --! Input start of packet
      RX_SOP         : in  std_logic;
      --! Input end of packet
      RX_EOP         : in  std_logic;
      --! Input source ready
      RX_SRC_RDY     : in  std_logic;
      --! Input destination ready
      RX_DST_RDY     : out std_logic;

      --! \name Input header interface
      --! Header data
      HDR_DATA      : in  std_logic_vector(HDR_WIDTH-1 downto 0);
      --! Header ready (source ready)
      HDR_READY     : in  std_logic;
      --! Header next (destination ready)
      HDR_NEXT      : out std_logic;

      --! \name Output FLU interface
      --! Output data
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Output position of packet start inside word
      TX_SOP_POS    : out std_logic_vector(max(1,SOP_POS_WIDTH)-1 downto 0);
      --! Output position of packet end inside word
      TX_EOP_POS    : out std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
      --! Output start of packet
      TX_SOP        : out std_logic;
      --! Output end of packet
      TX_EOP        : out std_logic;
      --! Output source ready
      TX_SRC_RDY    : out std_logic;
      --! Output destination ready
      TX_DST_RDY    : in  std_logic
   );
end entity;

