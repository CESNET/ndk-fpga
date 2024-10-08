-- flu2qdr_ent.vhd
--!
--! \file
--! \brief FLU to QDR converter
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2014
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

--! \brief Package with log2 function.
use work.math_pack.all;

--! General FLU_ADAPTER package
use work.flu_adapter_pkg.all;

--\name FLU to QDR converter
entity FLU2QDR is
   generic (
      --! Width of read request
      ADDR_WIDTH           : integer := 19 -- 72Mb = 144*2^19
   );
   port (
      --! Resets and clocks ----------------------------------------------------
      CLK             : in  std_logic;
      RST             : in  std_logic;

      --! Input FLU
      FLU_RX_DATA        : in  std_logic_vector(511 downto 0);
      FLU_RX_SOP_POS     : in  std_logic_vector(2 downto 0);
      FLU_RX_EOP_POS     : in  std_logic_vector(5 downto 0);
      FLU_RX_SOP         : in  std_logic;
      FLU_RX_EOP         : in  std_logic;
      FLU_RX_SRC_RDY     : in  std_logic;
      FLU_RX_DST_RDY     : out std_logic;


      --! Output FLU
      FLU_TX_DATA        : out std_logic_vector(511 downto 0);
      FLU_TX_SOP_POS     : out std_logic_vector(2 downto 0);
      FLU_TX_EOP_POS     : out std_logic_vector(5 downto 0);
      FLU_TX_SOP         : out std_logic;
      FLU_TX_EOP         : out std_logic;
      FLU_TX_SRC_RDY     : out std_logic;
      FLU_TX_DST_RDY     : in  std_logic;

      --! Output QDR
      --! read request (address)
      QDR_TX_RD_ADDR      : out std_logic_vector(ADDR_WIDTH-2 downto 0);
      QDR_TX_RD_SRC_RDY   : out std_logic;
      QDR_TX_RD_DST_RDY   : in  std_logic;

      --! write request (address+data)
      QDR_TX_WR_ADDR      : out std_logic_vector(ADDR_WIDTH-2 downto 0);
      QDR_TX_WR_DATA      : out std_logic_vector(863 downto 0);
      QDR_TX_WR_SRC_RDY   : out std_logic;
      QDR_TX_WR_DST_RDY   : in  std_logic;

      --! Input QDR
      --! read data
      QDR_RX_DATA         : in  std_logic_vector(863 downto 0);
      QDR_RX_SRC_RDY      : in  std_logic;
      QDR_RX_DST_RDY      : out std_logic;

      --! Control and status signals, default behaviour as FIFO
      CURRENT_STATE       : out std_logic_vector(3 downto 0);
      NEXT_STATE          : in  std_logic_vector(3 downto 0) := STORAGE_FIFO;
      NEXT_STATE_SRC_RDY  : in  std_logic := '1';
      NEXT_STATE_DST_RDY  : out std_logic;

      ITERATIONS          : in  std_logic_vector(31 downto 0) := (others => '0');
      MEMORY_EMPTY        : out std_logic;
      MEMORY_FULL         : out std_logic;
      MEMORY_START        : out std_logic_vector(ADDR_WIDTH-3 downto 0);
      MEMORY_END          : out std_logic_vector(ADDR_WIDTH-3 downto 0);
      MEMORY_POINTER      : out std_logic_vector(ADDR_WIDTH-3 downto 0)

   );

end entity;
