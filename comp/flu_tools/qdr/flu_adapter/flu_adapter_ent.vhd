-- flu_adapter_ent.vhd
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

--\name  FLU adapter entity
entity FLU_ADAPTER is
   generic (
      --! Width of read request
      ADDR_WIDTH           : integer := 19 -- 72Mb = 144*2^19
   );
   port (
      --! Resets and clocks ----------------------------------------------------
      APP_CLK             : in  std_logic;
      APP_RST             : in  std_logic;

      --! QDR clock domain
      QDR_CLK             : in  std_logic;
      QDR_RST             : in  std_logic;

      --! Calibration done from QDR IP core
      CAL_DONE            : in  std_logic_vector(3-1 downto 0);
      REG_CAL_DONE        : out std_logic;

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

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD           : out std_logic;
      --! Address for data to write
      USER_WR_ADDR          : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      --! Data to write
      USER_WR_DATA          : out std_logic_vector(432-1 downto 0);
      --! Data write enable - active low
      USER_WR_BW_N          : out std_logic_vector(144/9-1 downto 0);
      --! Valid bit for data to read
      USER_RD_CMD           : out std_logic;
      --! Address for data to read
      USER_RD_ADDR          : out std_logic_vector(ADDR_WIDTH-1 downto 0);

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID         : in  std_logic_vector(3-1 downto 0);
      --! Already read data
      USER_RD_DATA          : in  std_logic_vector(432-1 downto 0);

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
