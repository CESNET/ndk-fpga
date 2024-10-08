-- qdr_ent.vhd
--!
--! \file
--! \brief QDR adapter entity
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

--\name  Software Defined Monitoring QDR adapter module
entity QDR is
   generic (
      --! Number of QDRs
      QDR_NUMBER           : integer := 1;
      --! Width of read request
      ADDR_WIDTH           : integer := 19;
      --! Returned data width
      DATA_WIDTH           : integer := 144
   );
   port (
      --! Resets and clocks ----------------------------------------------------
      --! Application clock domain
      APP_CLK             : in  std_logic;
      APP_RST             : in  std_logic;

      --! QDR clock domain
      QDR_CLK             : in  std_logic;
      QDR_RST             : in  std_logic;

      --! Calibration done from QDR IP core
      CAL_DONE            : in  std_logic_vector(QDR_NUMBER-1 downto 0);
      REG_CAL_DONE        : out std_logic;

      --! FLU2QDR -> QDR adapter
      --! read request (address)
      QDR_RX_RD_ADDR      : in  std_logic_vector(ADDR_WIDTH-2 downto 0);
      QDR_RX_RD_SRC_RDY   : in  std_logic;
      QDR_RX_RD_DST_RDY   : out std_logic;

      --! write request (address+data)
      QDR_RX_WR_ADDR      : in  std_logic_vector(ADDR_WIDTH-2 downto 0);
      QDR_RX_WR_DATA      : in  std_logic_vector(2*DATA_WIDTH*QDR_NUMBER-1 downto 0);
      QDR_RX_WR_SRC_RDY   : in  std_logic;
      QDR_RX_WR_DST_RDY   : out std_logic;
      --! QDR Adapter -> FLU2QDR
      --! read data
      QDR_TX_DATA              : out std_logic_vector(2*DATA_WIDTH*QDR_NUMBER-1 downto 0);
      QDR_TX_SRC_RDY           : out std_logic;
      QDR_TX_DST_RDY           : in  std_logic;

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD           : out std_logic;
      --! Address for data to write
      USER_WR_ADDR          : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      --! Data to write
      USER_WR_DATA          : out std_logic_vector(DATA_WIDTH*QDR_NUMBER-1 downto 0);
      --! Data write enable - active low
      USER_WR_BW_N          : out std_logic_vector(DATA_WIDTH/9-1 downto 0);
      --! Valid bit for data to read
      USER_RD_CMD           : out std_logic;
      --! Address for data to read
      USER_RD_ADDR          : out std_logic_vector(ADDR_WIDTH-1 downto 0);

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID         : in  std_logic_vector(QDR_NUMBER-1 downto 0);
      --! Already read data
      USER_RD_DATA          : in  std_logic_vector(DATA_WIDTH*QDR_NUMBER-1 downto 0)

   );
end entity;
