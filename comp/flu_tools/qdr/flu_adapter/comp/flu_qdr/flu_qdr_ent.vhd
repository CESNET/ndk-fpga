-- qdr_bram_ent.vhd
--!
--! \file
--! \brief FLU_ADAPTER connected to 3 QDR composed of 2 BRAM
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

--\name FLU_ADAPTER connected to 3 QDR composed of 2 BRAM
entity FLU_QDR is
   port (
      --! Resets and clocks ----------------------------------------------------
      APP_CLK             : in  std_logic;
      APP_RST             : in  std_logic;

      --! QDR clock domain
      QDR_CLK             : in  std_logic;
      QDR_RST             : in  std_logic;

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
      FLU_TX_DST_RDY     : in  std_logic

   );
end entity;
