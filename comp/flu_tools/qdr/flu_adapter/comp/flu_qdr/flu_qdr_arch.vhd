-- flu_qdr_arch.vhd
--!
--! \file
--! \brief FLU_ADAPTER connected to 3 QDR composed of 2 BRAM architecture
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function.
use work.math_pack.all;

--! \brief Implementation FLU_ADAPTER connected to 3 QDR composed of 2 BRAM
architecture FULL of FLU_QDR is

   signal user_wr_cmd       : std_logic;
   signal user_wr_addr      : std_logic_vector(8 downto 0);
   signal user_wr_data      : std_logic_vector(431 downto 0);
   signal user_wr_bw_n      : std_logic_vector(15 downto 0);

   signal user_rd_cmd       : std_logic;
   signal user_rd_addr      : std_logic_vector(8 downto 0);

   signal user_rd_valid     : std_logic_vector(2 downto 0);
   signal user_rd_data      : std_logic_vector(431 downto 0);


begin

   --! FLU_ADAPTER instantiation
   flu_adapteri: entity work.FLU_ADAPTER
   generic map (
      --! Width of read request
      ADDR_WIDTH => 9 -- 72Mb = 144*2^19
   )
   port map (
      --! Resets and clocks ----------------------------------------------------
      APP_CLK => APP_CLK,
      APP_RST => APP_RST,

      --! QDR clock domain
      QDR_CLK => QDR_CLK,
      QDR_RST => QDR_RST,

      --! Calibration done from QDR IP core
      CAL_DONE => (others => '1'),
      REG_CAL_DONE => open,

      --! Input FLU
      FLU_RX_DATA => FLU_RX_DATA,
      FLU_RX_SOP_POS => FLU_RX_SOP_POS,
      FLU_RX_EOP_POS => FLU_RX_EOP_POS,
      FLU_RX_SOP => FLU_RX_SOP,
      FLU_RX_EOP => FLU_RX_EOP,
      FLU_RX_SRC_RDY => FLU_RX_SRC_RDY,
      FLU_RX_DST_RDY => FLU_RX_DST_RDY,


      --! Output FLU
      FLU_TX_DATA => FLU_TX_DATA,
      FLU_TX_SOP_POS => FLU_TX_SOP_POS,
      FLU_TX_EOP_POS => FLU_TX_EOP_POS,
      FLU_TX_SOP => FLU_TX_SOP,
      FLU_TX_EOP => FLU_TX_EOP,
      FLU_TX_SRC_RDY => FLU_TX_SRC_RDY,
      FLU_TX_DST_RDY => FLU_TX_DST_RDY,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => user_wr_addr,
      --! Data to write
      USER_WR_DATA => user_wr_data,
      --! Data write enable - active low
      USER_WR_BW_N => user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => user_rd_valid,
      --! Already read data
      USER_RD_DATA => user_rd_data
   );

   --! QDR instantiation
   qdr_bram0i: entity work.QDR_BRAM
   port map(
      --! Resets and clocks ----------------------------------------------------
      CLK => QDR_CLK,
      RST => QDR_RST,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => user_wr_addr,
      --! Data to write
      USER_WR_DATA =>user_wr_data(143 downto 0),
      --! Data write enable - active low
      USER_WR_BW_N => user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => user_rd_valid(0),
      --! Already read data
      USER_RD_DATA => user_rd_data(143 downto 0)
   );

   qdr_bram1i: entity work.QDR_BRAM
   port map(
      --! Resets and clocks ----------------------------------------------------
      CLK => QDR_CLK,
      RST => QDR_RST,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => user_wr_addr,
      --! Data to write
      USER_WR_DATA =>user_wr_data(287 downto 144),
      --! Data write enable - active low
      USER_WR_BW_N => user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => user_rd_valid(1),
      --! Already read data
      USER_RD_DATA => user_rd_data(287 downto 144)
   );

   qdr_bram2i: entity work.QDR_BRAM
   port map(
      --! Resets and clocks ----------------------------------------------------
      CLK => QDR_CLK,
      RST => QDR_RST,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => user_wr_addr,
      --! Data to write
      USER_WR_DATA =>user_wr_data(431 downto 288),
      --! Data write enable - active low
      USER_WR_BW_N => user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => user_rd_valid(2),
      --! Already read data
      USER_RD_DATA => user_rd_data(431 downto 288)
   );

end architecture;
