-- flu_adapter_arch.vhd
--!
--! \file
--! \brief FLU2QDR module TOP LEVEL entity
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function.
use work.math_pack.all;

--! General FLU_ADAPTER package
use work.flu_adapter_pkg.all;

--! \brief Implementation of FLU adapter
architecture FULL of FLU_ADAPTER is

   --! \brief constant declaration

   --! \brief signal declaration
   --! Input flu pipe output signals
   signal pipein_flu_tx_data             : std_logic_vector(511 downto 0);
   signal pipein_flu_tx_sop_pos          : std_logic_vector(2 downto 0);
   signal pipein_flu_tx_eop_pos          : std_logic_vector(5 downto 0);
   signal pipein_flu_tx_sop              : std_logic;
   signal pipein_flu_tx_eop              : std_logic;
   signal pipein_flu_tx_src_rdy          : std_logic;
   signal pipein_flu_tx_dst_rdy          : std_logic;

   --! Output flu pipe input signals
   signal pipeout_flu_rx_data            : std_logic_vector(511 downto 0);
   signal pipeout_flu_rx_sop_pos         : std_logic_vector(2 downto 0);
   signal pipeout_flu_rx_eop_pos         : std_logic_vector(5 downto 0);
   signal pipeout_flu_rx_sop             : std_logic;
   signal pipeout_flu_rx_eop             : std_logic;
   signal pipeout_flu_rx_src_rdy         : std_logic;
   signal pipeout_flu_rx_dst_rdy         : std_logic;

   --! QDR read request pipe input/output signals
   signal piperd_in_data                 : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal piperd_in_src_rdy              : std_logic;
   signal piperd_in_dst_rdy              : std_logic;

   signal piperd_out_data                : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal piperd_out_src_rdy             : std_logic;
   signal piperd_out_dst_rdy             : std_logic;

   --! QDR write request pipe input/output signals
   signal pipewr_in_data                 : std_logic_vector(864+ADDR_WIDTH-2 downto 0);
   signal pipewr_in_src_rdy              : std_logic;
   signal pipewr_in_dst_rdy              : std_logic;

   signal pipewr_out_data                : std_logic_vector(864+ADDR_WIDTH-2 downto 0);
   signal pipewr_out_src_rdy             : std_logic;
   signal pipewr_out_dst_rdy             : std_logic;

   --! QDR write request flu2qdr output signals
   signal flu2qdr_qdr_tx_wr_addr         : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal flu2qdr_qdr_tx_wr_data         : std_logic_vector(863 downto 0);
   signal flu2qdr_qdr_tx_wr_src_rdy      : std_logic;
   signal flu2qdr_qdr_tx_wr_dst_rdy      : std_logic;

   --! QDR adapter request signals
   signal qdr_request_in_rd              : std_logic_vector(ADDR_WIDTH*2-1 downto 0);
   signal qdr_request_in_rd_vld          : std_logic_vector(2-1 downto 0);
   signal qdr_request_in_wr              : std_logic_vector(ADDR_WIDTH*2+864-1 downto 0);
   signal qdr_request_in_wr_vld          : std_logic_vector(2-1 downto 0);
   signal qdr_request_in_ack             : std_logic;

   --! QDR adapter output qdr data pipe
   signal piperdout_in_data              : std_logic_vector(863 downto 0);
   signal piperdout_in_src_rdy           : std_logic;
   signal piperdout_in_dst_rdy           : std_logic;

   signal piperdout_out_data             : std_logic_vector(863 downto 0);
   signal piperdout_out_src_rdy          : std_logic;
   signal piperdout_out_dst_rdy          : std_logic;

   --! QDR adapter output qdr data
   signal qdr_data_out                   : std_logic_vector(863 downto 0);
   signal qdr_data_out_vld               : std_logic_vector(2-1 downto 0);
   signal qdr_data_out_dst_rdy           : std_logic;

   --! QDR Adapter -> QDR IP core pipeline registers
   signal qdr_user_wr_cmd                : std_logic;
   signal qdr_user_wr_addr               : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal qdr_user_wr_data               : std_logic_vector(431 downto 0);
   signal qdr_user_wr_bw_n               : std_logic_vector(15 downto 0);
   signal qdr_user_rd_cmd                : std_logic;
   signal qdr_user_rd_addr               : std_logic_vector(ADDR_WIDTH-1 downto 0);

   signal reg_user_wr_cmd                : std_logic;
   signal reg_user_wr_addr               : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg_user_wr_data               : std_logic_vector(431 downto 0);
   signal reg_user_wr_bw_n               : std_logic_vector(15 downto 0);
   signal reg_user_rd_cmd                : std_logic;
   signal reg_user_rd_addr               : std_logic_vector(ADDR_WIDTH-1 downto 0);

   --! QDR IP core -> QDR Adapter pipeline registers
   signal qdr_user_rd_valid              : std_logic_vector(2 downto 0);
   signal qdr_user_rd_data               : std_logic_vector(431 downto 0);

   signal reg_user_rd_valid              : std_logic_vector(2 downto 0);
   signal reg_user_rd_data               : std_logic_vector(431 downto 0);


begin

   --! FLU2QDR instantiation ---------------------------------------------------
   flu2qdri: entity work.flu2qdr
   generic map (
      --! Width of read request
      ADDR_WIDTH => ADDR_WIDTH
   )
   port map (
      --! Resets and clocks
      CLK => APP_CLK,
      RST => APP_RST,

      --! Input FLU
      FLU_RX_DATA => pipein_flu_tx_data,
      FLU_RX_SOP_POS => pipein_flu_tx_sop_pos,
      FLU_RX_EOP_POS => pipein_flu_tx_eop_pos,
      FLU_RX_SOP => pipein_flu_tx_sop,
      FLU_RX_EOP => pipein_flu_tx_eop,
      FLU_RX_SRC_RDY => pipein_flu_tx_src_rdy,
      FLU_RX_DST_RDY => pipein_flu_tx_dst_rdy,


      --! Output FLU
      FLU_TX_DATA => pipeout_flu_rx_data,
      FLU_TX_SOP_POS => pipeout_flu_rx_sop_pos,
      FLU_TX_EOP_POS => pipeout_flu_rx_eop_pos,
      FLU_TX_SOP => pipeout_flu_rx_sop,
      FLU_TX_EOP => pipeout_flu_rx_eop,
      FLU_TX_SRC_RDY => pipeout_flu_rx_src_rdy,
      FLU_TX_DST_RDY => pipeout_flu_rx_dst_rdy,

      --! Output QDR
      --! read request (address)
      QDR_TX_RD_ADDR => piperd_in_data,
      QDR_TX_RD_SRC_RDY => piperd_in_src_rdy,
      QDR_TX_RD_DST_RDY => piperd_in_dst_rdy,

      --! write request (address+data)
      QDR_TX_WR_ADDR => flu2qdr_qdr_tx_wr_addr,
      QDR_TX_WR_DATA => flu2qdr_qdr_tx_wr_data,
      QDR_TX_WR_SRC_RDY => flu2qdr_qdr_tx_wr_src_rdy,
      QDR_TX_WR_DST_RDY => flu2qdr_qdr_tx_wr_dst_rdy,

      --! Input QDR
      --! read data
      QDR_RX_DATA => piperdout_out_data,
      QDR_RX_SRC_RDY => piperdout_out_src_rdy,
      QDR_RX_DST_RDY => piperdout_out_dst_rdy,

      --! Control signals, default behaviour as FIFO
      CURRENT_STATE => CURRENT_STATE,
      NEXT_STATE => NEXT_STATE,
      NEXT_STATE_SRC_RDY => NEXT_STATE_SRC_RDY,
      NEXT_STATE_DST_RDY => NEXT_STATE_DST_RDY,

      ITERATIONS => ITERATIONS,
      MEMORY_EMPTY => MEMORY_EMPTY,
      MEMORY_FULL => MEMORY_FULL,
      MEMORY_START => MEMORY_START,
      MEMORY_END => MEMORY_END,
      MEMORY_POINTER => MEMORY_POINTER


   );

   --! QDR write request flu2qdr connection to QDR write request pipe
   pipewr_in_data <= flu2qdr_qdr_tx_wr_addr & flu2qdr_qdr_tx_wr_data;
   pipewr_in_src_rdy <= flu2qdr_qdr_tx_wr_src_rdy;
   flu2qdr_qdr_tx_wr_dst_rdy <= pipewr_in_dst_rdy;

   --! QDR TX RD/WR pipe
   piperdi : entity work.pipe
   generic map(
      DATA_WIDTH      => ADDR_WIDTH-1,
      USE_OUTREG      => false,
      FAKE_PIPE       => true
   )
   port map(
      CLK         => APP_CLK,
      RESET       => APP_RST,

      IN_DATA      => piperd_in_data,
      IN_SRC_RDY   => piperd_in_src_rdy,
      IN_DST_RDY   => piperd_in_dst_rdy,

      OUT_DATA     => piperd_out_data,
      OUT_SRC_RDY  => piperd_out_src_rdy,
      OUT_DST_RDY  => piperd_out_dst_rdy
   );

   pipewri : entity work.pipe
   generic map(
      DATA_WIDTH      => 864+ADDR_WIDTH-1,
      USE_OUTREG      => true,
      FAKE_PIPE       => false
   )
   port map(
      CLK         => APP_CLK,
      RESET       => APP_RST,

      IN_DATA      => pipewr_in_data,
      IN_SRC_RDY   => pipewr_in_src_rdy,
      IN_DST_RDY   => pipewr_in_dst_rdy,

      OUT_DATA     => pipewr_out_data,
      OUT_SRC_RDY  => pipewr_out_src_rdy,
      OUT_DST_RDY  => pipewr_out_dst_rdy
   );

   --! Input/Output FLU pipe
   flu_pipeini: entity work.flu_pipe
   generic map (
      -- FrameLinkUnaligned Data Width
      DATA_WIDTH => 512,
      SOP_POS_WIDTH => 3,
      USE_OUTREG => true,
      FAKE_PIPE => false
   )
   port map (
      -- Common interface
      CLK => APP_CLK,
      RESET => APP_RST,

      -- Input interface
      RX_DATA => FLU_RX_DATA,
      RX_SOP_POS => FLU_RX_SOP_POS,
      RX_EOP_POS => FLU_RX_EOP_POS,
      RX_SOP => FLU_RX_SOP,
      RX_EOP => FLU_RX_EOP,
      RX_SRC_RDY => FLU_RX_SRC_RDY,
      RX_DST_RDY => FLU_RX_DST_RDY,

      -- Output interface
      TX_DATA => pipein_flu_tx_data,
      TX_SOP_POS => pipein_flu_tx_sop_pos,
      TX_EOP_POS => pipein_flu_tx_eop_pos,
      TX_SOP => pipein_flu_tx_sop,
      TX_EOP => pipein_flu_tx_eop,
      TX_SRC_RDY => pipein_flu_tx_src_rdy,
      TX_DST_RDY => pipein_flu_tx_dst_rdy,

      -- Debuging interface ---------------------------------------------------
      DEBUG_BLOCK => '0',
      DEBUG_DROP => '0',
      DEBUG_SRC_RDY => open,
      DEBUG_DST_RDY => open,
      DEBUG_SOP => open,
      DEBUG_EOP => open
   );

   flu_pipeouti: entity work.flu_pipe
   generic map (
      -- FrameLinkUnaligned Data Width
      DATA_WIDTH => 512,
      SOP_POS_WIDTH => 3,
      USE_OUTREG => true,
      FAKE_PIPE => false
   )
   port map (
      -- Common interface
      CLK => APP_CLK,
      RESET => APP_RST,

      -- Input interface
      RX_DATA => pipeout_flu_rx_data,
      RX_SOP_POS => pipeout_flu_rx_sop_pos,
      RX_EOP_POS => pipeout_flu_rx_eop_pos,
      RX_SOP => pipeout_flu_rx_sop,
      RX_EOP => pipeout_flu_rx_eop,
      RX_SRC_RDY => pipeout_flu_rx_src_rdy,
      RX_DST_RDY => pipeout_flu_rx_dst_rdy,

      -- Output interface
      TX_DATA => FLU_TX_DATA,
      TX_SOP_POS => FLU_TX_SOP_POS,
      TX_EOP_POS => FLU_TX_EOP_POS,
      TX_SOP => FLU_TX_SOP,
      TX_EOP => FLU_TX_EOP,
      TX_SRC_RDY => FLU_TX_SRC_RDY,
      TX_DST_RDY => FLU_TX_DST_RDY,

      -- Debuging interface ---------------------------------------------------
      DEBUG_BLOCK => '0',
      DEBUG_DROP => '0',
      DEBUG_SRC_RDY => open,
      DEBUG_DST_RDY => open,
      DEBUG_SOP => open,
      DEBUG_EOP => open
   );

   --! QDR adapter instantiation
   qdri: entity work.qdr
   generic map (
      --! Number of QDRs
      QDR_NUMBER => 3,
      --! Width of read request
      ADDR_WIDTH => ADDR_WIDTH,
      --! Returned data width
      DATA_WIDTH => 144
   )
   port map (
      --! Resets and clocks ----------------------------------------------------
      --! SDM clock domain
      APP_CLK => APP_CLK,
      APP_RST => APP_RST,

      --! QDR clock domain
      QDR_CLK => QDR_CLK,
      QDR_RST => QDR_RST,

      --! Calibration done from QDR IP core
      CAL_DONE => CAL_DONE,
      REG_CAL_DONE => REG_CAL_DONE,

      --! FLU2QDR -> QDR adapter
      --! read request (address)
      QDR_RX_RD_ADDR => piperd_out_data,
      QDR_RX_RD_SRC_RDY => piperd_out_src_rdy,
      QDR_RX_RD_DST_RDY => piperd_out_dst_rdy,

      --! write request (address+data)
      QDR_RX_WR_ADDR => pipewr_out_data(864+ADDR_WIDTH-2 downto 864),
      QDR_RX_WR_DATA => pipewr_out_data(863 downto 0),
      QDR_RX_WR_SRC_RDY => pipewr_out_src_rdy,
      QDR_RX_WR_DST_RDY => pipewr_out_dst_rdy,
      --! QDR Adapter -> FLU2QDR
      --! read data
      QDR_TX_DATA => piperdout_in_data,
      QDR_TX_SRC_RDY => piperdout_in_src_rdy,
      QDR_TX_DST_RDY => piperdout_in_dst_rdy,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => qdr_user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => qdr_user_wr_addr,
      --! Data to write
      USER_WR_DATA => qdr_user_wr_data,
      --! Data write enable - active low
      USER_WR_BW_N => qdr_user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => qdr_user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => qdr_user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => qdr_user_rd_valid,
      --! Already read data
      USER_RD_DATA => qdr_user_rd_data
   );

   --! Pipeline registers to QDR IP CORE

   reg_userp: process(QDR_CLK)
   begin
      if (QDR_CLK'event and QDR_CLK = '1') then
         if (QDR_RST = '1') then
            reg_user_wr_cmd <= '0';
            reg_user_rd_cmd <= '0';
            reg_user_rd_valid <= (others => '0');
         else
            reg_user_wr_cmd <= qdr_user_wr_cmd;
            reg_user_wr_addr <= qdr_user_wr_addr;
            reg_user_wr_data <= qdr_user_wr_data;
            reg_user_wr_bw_n <= qdr_user_wr_bw_n;
            reg_user_rd_cmd <= qdr_user_rd_cmd;
            reg_user_rd_addr <= qdr_user_rd_addr;
            reg_user_rd_valid <= USER_RD_VALID;
            reg_user_rd_data <= USER_RD_DATA;
         end if;
      end if;
   end process;

   USER_WR_CMD <= reg_user_wr_cmd;
   USER_WR_ADDR <= reg_user_wr_addr;
   USER_WR_DATA <= reg_user_wr_data;
   USER_WR_BW_N <= reg_user_wr_bw_n;
   USER_RD_CMD <= reg_user_rd_cmd;
   USER_RD_ADDR <= reg_user_rd_addr;

   qdr_user_rd_valid <= reg_user_rd_valid;
   qdr_user_rd_data <= reg_user_rd_data;

   --! QDR adapter output data pipe
   piperdouti : entity work.pipe
   generic map(
      DATA_WIDTH      => 864,
      USE_OUTREG      => true,
      FAKE_PIPE       => false
   )
   port map(
      CLK         => APP_CLK,
      RESET       => APP_RST,

      IN_DATA      => piperdout_in_data,
      IN_SRC_RDY   => piperdout_in_src_rdy,
      IN_DST_RDY   => piperdout_in_dst_rdy,

      OUT_DATA     => piperdout_out_data,
      OUT_SRC_RDY  => piperdout_out_src_rdy,
      OUT_DST_RDY  => piperdout_out_dst_rdy
   );

end architecture;
