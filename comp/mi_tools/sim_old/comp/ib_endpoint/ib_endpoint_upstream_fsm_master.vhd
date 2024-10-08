--
-- ib_endpoint_upstream_fsm_master.vhd: Upstream FSM Master Mode
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.ib_pkg.all; -- Internal Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_UPSTREAM_FSM_MASTER is
   port (
      -- ========================
      -- Common Interface
      -- ========================

      -- Clk
      CLK                : in std_logic;
      -- Reset
      RESET              : in std_logic;

      -- ========================
      -- HDR_GEN Interface
      -- ========================

      -- Request from READ_FSM
      RD_COMPL_REQ       : in  std_logic;
      -- Ack for READ_FSM, After ACK Read FSM starts read
      RD_COMPL_ACK       : out std_logic;
      -- Request for any BM operation
      BM_REQ             : in  std_logic;
      -- Ack for BM_FSM, after ack BM_FSM start reading data
      BM_READ_ACK        : out std_logic;
      -- Ack after any BM operation is done
      BM_ACK             : out std_logic;
      -- Type of transaction
      BM_TRANS_TYPE      : in  std_logic_vector(1 downto 0);

      -- ========================
      -- Control Interface
      -- ========================

      -- 0-Slave/1-Master
      GET_SLAVE_MASTER   : out std_logic;
      -- Get second header
      GET_SECOND_HDR     : out std_logic;
      GET_TRANS_TYPE     : out std_logic_vector(1 downto 0);

      -- ========================
      -- Align buffer Interface
      -- ========================

      -- Align buffer src_rdy
      RD_SRC_RDY         : in  std_logic;
      -- Align buffer dst_rdy
      RD_DST_RDY         : out std_logic;
      -- Align buffer eof
      RD_EOF             : in  std_logic;

      -- ========================
      -- Multipexor Interface
      -- ========================

      -- Select HEADER/DATA
      MUX_SEL            : out std_logic;

      -- ========================
      -- Upstream Interface
      -- ========================

      -- Start of Packet (Start of transaction)
      SOP                : out std_logic;
      -- Ent of Packet (End of Transaction)
      EOP                : out std_logic;
      -- Source Ready
      SRC_RDY            : out std_logic;
      -- Destination Ready
      DST_RDY            : in  std_logic
   );
end entity IB_ENDPOINT_UPSTREAM_FSM_MASTER;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_UPSTREAM_FSM_MASTER_ARCH of IB_ENDPOINT_UPSTREAM_FSM_MASTER is

   -- Control FSM declaration
   type   t_states is (st_idle, st_slave_read_wait, st_bm_read_wait, st_rd_hdr, st_bm_hdr, st_data_slave, st_data_master);
   signal present_state, next_state : t_states;
   signal process_en : std_logic;
   signal out_rd_req : std_logic;
   signal out_bm_req : std_logic;
   signal out_rd_ack : std_logic;
   signal out_bm_ack : std_logic;

begin


IB_ENDPOINT_UPSTREAM_PRIORITY_DEC_U : entity work.IB_ENDPOINT_UPSTREAM_PRIORITY_DEC
   port map (
      -- FPGA control
      CLK                   => CLK,
      RESET                 => RESET,

      -- Input Interface
      IN_RD_RQ              => RD_COMPL_REQ,
      IN_BM_RQ              => BM_REQ,
      IN_RD_ACK             => RD_COMPL_ACK,
      IN_BM_ACK             => BM_ACK,

      -- Output Interface
      OUT_RD_RQ             => out_rd_req,
      OUT_BM_RQ             => out_bm_req,
      OUT_RD_ACK            => out_rd_ack,
      OUT_BM_ACK            => out_bm_ack
      );


-- UPSTREAM FSM -----------------------------------------------------------
-- next state clk logic
clk_d: process(CLK, RESET)
  begin
    if RESET = '1' then
      present_state <= st_idle;
    elsif (CLK='1' and CLK'event) then
      present_state <= next_state;
    end if;
  end process;

-- next state logic
state_trans: process(present_state, out_rd_req, out_bm_req, BM_TRANS_TYPE, DST_RDY, RD_EOF, RD_SRC_RDY)
  begin
    case present_state is


      -- ST_IDLE
      when st_idle =>
         -- Header Valid
         if (out_rd_req = '1') then -- Slave read completition
            next_state <= st_slave_read_wait;
         elsif (out_bm_req = '1' and BM_TRANS_TYPE(0) = '1') then -- Master L2GW, L2LW
            next_state <= st_bm_read_wait;
         elsif (out_bm_req = '1' and BM_TRANS_TYPE(0) = '0' and DST_RDY = '1') then -- Master G2LR, L2LR
            next_state <= st_bm_hdr;
         else
            next_state <= st_idle;
         end if;

      -- Wait for slave readed data
      when st_slave_read_wait =>
         if (DST_RDY = '1' and RD_SRC_RDY = '1') then
            next_state <= st_rd_hdr;
         else
            next_state <= st_slave_read_wait;
         end if;

      -- Wait for master readed data
      when st_bm_read_wait =>
         if (DST_RDY = '1' and RD_SRC_RDY = '1') then
            next_state <= st_bm_hdr;
         else
            next_state <= st_bm_read_wait;
         end if;

      -- ST_RD_HDR
      when st_rd_hdr =>
         if (DST_RDY = '1') then
            next_state <= st_data_slave;
         else
            next_state <= st_rd_hdr;
         end if;

      -- ST_BM_HDR
      when st_bm_hdr =>
         if (DST_RDY = '1' and BM_TRANS_TYPE(0) = '0') then -- Master G2LR, L2LR
            next_state <= st_idle;
         elsif (DST_RDY = '1' and BM_TRANS_TYPE(0) = '1') then -- Master L2GW, L2LW
            next_state <= st_data_master;
         else
            next_state <= st_bm_hdr;
         end if;

      -- ST_DATA_SLAVE
      when st_data_slave =>
         -- When Last data readed
         if (DST_RDY = '1' and RD_EOF = '1') then
           next_state <= st_idle;
         else
           next_state <= st_data_slave;
         end if;

      -- ST_DATA_MASTER
      when st_data_master =>
         -- When Last data readed
         if (DST_RDY = '1' and RD_EOF = '1') then
           next_state <= st_idle;
         else
           next_state <= st_data_master;
         end if;

      end case;
  end process;

-- output logic
output_logic: process(present_state, out_rd_req, out_bm_req, BM_TRANS_TYPE, DST_RDY, RD_EOF, RD_SRC_RDY)
  begin
   MUX_SEL            <= '0'; -- Select HEADER/DATA
   RD_DST_RDY         <= '0'; -- RD_DST_RDY
   SOP                <= '0'; -- Start of Packet (Start of transaction)
   EOP                <= '0'; -- Ent of Packet (End of Transaction)
   SRC_RDY            <= '0'; -- Source Ready
   GET_SLAVE_MASTER   <= '0'; -- 0-Slave/1-Master
   GET_SECOND_HDR     <= '0';
   GET_TRANS_TYPE     <= "00";
   out_rd_ack         <= '0';
   out_bm_ack         <= '0';
   BM_READ_ACK        <= '0';

   case present_state is

      -- ST_IDLE
      when st_idle =>
         RD_DST_RDY <= '0';

         if (out_rd_req = '1') then -- Slave read completition
            out_rd_ack        <= '1'; -- Ack for read fsm
         elsif (out_bm_req = '1' and BM_TRANS_TYPE(0) = '1') then -- Master L2GW, L2LW
            BM_READ_ACK       <= '1'; -- ack for bm read fsm
         elsif (out_bm_req = '1' and BM_TRANS_TYPE(0) = '0' and DST_RDY = '1') then -- Master G2LR, L2LR
            SOP               <= '1';
            SRC_RDY           <= '1';
            GET_SLAVE_MASTER  <= '1';
            GET_SECOND_HDR    <= '0';
            GET_TRANS_TYPE    <= BM_TRANS_TYPE;
         end if;

      -- ST_SLAVE_READ_WAIT
      when st_slave_read_wait =>
         if (DST_RDY = '1' and RD_SRC_RDY = '1') then
            SOP               <= '1';
            SRC_RDY           <= '1';
            GET_SLAVE_MASTER  <= '0';
            GET_SECOND_HDR    <= '0';
            GET_TRANS_TYPE    <= "00";
         end if;

      -- ST_BM_READ_WAIT
      when st_bm_read_wait =>
         if (DST_RDY = '1' and RD_SRC_RDY = '1') then
            SOP               <= '1';
            SRC_RDY           <= '1';
            GET_SLAVE_MASTER  <= '1';
            GET_SECOND_HDR    <= '0';
            GET_TRANS_TYPE    <= BM_TRANS_TYPE;
         end if;

      -- ST_RD_HDR
      when st_rd_hdr =>
         GET_SLAVE_MASTER  <= '0';
         GET_SECOND_HDR    <= '1';
         GET_TRANS_TYPE    <= "00";
        if (DST_RDY = '1') then
            SRC_RDY           <= '1';
         end if;

      -- ST_BM_HDR
      when st_bm_hdr =>
         GET_SLAVE_MASTER   <= '1';
         GET_SECOND_HDR     <= '1';
         GET_TRANS_TYPE     <= BM_TRANS_TYPE;
         if (DST_RDY = '1' and BM_TRANS_TYPE(0) = '0') then -- Global to Local
            SRC_RDY           <= '1';
            EOP               <= '1';
            out_bm_ack        <= '1';
         end if;
         if (DST_RDY = '1' and BM_TRANS_TYPE(0) = '1') then -- Local to Global
            SRC_RDY           <= '1';
         end if;

      -- ST_DATA_SLAVE
      when st_data_slave =>
         RD_DST_RDY        <= DST_RDY;
         EOP               <= RD_EOF;
         SRC_RDY           <= RD_SRC_RDY;
         MUX_SEL           <= '1';

      -- ST_DATA_MASTER
      when st_data_master =>
         RD_DST_RDY        <= DST_RDY;
         EOP               <= RD_EOF;
         SRC_RDY           <= RD_SRC_RDY;
         MUX_SEL           <= '1';
         if (DST_RDY = '1' and RD_EOF='1') then
            out_bm_ack    <= '1';
         end if;

      end case;
  end process;

end architecture IB_ENDPOINT_UPSTREAM_FSM_MASTER_ARCH;

