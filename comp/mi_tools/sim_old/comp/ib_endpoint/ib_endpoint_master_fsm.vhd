--
-- ib_endpoint_master_fsm.vhd: ib2adc Read FSM
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
entity IB_ENDPOINT_MASTER_FSM is
   generic (
      STRICT_EN  : boolean
   );
   port (
   -- ========================
   -- Common Interface
   -- ========================

   -- Clk
   CLK              : in std_logic;
   -- Reset
   RESET            : in std_logic;
   IDLE             : out std_logic;
   WRITE_FSM_IDLE   : in  std_logic;

   -- ========================
   -- BusMaster Interface
   -- ========================

   -- Busmaster Request (Request for BM operation)
   BM_REQ           : in  std_logic;
   -- Acknowledge from upstream FSM (transaction was sended)
   BM_ACK           : in  std_logic;
   -- Busmaster FSM can read data (Upstream FSM RDY)
   BM_READ_ACK      : in  std_logic;
   -- Type
   BM_TRANS_TYPE    : in  std_logic_vector(1 downto 0);

   -- ==========================
   -- Component status interface
   -- ==========================

   -- Last Read Req
   LAST_READ_REQ    : in std_logic;

   -- ==========================
   -- Register control interface
   -- ==========================

   -- Store Addr into addr_cnt and addr_align
   ADDR_WE          : out std_logic;
   -- Store lenght for Align circuit
   LENGHT_WE        : out std_logic;

   -- ==========================
   -- Component Init interface
   -- ==========================

   -- Init BE circuit
   INIT_BE          : out std_logic;
   -- Init Read Align circuit
   READ_ALIGN_INIT  : out std_logic;

   -- ==========================
   -- Read Interface
   -- ==========================

   -- Start of frame (Start of transaction)
   RD_SOF_IN        : out std_logic;
   -- Ent of frame (End of Transaction)
   RD_EOF_IN        : out std_logic;
   -- Read from User Component
   RD_REQ           : out std_logic;
   -- Adress RDY
   RD_ARDY          : in  std_logic
   );
end entity IB_ENDPOINT_MASTER_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_MASTER_FSM_ARCH of IB_ENDPOINT_MASTER_FSM is

   -- Control FSM declaration
   type   t_states is (st_idle, st_sop, st_strict_wait, st_read, st_wait);
   signal present_state, next_state : t_states;
   signal process_en                : std_logic;

begin

process_en <= '1' when (not STRICT_EN or (STRICT_EN and WRITE_FSM_IDLE = '1')) else '0';



-- SWITCH INPUT FSM -----------------------------------------------------------
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
state_trans: process(present_state, BM_REQ, BM_ACK, BM_TRANS_TYPE, BM_READ_ACK, LAST_READ_REQ, RD_ARDY, process_en)
  begin
    case present_state is

      when st_idle =>
         -- Busmaster operation which needs data from user component, Need ACK for reading
         if (BM_TRANS_TYPE(0) = '1' and BM_READ_ACK = '1') then -- Master L2GW, L2LW
            if (process_en = '1') then
               next_state <= st_sop;
            else
               next_state <= st_strict_wait;
            end if;
         else
            next_state <= st_idle; -- Idle
         end if;

      when st_strict_wait =>
         if (process_en = '1') then
            next_state <= st_sop;
         else
            next_state <= st_strict_wait;
         end if;

      -- ST_SOP
      when st_sop =>
         -- End of transaction
         if (LAST_READ_REQ='1' and RD_ARDY='1') then
           next_state <= st_wait;
         -- Write another word
         elsif (RD_ARDY='1') then
           next_state <= st_read;
         -- Stay
         else
           next_state <= st_sop;
         end if;

      -- ST_READ
      when st_read =>
         -- Wait for all ardy
         if (LAST_READ_REQ = '1' and RD_ARDY='1') then
           next_state <= st_wait;
         else
           next_state <= st_read;
         end if;

      -- ST_WAIT
      when st_wait =>
         if (BM_ACK = '1') then
            next_state <= st_idle;
         else
            next_state <= st_wait;
         end if;
      end case;
  end process;

-- output logic
output_logic: process(present_state, BM_REQ, BM_READ_ACK, BM_TRANS_TYPE, LAST_READ_REQ, process_en)
  begin

  ADDR_WE          <= '0'; -- Store Addr into addr_cnt and addr_align
  LENGHT_WE        <= '0'; -- Store lenght for Align circuit
  INIT_BE          <= '0'; -- Init BE circuit
  READ_ALIGN_INIT  <= '0'; -- Init Read Align circuit
  RD_SOF_IN        <= '0'; -- Start of frame (Start of transaction)
  RD_EOF_IN        <= '0'; -- Ent of frame (End of Transaction)
  RD_REQ           <= '0'; -- Read from User Component
  IDLE             <= '0';

   case present_state is

      -- ST_IDLE
      when st_idle =>
       if (process_en = '1' and BM_TRANS_TYPE(0) = '1' and BM_READ_ACK = '1') then -- Master L2GW, L2LW
          ADDR_WE         <= '1';
          LENGHT_WE       <= '1';
          INIT_BE         <= '1';
          READ_ALIGN_INIT <= '1';
          IDLE <= '0'; -- Priority from write side in strict version
       else
          IDLE <= '1';
       end if;

      when st_strict_wait =>
         if (process_en = '1') then
            ADDR_WE         <= '1';
            LENGHT_WE       <= '1';
            INIT_BE         <= '1';
            READ_ALIGN_INIT <= '1';
         end if;

      -- ST_SOP
      when st_sop =>
         RD_SOF_IN             <= '1';
         RD_REQ                <= '1';
         if (LAST_READ_REQ = '1') then
            RD_EOF_IN          <= '1';
         end if;

      -- ST_READ
      when st_read =>
         RD_REQ              <= '1';
         if (LAST_READ_REQ = '1') then
            RD_EOF_IN          <= '1';
         end if;

      -- ST_WAIT
      when st_wait =>
         IDLE <= '1';

   end case;
end process;

end architecture IB_ENDPOINT_MASTER_FSM_ARCH;

