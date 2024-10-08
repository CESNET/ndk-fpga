--
-- lb_root_core_fsm.vhd: Local Bus root component FSM
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
entity LB_ROOT_CORE_FSM is
   generic (
      ABORT_CNT_WIDTH     : integer := 4
   );
   port(
   -- ==========================
   -- Common Interface
   -- ==========================

   -- Clk
   CLK                    : in std_logic;
   -- Reset
   RESET                  : in std_logic;

   -- ==========================
   -- Buffer Interface
   -- ==========================

   -- Start of Frame
   BUFFER_SOF             : in  std_logic;
   -- End Of Frame
   BUFFER_EOF             : in  std_logic;
   -- Read
   BUFFER_RD              : in  std_logic;
   -- Write
   BUFFER_WR              : in  std_logic;
   -- Item VLD
   BUFFER_VLD             : in  std_logic;
   -- Next 64 bits Item
   BUFFER_NEXT            : out std_logic;

   -- ==========================
   -- Core Control Interface
   -- ==========================

   -- Clear all counters
   INIT_COUNTERS          : out std_logic;
   -- Select LB_DWR
   ADDR_DATA_MUX_SEL      : out std_logic_vector(1 downto 0);
   -- Increment data out counter (select 16 bit item from 64 bit word)
   DATA_OUT_CNT_CE        : out std_logic;
   -- Set when reading operation
   READING_FLAG           : out std_logic;

   -- ==========================
   -- Core Status Interface
   -- ==========================

   -- Generate Abort Flag
   GEN_ABORT_FLAG         : in  std_logic;
   -- Waiting for all rdy signals
   WAIT_FOR_ALL_RDY       : out std_logic;
   -- Realize data_mux select
   DATA_OUT_CNT           : in  std_logic_vector(1 downto 0);
   -- Pending Items Counter
   PENDING_CNT            : in  std_logic_vector(3 downto 0);
   -- Is set when BE = 00 (end of transaction)
   LAST_REQ               : in  std_logic;

   -- ==========================
   -- Local Bus Output Interface
   -- ==========================

   -- Address Select
   LB_ADS                 : out std_logic;
   -- Read
   LB_RD                  : out std_logic;
   -- Write
   LB_WR                  : out std_logic;
   -- Abort Generation
   LB_ABORT               : out std_logic
   );
end entity LB_ROOT_CORE_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ROOT_CORE_FSM_ARCH of LB_ROOT_CORE_FSM is

   -- Control FSM declaration
   type   t_states is (st_idle, st_addr, st_rw0, st_rw1, st_rw_wait, st_abort);
   signal present_state, next_state : t_states;
   signal reading_flag_reg          : std_logic;
   signal reading_flag_reg_set      : std_logic;
   signal reading_flag_reg_rst      : std_logic;

   signal abort_cnt_ce  : std_logic;
   signal abort_cnt_rst : std_logic;
   signal abort_cnt     : std_logic_vector(ABORT_CNT_WIDTH-1 downto 0);

   constant abort_vccvec  : std_logic_vector(ABORT_CNT_WIDTH-1 downto 0) :=
                              (others => '1');


begin

READING_FLAG <= reading_flag_reg;

-- register reading_flag_reg --------------------------------------------------
reading_flag_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reading_flag_reg <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (reading_flag_reg_set = '1') then
         reading_flag_reg <= '1';
      end if;
      if (reading_flag_reg_rst = '1') then
         reading_flag_reg <= '0';
      end if;
   end if;
end process;


abort_cntp: process(RESET, CLK)
begin
   if (RESET = '1') then
      abort_cnt <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (abort_cnt_ce = '1') then
         abort_cnt <= abort_cnt + 1;
      end if;
      if (abort_cnt_rst = '1') then
         abort_cnt <= (others => '0');
      end if;
   end if;
end process;


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
state_trans: process(present_state, BUFFER_VLD, BUFFER_SOF, BUFFER_EOF,
                     PENDING_CNT, DATA_OUT_CNT, LAST_REQ, abort_cnt, GEN_ABORT_FLAG)
  begin
    case present_state is

      -- ST_IDLE
      when st_idle =>
         if (GEN_ABORT_FLAG = '1') then
            next_state <= st_abort;
         -- When start of transaction
         elsif (BUFFER_VLD = '1' and BUFFER_SOF = '1') then
           next_state <= st_addr;
         else
           next_state <= st_idle;
         end if;

      -- ST_ADDR
      when st_addr =>
         if (GEN_ABORT_FLAG = '1') then
           next_state <= st_abort;
         else
           next_state <= st_rw0;
         end if;

      -- ST_RW0
      when st_rw0 =>
         if (GEN_ABORT_FLAG = '1') then
            next_state <= st_abort;
         -- Data is Valid and 16 item limit isn't reached
         elsif (LAST_REQ = '1') then
           next_state <= st_rw_wait;
         elsif (PENDING_CNT < "1110" and BUFFER_VLD='1') then
           next_state <= st_rw1;
         else
           next_state <= st_rw0;
         end if;

      -- ST_RW1
      when st_rw1 =>
         if (GEN_ABORT_FLAG = '1') then
            next_state <= st_abort;
         -- When last item and item can be writen (wait for all rdy)
         elsif ((PENDING_CNT < "1110" and BUFFER_VLD='1' and BUFFER_EOF ='1' and DATA_OUT_CNT = "11") or LAST_REQ = '1') then
            next_state <= st_rw_wait;
         -- Data is Valid and 16 item limit isn't reached
         elsif (PENDING_CNT < "1110" and BUFFER_VLD='1') then
            next_state <= st_rw0;
         else
            next_state <= st_rw1;
         end if;

      -- ST_RW_WAIT
      when st_rw_wait =>
         if (GEN_ABORT_FLAG = '1') then
            next_state <= st_abort;
         -- Wait for all rdy signals
         elsif (PENDING_CNT = "0000") then
           next_state <= st_idle;
         else
           next_state <= st_rw_wait;
         end if;

      -- ST_ABORT
      when st_abort =>
         if (abort_cnt = abort_vccvec) then
            next_state <= st_idle;
         else
            next_state <= st_abort;
         end if;
      end case;
  end process;

-- output logic
output_logic: process(present_state, BUFFER_VLD, BUFFER_SOF, BUFFER_EOF, BUFFER_RD, BUFFER_WR,
                      PENDING_CNT, DATA_OUT_CNT, LAST_REQ)
  begin
   BUFFER_NEXT            <= '0';  -- Next 64 bits Item
   INIT_COUNTERS          <= '0';  -- Clear Counter
   ADDR_DATA_MUX_SEL      <= "00"; -- Select LB_DWR
   DATA_OUT_CNT_CE        <= '0';  -- Increment data out counter (select 16 bit item from 64 bit word)
   LB_ADS                 <= '0';  -- Address Select
   LB_RD                  <= '0';  -- Read
   LB_WR                  <= '0';  -- Write
   LB_ABORT               <= '0';  -- Abort Generation
   reading_flag_reg_rst   <= '0';  -- Reset read flag
   reading_flag_reg_set   <= '0';  -- Set read flag
   WAIT_FOR_ALL_RDY       <= '0';
   abort_cnt_ce           <= '0';
   abort_cnt_rst          <= '0';

   case present_state is

      -- ST_IDLE
      when st_idle =>
         BUFFER_NEXT            <= BUFFER_VLD and not BUFFER_SOF;
         INIT_COUNTERS          <= '1';
         abort_cnt_rst          <= '1';
         reading_flag_reg_rst   <= '1';
         if (BUFFER_VLD = '1' and BUFFER_SOF = '1') then
            ADDR_DATA_MUX_SEL   <= "00";
            LB_ADS              <= '1';
         end if;

      -- ST_ADDR
      when st_addr =>
         INIT_COUNTERS          <= '1';
         ADDR_DATA_MUX_SEL      <= "01";
         LB_ADS                 <= '1';
         reading_flag_reg_set   <= BUFFER_RD;

      -- ST_RW0
      when st_rw0 =>
         if (LAST_REQ = '1') then -- TODO Check this
            BUFFER_NEXT         <= '1';
         end if;
         ADDR_DATA_MUX_SEL      <= "10";
         if (PENDING_CNT  < "1110" and BUFFER_VLD='1') then
           LB_WR                <= BUFFER_WR;
           LB_RD                <= BUFFER_RD;
           DATA_OUT_CNT_CE      <= '1';
         end if;

      -- ST_RW1
      when st_rw1 =>
         if (LAST_REQ = '1') then -- TODO Check this
            BUFFER_NEXT         <= '1';
         end if;
         ADDR_DATA_MUX_SEL      <= "10";
         if (PENDING_CNT < "1110"  and BUFFER_VLD='1' and LAST_REQ = '0') then
            DATA_OUT_CNT_CE      <= '1';
            LB_WR             <= BUFFER_WR;
            LB_RD             <= BUFFER_RD;
         end if;
         if (DATA_OUT_CNT = "11" and PENDING_CNT < "1110" and BUFFER_VLD='1') then
            BUFFER_NEXT             <= '1';
         end if;

      -- ST_RW_WAIT
      when st_rw_wait =>
         WAIT_FOR_ALL_RDY       <= '1';

      -- ST_ABORT
      when st_abort =>
          abort_cnt_ce  <= '1';
          LB_ABORT      <= '1';

   end case;
end process;

end architecture LB_ROOT_CORE_FSM_ARCH;

