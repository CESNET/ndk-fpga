--
-- lb_root_core.vhd: Local Bus Root Core
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ROOT_CORE is
   generic (
      ABORT_CNT_WIDTH : integer -- Abort TIMEOUT is 2**WIDTH
                                -- Abort TIME is also 2**WIDTH
   );
   port (
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;

      -- Buffer Interface
      BUFFER_ADDR       : in  std_logic_vector(31 downto 0);
      BUFFER_SOF        : in  std_logic;
      BUFFER_EOF        : in  std_logic;
      BUFFER_DATA       : in  std_logic_vector(63 downto 0);
      BUFFER_BE         : in  std_logic_vector(7 downto 0);
      BUFFER_RD         : in  std_logic;
      BUFFER_WR         : in  std_logic;
      BUFFER_VLD        : in  std_logic;
      BUFFER_NEXT       : out std_logic;
      BUFFER_DRD        : out std_logic_vector(63 downto 0);
      BUFFER_DRDY       : out std_logic;
      BUFFER_DRD_LAST   : out std_logic;

      -- Localbus Interface
      LB_DWR           : out std_logic_vector(15 downto 0);
      LB_BE            : out std_logic_vector(1 downto 0);
      LB_ADS           : out std_logic;
      LB_RD            : out std_logic;
      LB_WR            : out std_logic;
      LB_DRD           : in  std_logic_vector(15 downto 0);
      LB_RDY           : in  std_logic;
      LB_ERR           : in  std_logic;
      LB_ABORT         : out std_logic
   );
end entity LB_ROOT_CORE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ROOT_CORE_ARCH of LB_ROOT_CORE is
    -- Local Bus Mapping Signals
    signal lb_dwr_out              : std_logic_vector(15 downto 0);
    signal lb_be_out               : std_logic_vector(1 downto 0);
    signal lb_ads_out              : std_logic;
    signal lb_rd_out               : std_logic;
    signal lb_wr_out               : std_logic;
    signal aux_lb_rd_out           : std_logic;
    signal aux_lb_wr_out           : std_logic;
    signal lb_drd_in               : std_logic_vector(15 downto 0);
    signal lb_rdy_in               : std_logic;
    signal lb_err_in               : std_logic;
    signal lb_abort_out            : std_logic;

    -- Multiplexors
    signal data_mux                : std_logic_vector(15 downto 0);
    signal data_mux_sel            : std_logic_vector( 1 downto 0);
    signal be_mux                  : std_logic_vector( 1 downto 0);
    signal be_mux_sel              : std_logic_vector( 1 downto 0);
    signal addr_data_mux           : std_logic_vector(15 downto 0);
    signal addr_data_mux_sel       : std_logic_vector( 1 downto 0);
    signal drd_reg                 : std_logic_vector(63 downto 0);
    signal drd_dec                 : std_logic_vector( 3 downto 0);
    signal drd_dec_sel             : std_logic_vector( 1 downto 0);

    -- Counters
    signal init_counters           : std_logic;
    signal data_counters_init      : std_logic_vector(1 downto 0);
    signal data_out_cnt            : std_logic_vector( 1 downto 0);
    signal data_out_cnt_ce         : std_logic;
    signal data_in_cnt             : std_logic_vector( 1 downto 0);
    signal pending_items_cnt_up    : std_logic;
    signal pending_items_cnt_down  : std_logic;
    signal pending_items_cnt       : std_logic_vector( 3 downto 0);

    -- FSM Localbus signals
    signal fsm_ads                 : std_logic;
    signal fsm_rd                  : std_logic;
    signal fsm_wr                  : std_logic;
    signal fsm_abort               : std_logic;

    -- Flags and status signals
    signal gen_abort_flag          : std_logic;
    signal fsm_waiting_for_rdy     : std_logic;
    signal fsm_reading_flag        : std_logic;
    signal drdy_overflow           : std_logic;
    signal drdy_last               : std_logic;
    signal vld_cnt                 : std_logic;
    signal first_do_flag           : std_logic;
    signal fsm_last_rq             : std_logic;
    signal abort_cnt_ce            : std_logic;
    signal abort_cnt_rst           : std_logic;
    -- This counter is one bit wider !!! than counter in the core FSM
    signal abort_cnt               : std_logic_vector(ABORT_CNT_WIDTH downto 0);


begin

-- ----------------------------------------------------------------------------
-- LOCAL BUS MAPING
-------------------------------------------------------------------------------
localbus_pipe: process(RESET, CLK)
begin
   if (RESET = '1') then
       lb_dwr_out     <= (others => '0');
       lb_be_out      <= (others => '0');
       lb_ads_out     <= '0';
       aux_lb_rd_out  <= '0';
       aux_lb_wr_out  <= '0';
       lb_abort_out   <= '0';
       lb_drd_in      <= (others => '0');
       lb_rdy_in      <= '0';
       lb_err_in      <= '0';
   elsif (CLK'event AND CLK = '1') then
       lb_dwr_out    <= addr_data_mux;
       lb_be_out     <= be_mux;
       lb_ads_out    <= fsm_ads;
       aux_lb_rd_out <= fsm_rd;
       aux_lb_wr_out <= fsm_wr;
       lb_abort_out  <= fsm_abort;
       lb_drd_in     <= LB_DRD;
       lb_rdy_in     <= LB_RDY;
       lb_err_in     <= LB_ERR;
   end if;
end process;

LB_DWR   <= lb_dwr_out;
LB_BE    <= lb_be_out;
LB_ADS   <= lb_ads_out;
LB_RD    <= lb_rd_out;
LB_WR    <= lb_wr_out;
LB_ABORT <= lb_abort_out;

-- ---------------------------------------------------------------------------
-- DON'T SEND BE = 0  (when end of IB transaction have last four BE = 0)
-- ---------------------------------------------------------------------------
lb_rd_out <= '1' when (aux_lb_rd_out='1' and not (lb_be_out(0) ='0' and vld_cnt='0' and first_do_flag = '0')) else '0';
lb_wr_out <= '1' when (aux_lb_wr_out='1' and not (lb_be_out(0) ='0' and vld_cnt='0' and first_do_flag = '0')) else '0';

-- Signal is set when unuseful data is trying to send throw localbus
-- this signal is used when last 4 IB BE is set to 0
fsm_last_rq <= '1' when (aux_lb_wr_out='1' or aux_lb_rd_out='1') and
                        (vld_cnt='0' and lb_be_out(0) ='0' and first_do_flag = '0') else '0';

-- vld_cnt counter -------------------------------------------------------
vld_cntp: process(RESET, CLK)
begin
   if (RESET = '1') then
      vld_cnt       <= '0';
      first_do_flag <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (aux_lb_rd_out='1' or aux_lb_wr_out='1') then
         vld_cnt       <= not vld_cnt;
         first_do_flag <= '0';
      end if;
      if (init_counters = '1') then
         vld_cnt       <= '0';
         first_do_flag <= '1';
      end if;
   end if;
end process;


-- ---------------------------------------------------------------------------
-- GENERATING ABORT (counters and logic)
------------------------------------------------------------------------------
-- Generate abort (will be used in the future)
--gen_abort_flag <= '0';
gen_abort_flag <= abort_cnt(ABORT_CNT_WIDTH) or lb_err_in;
abort_cnt_ce   <= '1' when (pending_items_cnt > 0) else '0';
abort_cnt_rst  <= lb_rdy_in or init_counters;

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


-- ---------------------------------------------------------------------------
-- CORE FSM (Create and control transactions)
------------------------------------------------------------------------------
LB_ROOT_CORE_FSM_U : entity work.LB_ROOT_CORE_FSM
   generic map (
      ABORT_CNT_WIDTH     => ABORT_CNT_WIDTH
   )
   port map (
   -- Common Interface
   CLK                    => CLK,                  -- Clk
   RESET                  => RESET,                -- Reset
   -- Buffer Interface
   BUFFER_SOF             => BUFFER_SOF,           -- Start of Frame
   BUFFER_EOF             => BUFFER_EOF,           -- End Of Frame
   BUFFER_RD              => BUFFER_RD,            -- Read
   BUFFER_WR              => BUFFER_WR,            -- Write
   BUFFER_VLD             => BUFFER_VLD,           -- Item VLD
   BUFFER_NEXT            => BUFFER_NEXT,          -- Next 64 bits Item
   -- Core control Interface
   INIT_COUNTERS          => init_counters,        -- Init counters (Based on BE)
   ADDR_DATA_MUX_SEL      => addr_data_mux_sel,    -- Select LB_DWR (ADDR_L,ADDR_H,DATA)
   DATA_OUT_CNT_CE        => data_out_cnt_ce,      -- Increment data_out_counter (select 16 bit item from 64 bit word)
   WAIT_FOR_ALL_RDY       => fsm_waiting_for_rdy,  -- FSM is waiting for all rdy signals
   READING_FLAG           => fsm_reading_flag,     -- Is set when reading operation

   -- Core Status Interface
   GEN_ABORT_FLAG         => gen_abort_flag,       -- When signal is set FSM generate ABORT
   DATA_OUT_CNT           => data_out_cnt,         -- Status of data_out_counter
   PENDING_CNT            => pending_items_cnt,    -- Status of pending_items_counter
   LAST_REQ               => fsm_last_rq,          -- Is set when last rq is in pipeline

   -- Local Bus Output Interface
   LB_ADS                 => fsm_ads,              -- Address Select
   LB_RD                  => fsm_rd,               -- Read
   LB_WR                  => fsm_wr,               -- Write
   LB_ABORT               => fsm_abort             -- Abort Generation
   );



-- ---------------------------------------------------------------------------
-- PENDING ITEMS COUNTER (only 16 items can be send without rdy)
------------------------------------------------------------------------------
pending_items_cnt_up    <= (lb_wr_out or lb_rd_out) and not lb_rdy_in;
pending_items_cnt_down  <= (not lb_rd_out and not lb_wr_out) and lb_rdy_in;

pending_items_cntp: process(RESET, CLK)
begin
   if (RESET = '1') then
      pending_items_cnt <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (pending_items_cnt_up = '1') then
         pending_items_cnt <= pending_items_cnt + 1;
      end if;
      if (pending_items_cnt_down = '1') then
         pending_items_cnt <= pending_items_cnt - 1;
      end if;
      if (init_counters = '1') then
         pending_items_cnt <= (others => '0');
      end if;
   end if;
end process;


-- ---------------------------------------------------------------------------
-- READ AND WRITE PART (Multiplexors, 64 -> 16)
------------------------------------------------------------------------------

data_counters_init <= "10" when BUFFER_BE(3 downto 0) = "0000" else "00";

-- data_out_cnt counter ------------------------------------------------------
data_out_cntp: process(RESET, CLK)
begin
   if (RESET = '1') then
      data_out_cnt <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (data_out_cnt_ce = '1') then
         data_out_cnt <= data_out_cnt + 1;
      end if;
      if (init_counters = '1') then
         data_out_cnt <= data_counters_init;
      end if;
   end if;
end process;

-- multiplexor data_mux ------------------------------------------------------
data_mux_sel <= data_out_cnt;

data_muxp: process(data_mux_sel, BUFFER_DATA)
begin
   case data_mux_sel is
      when "00"   => data_mux <= BUFFER_DATA(15 downto  0);
      when "01"   => data_mux <= BUFFER_DATA(31 downto 16);
      when "10"   => data_mux <= BUFFER_DATA(47 downto 32);
      when "11"   => data_mux <= BUFFER_DATA(63 downto 48);
      when others => data_mux <= (others => 'X');
   end case;
end process;

-- multiplexor be_mux --------------------------------------------------------
be_mux_sel <= data_out_cnt;

be_muxp: process(be_mux_sel, BUFFER_BE)
begin
   case be_mux_sel is
      when "00"   => be_mux <= BUFFER_BE(1 downto 0);
      when "01"   => be_mux <= BUFFER_BE(3 downto 2);
      when "10"   => be_mux <= BUFFER_BE(5 downto 4);
      when "11"   => be_mux <= BUFFER_BE(7 downto 6);
      when others => be_mux <= (others => 'X');
   end case;
end process;

-- multiplexor addr_data_mux -------------------------------------------------
addr_data_muxp: process(addr_data_mux_sel, BUFFER_ADDR, data_mux)
begin
   case addr_data_mux_sel is
      when "00"   => addr_data_mux <= BUFFER_ADDR(15 downto  0);
      when "01"   => addr_data_mux <= BUFFER_ADDR(31 downto 16);
      when "10"   => addr_data_mux <= data_mux;
      when others => addr_data_mux <= (others => 'X');
   end case;
end process;


-- ---------------------------------------------------------------------------
-- DRD PART (Readed data from localbus)
------------------------------------------------------------------------------
BUFFER_DRD      <= drd_reg;
-- fsm reading flag is used due to same fsm for RD and WR
BUFFER_DRDY     <= (drdy_overflow or drdy_last) and fsm_reading_flag;
BUFFER_DRD_LAST <= drdy_last and fsm_reading_flag;


-- data_in_cnt counter -------------------------------------------------------
data_in_cntp: process(RESET, CLK)
begin
   if (RESET = '1') then
      data_in_cnt <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (lb_rdy_in = '1') then
         data_in_cnt <= data_in_cnt + 1;
      end if;
      if (init_counters = '1') then
         data_in_cnt <= data_counters_init;
      end if;
   end if;
end process;

-- decoder drd_dec -----------------------------------------------------------
drd_dec_sel <= data_in_cnt;

drd_decp: process(drd_dec_sel)
begin
   case drd_dec_sel is
      when "00"   => drd_dec <= "0001";
      when "01"   => drd_dec <= "0010";
      when "10"   => drd_dec <= "0100";
      when "11"   => drd_dec <= "1000";
      when others => drd_dec <= (others => 'X');
   end case;
end process;

-- register drd_reg ----------------------------------------------------------
drd_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      drd_reg       <= (others => '0');
      drdy_overflow <= '0';
      drdy_last     <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (drd_dec(3) = '1' and lb_rdy_in = '1') then
         drdy_overflow <= '1';
      else
         drdy_overflow <= '0';
      end if;

      if (lb_rdy_in = '1' and fsm_waiting_for_rdy='1' and pending_items_cnt=1) then
         drdy_last <= '1';
      else
         drdy_last <= '0';
      end if;

      if (drd_dec(0) = '1' and lb_rdy_in = '1') then
         drd_reg(15 downto  0) <= lb_drd_in;
      end if;
      if (drd_dec(1) = '1' and lb_rdy_in = '1') then
         drd_reg(31 downto 16) <= lb_drd_in;
      end if;
      if (drd_dec(2) = '1' and lb_rdy_in = '1') then
         drd_reg(47 downto 32) <= lb_drd_in;
      end if;
      if (drd_dec(3) = '1' and lb_rdy_in = '1') then
         drd_reg(63 downto 48) <= lb_drd_in;
      end if;
   end if;
end process;




end architecture LB_ROOT_CORE_ARCH;
