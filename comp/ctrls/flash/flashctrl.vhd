-- flashctrl.vhd : Asynchronous mode parallel FLASH interface
-- Copyright (C) 2015 CESNET
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
-- NOTE: DWR port structure
--
-- 63     59                       31        15        0
-- +-----+------------------------+---------------------+
-- | CMD |       ADDRESS (28b)    |  RSVD    | DATA(16b)|
-- +-----+------------------------+---------------------+
--
-- CMDs: "0001": FLASH read cycle
--       "0010": FLASH write cycle, ADDRESS and DATA = don't care
--       others: RESERVED
--
-- DRD port:
--
-- 63                                       16  15       0
-- +---------------------------------------+---+----------+
-- |                RSVD                   |RDY| DATA(16b)|
-- +---------------------------------------+---+----------+
--
-- RDY: '0' = controller busy, '1' controller ready for next command
--
library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity flashctrl is
   generic (
      -- Period of the CLK (truncated when non-integer)
      CLK_PERIOD : natural := 8;
      ADDR_WIDTH : integer := 27
   );
   port (
      -- sync reset
      RESET     : in std_logic;
      -- clock
      CLK       : in std_logic;

      -- =================
      -- Command interface
      -- =================

      -- Write data (cmd & data to be written to flash)
      DWR       : in  std_logic_vector(63 downto 0);
      -- command strobe
      DWR_WR    : in  std_logic;
      -- Read data (data & status from flash)
      DRD       : out std_logic_vector(63 downto 0);

      -- =================
      -- FLASH interface
      -- =================

      -- Flash address
      AD        : out std_logic_vector(ADDR_WIDTH-1 downto 0 );
      -- Data from flash
      D_I       : in  std_logic_vector(15 downto 0 );
      -- Data to flash
      D_O       : out std_logic_vector(15 downto 0 );
      -- D output enable (HI-Z on data disable). Active high
      D_OE      : out std_logic;
      -- Chip select
      CS_N      : out std_logic;
      -- Output drivers enable
      OE_N      : out std_logic;
      -- Flash reset
      RST_N     : out std_logic;
      -- Write anable
      WE_N      : out std_logic;

      -- =====================
      --  Others FLASH signals
      -- =====================

      -- WAIT      : in  std_logic;  -- Synchronous mode only
      -- ADV_N     : out std_logic;  -- Synchronous mode only. Tie LOW
      -- WP_N      : out std_logic;  -- Write protect - tie HIGH
      -- CLK       : out std_logic;  -- synchronous mode clock - tie LOW or HIGH
      -- Debug
      STATE     : out std_logic_vector(7 downto 0)
   );
end flashctrl;

architecture structural of flashctrl is

  -- ===================
  -- Flash Memory Timing
  -- ===================

  -- Access time
  constant T_ACC  : integer := (105/CLK_PERIOD) + 1;
  -- Page access time
  constant T_PACC : integer := (25/CLK_PERIOD) + 1;
  -- Write pulse low time
  constant T_WP   : integer := (50/CLK_PERIOD) + 1;
  -- Write pulse high time;
  constant T_WPH  : integer := (20/CLK_PERIOD) + 1;

  --
  type TYPE_CONFIG_FSM_STATE is ( STATE_IDLE,
                                  STATE_READ,
                                  STATE_WRITE0,
                                  STATE_WRITE1
                                  );

  signal fsm_state : TYPE_CONFIG_FSM_STATE;

  --
  signal counter : std_logic_vector(8 downto 0);
  signal counter_top : std_logic_vector( counter'range );
  signal counter_reset    : std_logic;
  signal counter_finish   : std_logic;
  signal counter_finished : std_logic;
  --
  signal flash_memory_address : std_logic_vector( AD'range ) := (others => '1');
  signal flash_memory_data_o : std_logic_vector( D_O'range );
  signal flash_memory_data : std_logic_vector( D_I'range );
  signal flash_memory_cs_n : std_logic;
  signal flash_memory_oe_n : std_logic;
  signal flash_memory_fd_oe: std_logic;
  signal flash_memory_we_n : std_logic;

  signal busy            : std_logic;

attribute iob: string;
attribute iob of flash_memory_data_o  : signal is "TRUE";
attribute iob of flash_memory_data    : signal is "TRUE";
attribute iob of flash_memory_address : signal is "TRUE";
attribute iob of flash_memory_cs_n    : signal is "TRUE";
attribute iob of flash_memory_fd_oe   : signal is "TRUE";
attribute iob of flash_memory_we_n    : signal is "TRUE";

begin

  -- Flash
  AD    <= flash_memory_address;
  CS_N  <= flash_memory_cs_n;
  OE_N  <= flash_memory_oe_n;
  D_OE  <= flash_memory_fd_oe;
  D_O   <= flash_memory_data_o;
  WE_N  <= flash_memory_we_n;    -- Read only

  flash_memory_data <= D_I;

  DRD(16) <= not busy;

  process( RESET, CLK )
  begin
    if( RESET = '1' )then
      counter <= (others=>'0');
      counter_finish <= '0';
      counter_finished <= '0';
    elsif( CLK='1' and CLK'event )then
      if (counter_reset = '1' )then
         counter <= (others=>'0');
      else
         counter <= counter + 1;
      end if;

      if (counter = counter_top )then
         counter_finish <= '1';
      else
         counter_finish <= '0';
      end if;

      if (counter_reset = '1' )then
         counter_finished <= '0';
      elsif (counter = counter_top )then
         counter_finished <= '1';
      end if;

    end if;
  end process;

  DEBUG_STATE_OUT: process(FSM_STATE)
  begin
     case FSM_STATE is
        when STATE_IDLE   => STATE <= X"00";
        when STATE_READ   => STATE <= X"02";
        when STATE_WRITE0 => STATE <= X"0a";
        when STATE_WRITE1 => STATE <= X"0b";
        when others       => STATE <= X"FF";
     end case;
  end process;

  --
  process( RESET, CLK )
  begin
    if CLK = '1' and CLK'event then

      flash_memory_cs_n  <= '1';
      flash_memory_oe_n  <= '1';
      flash_memory_fd_oe <= '0';
      flash_memory_we_n  <= '1';
      counter_reset      <= '1';
      busy               <= '1';
      RST_N              <= '1';

      case FSM_STATE is
        when STATE_IDLE =>
            flash_memory_fd_oe <= '0';  -- Disable driving data bus
            flash_memory_cs_n  <= '1';  --
            flash_memory_we_n  <= '1';  --
            flash_memory_oe_n  <= '1';  -- Flash output disable
            counter_reset      <= '1';  -- Stop the counter
            busy               <= '0';
            if (DWR_WR = '1') then
               flash_memory_address <= DWR(32+flash_memory_address'high downto 32);
               flash_memory_data_o  <= DWR(flash_memory_data_o'high downto 0);
               busy                 <= '1';
               if (DWR(63 downto 60) = "0001") then
                  fsm_state            <= STATE_READ;
               elsif (DWR(63 downto 60) = "0010") then
                  fsm_state           <= STATE_WRITE0;
               end if;
            end if;
            -- DRD(31 downto 28) <= X"1";


        -- FLASH write seq:
        -- 0. CE=1; WE=1; Address; Data -> goto 2. (SETUP)
        -- 1. CE=0; WE=0; wait Twp  -> goto 3. (WRITE_PULSE, data latched on WE->1, addr latched on CE->0) (35ns)
        -- 2. CE=0; WE=1; wait Twc-Twp -> goto 4. (130-35=95ns)
        -- 4. done

        -- FLASH write - phase 1 - pull WE low, SETUP data and address
        when STATE_WRITE0 =>
           flash_memory_fd_oe   <= '1'; -- Drive data bus
           flash_memory_cs_n    <= '0'; --
           flash_memory_we_n    <= '0'; --
           flash_memory_oe_n    <= '1'; -- Flash output disable
           counter_reset        <= '0'; -- Run the counter
           counter_top          <= conv_std_logic_vector(T_WP, counter_top'length);
           if (counter_finish = '1') then
              fsm_state <= STATE_WRITE1;
              counter_reset <= '1';
           end if;
           -- DRD(31 downto 28) <= X"2";

        -- FLASH write - phase 2 - put WE high, hold data for T_WPH time
        when STATE_WRITE1 =>
           flash_memory_fd_oe   <= '1'; -- Drive data bus
           flash_memory_cs_n    <= '0'; --
           flash_memory_we_n    <= '1'; --
           flash_memory_oe_n    <= '1'; -- Flash output disable
           counter_reset        <= '0';
           counter_top          <= conv_std_logic_vector(T_WPH, counter_top'length );
           if (counter_finish = '1') then
              fsm_state <= STATE_IDLE;
              flash_memory_cs_n <= '1';
              busy              <= '0';
           end if;
           -- DRD(31 downto 28) <= X"3";

        -- FLASH memory read
        when STATE_READ =>
           flash_memory_fd_oe  <= '0'; -- Disable driving data bus
           flash_memory_cs_n   <= '0'; --
           flash_memory_we_n   <= '1'; --
           flash_memory_oe_n   <= '0'; -- Flash output enable
           counter_top         <= conv_std_logic_vector(T_ACC, counter_top'length );
           counter_reset       <= '0';
           if (counter_finish = '1') then
              fsm_state         <= STATE_IDLE;
              DRD(flash_memory_data'high downto 0) <= flash_memory_data;
              flash_memory_cs_n <= '1';
              busy              <= '0';
           end if;
           -- DRD(31 downto 28) <= X"4";

        when others =>
      end case;

      if (RESET = '1')then
          fsm_state           <= STATE_IDLE;
          counter_reset       <= '1';
          flash_memory_cs_n   <= '1';
          flash_memory_oe_n   <= '1';
          -- flash_memory_fd_oe  <= '0'; -- Cannot be placed in the IOB when reset
          flash_memory_we_n   <= '1';
          busy                <= '0';
          RST_N               <= '0';
      end if;

    end if;
  end process;

end structural;
