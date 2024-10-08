-- i2c_slave_top.vhd: Slave controller of I2C bus, MI32 master
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Puš <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

entity i2c_slave_top is
   generic (
      --+ I2C bit controller setting
      FILTER_LENGTH  : integer := 8;
      FILTER_SAMPLING: integer := 4;
      --* This device I2C address
      DEV_ADDR       : std_logic_vector(6 downto 0) := "0000000"
   );
   port (
      CLK      : in std_logic;
      RESET    : in std_logic;

      --+ MI32 interface (master direction)
      --+ Byte Enables are used!
      DWR   : out std_logic_vector(31 downto 0);
      ADDR  : out std_logic_vector(31 downto 0);
      RD    : out std_logic;
      WR    : out std_logic;
      BE    : out std_logic_vector( 3 downto 0);
      DRD   : in  std_logic_vector(31 downto 0);
      ARDY  : in  std_logic;
      DRDY  : in  std_logic;

      --+ i2c lines
      SCL_I   : in  std_logic;  -- i2c clock line input
      SCL_O   : out std_logic; -- i2c clock line output
      SCL_OEN : out std_logic; -- i2c clock line output enable, active low
      SDA_I   : in  std_logic;  -- i2c data line input
      SDA_O   : out std_logic; -- i2c data line output
      SDA_OEN : out std_logic  -- i2c data line output enable, active low
   );
end entity i2c_slave_top;

architecture structural of i2c_slave_top is

   -- FSM
   type t_states is (idle, cmd_dev_addr, wait_dev_addr,
                     cmd_mi_read, wait_mi_read,
                     cmd_reply, wait_reply,
                     cmd_read_addr_lo, wait_addr_lo,
                     cmd_read_addr_hi, wait_addr_hi,
                     cmd_read_data, wait_data,
                     cmd_mi_write);

   signal state            : t_states;
   signal next_state       : t_states;

   constant I2C_ACCEPT_BYTE: std_logic_vector(1 downto 0) := "01";
   constant I2C_REPLY_BYTE : std_logic_vector(1 downto 0) := "10";

   constant I2C_WRITE      : std_logic := '0';
   constant I2C_READ       : std_logic := '1';

   signal core_cmd         : std_logic_vector(1 downto 0);
   signal core_dev_addr_mask:std_logic_vector(7 downto 0);
   signal core_cmd_vld     : std_logic;
   signal core_cmd_rdy     : std_logic;

   signal core_cmd_ack     : std_logic;
   signal core_ack_out     : std_logic;
   signal core_dout        : std_logic_vector(7 downto 0);
   signal core_start       : std_logic;
   signal core_stop        : std_logic;

   signal reg_addr         : std_logic_vector(15 downto 0);
   signal reg_addr_ld_lo   : std_logic;
   signal reg_addr_ld_hi   : std_logic;
   signal reg_addr_inc     : std_logic;

   signal reg_drd          : std_logic_vector(7 downto 0);
   signal reg_drd_d        : std_logic_vector(7 downto 0);
   signal reg_drd_en       : std_logic;

   signal reg_dwr          : std_logic_vector(7 downto 0);
   signal reg_dwr_en       : std_logic;

begin

   ctrl : entity work.i2c_slave_byte_ctrl
   generic map(
      FILTER_LENGTH     => FILTER_LENGTH,
      FILTER_SAMPLING   => FILTER_SAMPLING
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,

      CMD      => core_cmd,
      DIN      => reg_drd,
      DEV_ADDR => DEV_ADDR & '0',
      DEV_ADDR_MASK=>core_dev_addr_mask,
      ACK_IN   => '0',
      CMD_VLD  => core_cmd_vld,
      CMD_RDY  => core_cmd_rdy,

      CMD_ACK  => core_cmd_ack,
      ACK_OUT  => core_ack_out,
      DOUT     => core_dout,

      START    => core_start,
      STOP     => core_stop,

      SCL_I    => SCL_I,
      SCL_O    => SCL_O,
      SCL_OEN  => SCL_OEN,
      SDA_I    => SDA_I,
      SDA_O    => SDA_O,
      SDA_OEN  => SDA_OEN
   );

   --* Address register
   reg_addr_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if reg_addr_ld_lo = '1' then
            reg_addr(7 downto 0) <= core_dout;
         end if;
         if reg_addr_ld_hi = '1' then
            reg_addr(15 downto 8) <= core_dout;
         end if;
         if reg_addr_inc = '1' then
            reg_addr <= reg_addr + 1;
         end if;
      end if;
   end process;

   ADDR <= X"0000" & reg_addr(15 downto 2) & "00";

   --* Byte enable is based on address two LSBs
   be_p : process(reg_addr)
   begin
      BE <= "0000";
      case reg_addr(1 downto 0) is
         when "00" => BE <= "0001";
         when "01" => BE <= "0010";
         when "10" => BE <= "0100";
         when "11" => BE <= "1000";
         when others =>
      end case;
   end process;

   --* Data from MI32
   reg_drd_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if reg_drd_en = '1' then
            reg_drd <= reg_drd_d;
         end if;
      end if;
   end process;

   --* Data to MI32
   reg_dwr_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if reg_dwr_en = '1' then
            reg_dwr <= core_dout;
         end if;
      end if;
   end process;

   -- Byte enable will tell which byte it actually is
   DWR <= reg_dwr & reg_dwr & reg_dwr & reg_dwr;

   --* FSM state memory
   fsm_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            state <= idle;
         else
            state <= next_state;
         end if;
      end if;
   end process;

   --* FSM next state logic
   next_state_p : process(state, core_start, ARDY, DRDY, core_cmd_rdy,
                          core_cmd_ack, core_dout, core_ack_out)
   begin
      next_state <= state;

      case state is
         when idle =>
            if core_start = '1' then
               next_state <= cmd_dev_addr;
            end if;

         when cmd_dev_addr =>
            if core_cmd_rdy = '1' then
               next_state <= wait_dev_addr;
            end if;

         when wait_dev_addr  =>
            if core_cmd_ack = '1' then
               if core_dout(7 downto 1) = DEV_ADDR then
                  if core_dout(0) = I2C_READ then
                     next_state <= cmd_mi_read;
                  else -- WRITE
                     next_state <= cmd_read_addr_lo;
                  end if;
               else  -- No device address match
                  next_state <= idle;
               end if;
            end if;

         when cmd_mi_read =>
            if ARDY = '1' then
               if DRDY = '1' then -- Skip waiting for MI32 reply
                  next_state <= cmd_reply;
               else
                  next_state <= wait_mi_read;
               end if;
            end if;

         when wait_mi_read =>
            if DRDY = '1' then
               next_state <= cmd_reply;
            end if;

         when cmd_reply =>
            if core_cmd_rdy = '1' then
               next_state <= wait_reply;
            end if;

         when wait_reply =>
            if core_cmd_ack = '1' then
               if core_ack_out = '0' then -- Continue reading
                  next_state <= cmd_mi_read;
               else -- Stop reading
                  next_state <= idle;
               end if;
            end if;

         when cmd_read_addr_lo =>
            if core_cmd_rdy = '1' then
               next_state <= wait_addr_lo;
            end if;

         when wait_addr_lo =>
            if core_cmd_ack = '1' then
               next_state <= cmd_read_addr_hi;
            end if;

         when cmd_read_addr_hi =>
            if core_cmd_rdy = '1' then
               next_state <= wait_addr_hi;
            end if;

         when wait_addr_hi =>
            if core_cmd_ack = '1' then
               next_state <= cmd_read_data; -- Suppose I2C will send next byte
            end if;                         -- to me

         when cmd_read_data =>
            if core_cmd_rdy = '1' then
               next_state <= wait_data;
            end if;

         when wait_data  =>
            if core_start = '1' then -- No next byte, completely new start
               next_state <= cmd_dev_addr;
            end if;
            if core_cmd_ack = '1' then -- I2C byte received
               next_state <= cmd_mi_write;
            end if;

         when cmd_mi_write =>
            if ARDY = '1' then
               next_state <= cmd_read_data; -- Suppose I2C will send next
            end if;                         -- byte to me

         when others =>

      end case;
   end process;

   --* FSM output logic
   output_logic_p : process(state, core_cmd_ack, reg_addr, DRDY, DRD, ARDY)
   begin
      core_cmd <= I2C_ACCEPT_BYTE;
      core_dev_addr_mask <= "00000001";
      core_cmd_vld <= '0';

      reg_addr_ld_lo <= '0';
      reg_addr_ld_hi <= '0';
      reg_addr_inc <= '0';

      reg_drd_en <= '0';
      reg_drd_d  <= DRD(7 downto 0);
      reg_dwr_en <= '0';

      RD    <= '0';
      WR    <= '0';

      case state is
         when idle =>

         when cmd_dev_addr =>
            core_cmd_vld <= '1';

         when wait_dev_addr =>

         when cmd_mi_read =>
            RD <= '1';
            if DRDY = '1' then
               reg_drd_en <= '1';
               case reg_addr(1 downto 0) is
                  when "00" => reg_drd_d <= DRD( 7 downto  0);
                  when "01" => reg_drd_d <= DRD(15 downto  8);
                  when "10" => reg_drd_d <= DRD(23 downto 16);
                  when "11" => reg_drd_d <= DRD(31 downto 24);
                  when others =>
               end case;
               reg_addr_inc <= '1';
            end if;

         when wait_mi_read =>
            if DRDY = '1' then
               reg_drd_en <= '1';
               case reg_addr(1 downto 0) is
                  when "00" => reg_drd_d <= DRD( 7 downto  0);
                  when "01" => reg_drd_d <= DRD(15 downto  8);
                  when "10" => reg_drd_d <= DRD(23 downto 16);
                  when "11" => reg_drd_d <= DRD(31 downto 24);
                  when others =>
               end case;
               reg_addr_inc <= '1';
            end if;

         when cmd_reply =>
            core_cmd <= I2C_REPLY_BYTE;
            core_cmd_vld <=  '1';

         when wait_reply =>

         when cmd_read_addr_lo =>
            core_dev_addr_mask <= "11111111";
            core_cmd_vld <= '1';

         when wait_addr_lo =>
            if core_cmd_ack = '1' then
               reg_addr_ld_lo <= '1';
            end if;

         when cmd_read_addr_hi =>
            core_dev_addr_mask <= "11111111";
            core_cmd_vld <= '1';

         when wait_addr_hi =>
            if core_cmd_ack = '1' then
               reg_addr_ld_hi <= '1';
            end if;

         when cmd_read_data =>
            core_dev_addr_mask <= "11111111";
            core_cmd_vld <= '1';

         when wait_data =>
            if core_cmd_ack = '1' then
               reg_dwr_en <= '1';
            end if;

         when cmd_mi_write =>
            WR <= '1';
            if ARDY = '1' then
               reg_addr_inc <= '1';
            end if;

         when others =>
      end case;
   end process;

end architecture structural;
