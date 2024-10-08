-- i2c_slave_bit_ctrl.vhd: Bit slave controller of I2C bus
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

entity i2c_slave_bit_ctrl is
   generic (
      FILTER_LENGTH  : integer := 4;
      FILTER_SAMPLING: integer := 2
   );
   port (
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      --* Command code input
      CMD      : in  std_logic_vector(1 downto 0);
      --* Data to be written to the bus, in case of I2C_REPLY_BIT command.
      DIN      : in  std_logic;
      --* Command valid (pulse)
      CMD_VLD  : in  std_logic;
      --* Ready to accept command
      CMD_RDY  : out std_logic;

      --* Command completed (pulse)
      CMD_ACK  : out std_logic;
      --* Data bit from bus. Valid with CMD_ACK.
      DOUT     : out std_logic;

      --* START condidion detected (pulse)
      START    : out std_logic;
      --* STOP condidion detected (pulse)
      STOP     : out std_logic;

      --+ i2c lines
      SCL_I   : in  std_logic; -- i2c clock line input
      SCL_O   : out std_logic; -- i2c clock line output
      SCL_OEN : out std_logic; -- i2c clock line output enable, active low
      SDA_I   : in  std_logic; -- i2c data line input
      SDA_O   : out std_logic; -- i2c data line output
      SDA_OEN : out std_logic  -- i2c data line output enable, active low
   );
end entity i2c_slave_bit_ctrl;

architecture structural of i2c_slave_bit_ctrl is
   constant I2C_ACCEPT_BIT       : std_logic_vector(1 downto 0) := "01";
   constant I2C_REPLY_BIT        : std_logic_vector(1 downto 0) := "10";

   type states is (idle, accept_wf0, accept_wf1, accept_bit,
                   reply_wf0, reply_win0, reply_wf01, reply_wf010, reply_bit);
	signal state, next_state : states;

   -- I2C Output register for each signal
   signal reg_sda_oen         : std_logic;
	signal reg_sda_oen_in      : std_logic;

	signal sSCL, sSDA          : std_logic; -- synchronized SCL and SDA inputs
	signal fSCL, fSDA          : std_logic; -- filtered SCL and SDA inputs
	signal dSCL, dSDA          : std_logic; -- delayed SCL and SDA inputs

   signal sta_condition       : std_logic;  -- start detected
   signal sto_condition       : std_logic;  -- stop detected

   signal reg_dout            : std_logic;
   signal reg_din             : std_logic;
   signal iCMD_RDY            : std_logic;

begin

   --* synchronize and delay SCL and SDA inputs
   sync_scl_sda: process(CLK)
   begin
	   if (CLK'event and CLK = '1') then
	      if (RESET = '1') then
	         sSCL <= '1';
	         sSDA <= '1';
	         dSCL <= '1';
	         dSDA <= '1';
	      else
	         sSCL <= scl_i;
	         sSDA <= sda_i;
	         dSCL <= fSCL;
	         dSDA <= fSDA;
	      end if;
	   end if;
   end process sync_SCL_SDA;

   --* Filter glitches at SCL input caused by slow edges
   filter_scl : entity work.glitch_filter
   generic map(
      FILTER_LENGTH     => FILTER_LENGTH,
      FILTER_SAMPLING   => FILTER_SAMPLING,
      INIT              => '1'
   )
   port map(
      CLK   => CLK,
      RESET => RESET,
      DIN   => sSCL,
      DOUT  => fSCL
   );

   --* Filter glitches at SDA input caused by slow edges
   filter_sda : entity work.glitch_filter
   generic map(
      FILTER_LENGTH     => FILTER_LENGTH,
      FILTER_SAMPLING   => FILTER_SAMPLING,
      INIT              => '1'
   )
   port map(
      CLK   => CLK,
      RESET => RESET,
      DIN   => sSDA,
      DOUT  => fSDA
   );

   --* detect start condition => detect falling edge on SDA while SCL is high
   --* detect stop condition  => detect rising edge on SDA while SCL is high
   detect_sta_sto: process(CLK)
   begin
	   if (CLK'event and CLK = '1') then
	      if (RESET = '1') then
	         sta_condition <= '0';
	         sto_condition <= '0';
	      else
	         sta_condition <= (not fSDA and dSDA) and fSCL;
	         sto_condition <= (fSDA and not dSDA) and fSCL;
	      end if;
	   end if;
   end process detect_sta_sto;
   START <= sta_condition;
   STOP <= sto_condition;

	-- generate dout signal, store dout on rising edge of SCL
	gen_dout: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (fSCL = '1' and dSCL = '0') then
            reg_dout <= fSDA;
         end if;
      end if;
   end process gen_dout;
   DOUT <= reg_dout;

   -- Store DIN in case of I2C_REPLY_BIT command
   reg_din_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if CMD = I2C_REPLY_BIT and CMD_VLD = '1' and iCMD_RDY = '1' then
            reg_din <= DIN;
         end if;
      end if;
   end process;

   CMD_RDY <= iCMD_RDY;

   -- Output register for I2C line
   i2c_regs_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_sda_oen <= '1';
         else
            reg_sda_oen <= reg_sda_oen_in;
         end if;
      end if;
   end process;
   SCL_O <= '0'; -- Constant values
   SCL_OEN <= '1';
   SDA_O <= '0';
   SDA_OEN <= reg_sda_oen; -- Only SDA_OEN may be changed by slave ctrl

   --* FSM state memory
   next_state_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' or sta_condition = '1' then
            -- START also resets the controller!
            state <= idle;
         else
            state <= next_state;
         end if;
      end if;
   end process;

	--* FSM next state logic
	next_state_logic : process (state, CMD, CMD_VLD, iCMD_RDY,
                               fSDA, fSCL)
	begin
      next_state <= state; -- Default value
      case (state) is
         when idle =>
            if CMD_VLD = '1' and iCMD_RDY = '1' and CMD = I2C_ACCEPT_BIT then
               next_state <= accept_wf0;
            end if;
            if CMD_VLD = '1' and iCMD_RDY = '1' and CMD = I2C_REPLY_BIT then
               next_state <= reply_wf0;
            end if;

         when accept_wf0 =>
            if fSCL = '0' then
               next_state <= accept_wf1;
            end if;

         when accept_wf1 =>
            if fSCL = '1' then
               next_state <= accept_bit;
            end if;

         when accept_bit =>
            next_state <= idle;

         when reply_wf0 =>
            if fSCL = '0' then
               next_state <= reply_wf01;
            end if;

         when reply_wf01 =>
            if fSCL = '1' then
               next_state <= reply_wf010;
            end if;

         when reply_wf010 =>
            if fSCL = '0' then
               next_state <= reply_bit;
            end if;

         when reply_bit =>
            next_state <= idle;

         when others =>
            next_state <= idle;
      end case;
	end process next_state_logic;

   --* FSM output logic
   output_logic_p : process(state, fSDA, fSCL, reg_din)
   begin
      reg_sda_oen_in <= '1';
      iCMD_RDY <= '0';
      CMD_ACK <= '0';

      case (state) is
         when idle =>
            iCMD_RDY <= '1';

         when accept_wf0 =>
         when accept_wf1 =>
         when accept_bit =>
            CMD_ACK <= '1';

         when reply_wf0 =>
         when reply_wf01 => -- Wait for SCL=1, already sending data
            reg_sda_oen_in <= reg_din;
         when reply_wf010 => -- Keep data while SCL=1
            reg_sda_oen_in <= reg_din;
         when reply_bit =>
            CMD_ACK <= '1';
         when others =>
      end case;

   end process;

end architecture structural;

