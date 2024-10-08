-- id_comp.vhd
--!
--! @file
--! \brief Design identification with MI32 interface
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2012
--!
--! @section License
--!
--! Copyright (C) 2012 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
--! Part of IEEE standard library.
use IEEE.numeric_std.all;

--! \brief Design identification component with MI32 interface.
--! \details Uses MI32 address space 0x00-0x7F.
entity ID_COMP is
  generic (
    --! \brief Identification of project
    --! \details Readable from address 0x04 as the highest 2 bytes.
    PROJECT_ID     : std_logic_vector(15 downto 0):= X"0000";
    --! \brief Software version major number
    --! \details Readable from address 0x04 as the second lowest bytes.
    SW_MAJOR       : std_logic_vector( 7 downto 0):=   X"00";
    --! \brief Software version minor number
    --! \details Readable from address 0x04 as the lowest byte.
    SW_MINOR       : std_logic_vector( 7 downto 0):=   X"00";
    --! \brief Hardware version major number
    --! \details Readable from address 0x08 as the highest 2 bytes.
    HW_MAJOR       : std_logic_vector(15 downto 0):= X"0000";
    --! \brief Hardware version minor number
    --! \details Readable from address 0x08 as the lowest 2 bytes.
    HW_MINOR       : std_logic_vector(15 downto 0):= X"0000";
    --! \brief Text identificator of project
    --! \details Readable from addresses 0x20-0x3f.
    PROJECT_TEXT   : std_logic_vector(255 downto 0) :=
    X"0000000000000000000000000000000000000000000000000000000000000000";
    --! \brief Number of DMA channels from FPGA to RAM
    --! \details Readable from address 0x40 as the lowest byte.
    RX_CHANNELS    : std_logic_vector(7 downto 0):= X"FF";
    --! \brief Number of DMA channels from RAM to FPGA
    --! \details Readable from address 0x40 as the second lowest byte.
    TX_CHANNELS    : std_logic_vector(7 downto 0):= X"FF";
    --! \brief Version of this module major number
    --! \details Readable from address 0x48 as the second lowest byte. Should not be changed when instantiating.
    ID_MAJOR       : std_logic_vector(7 downto 0) := X"01";
    --! \brief Version of this module minor number
    --! \details Readable from address 0x48 as the lowest byte. Should not be changed when instantiating.
    ID_MINOR       : std_logic_vector(7 downto 0) := X"04";
    --! \brief Version of NetCOPE major number
    --! \details Readable from address 0x48 as the highest byte.
    NETCOPE_MAJOR  : std_logic_vector(7 downto 0) := X"00";
    --! \brief Version of NetCOPE minor number
    --! \details Readable from address 0x48 as the second highest byte.
    NETCOPE_MINOR  : std_logic_vector(7 downto 0) := X"00";
    --! \brief Date and time of building
    --! \details Readable from address 0x4C.
    BUILD_TIME     : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief Builder's Unix User ID
    --! \details Readable from address 0x50.
    BUILD_UID      : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief CLK_ICS frequency in MHz
    --! \details Readable from address 0x40 as the highest 2 bytes.
    ICS_FREQUENCY  : std_logic_vector(15 downto 0) := X"00BB";
    --! \brief User generic0 (no default meaning)
    --! \details Readable from address 0x58.
    USER_GENERIC0  : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief User generic1 (no default meaning)
    --! \details Readable from address 0x5C.
    USER_GENERIC1  : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief User generic2 (no default meaning)
    --! \details Readable from address 0x60.
    USER_GENERIC2  : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief User generic3 (no default meaning)
    --! \details Readable from address 0x64.
    USER_GENERIC3  : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief Max MTU of RX packets (in Bytes) including Ethernet, MACs and FSC
    --! \details Special value: 0 = unlimited. Readable from address 0x68.
    MAX_MTU_RX     : std_logic_vector(31 downto 0) := X"00000000";
    --! \brief Max size of TX blocks (in Bytes) including SZE2 header.
    --! \details Special value: 0 = unlimited. Readable from address 0x6C.
    MAX_MTU_TX     : std_logic_vector(31 downto 0) := X"00000000"
  );
  port (
    --! \name Basic signals

    --! Global clock.
    CLK            : in std_logic;
    --! Global reset.
    RESET          : in std_logic;

    --! \name Misc ports

    --! Contents of the COMMAND register (writable by SW)
    COMMAND        : out std_logic_vector(31 downto 0);
    --! Signals readable by SW
    STATUS         : in  std_logic_vector(127 downto 0);
    --! Write enables for four 32bit words of STATUS
    WE             : in  std_logic_vector(3 downto 0);
    --! \brief Control of ethernet repeater
    --! \details Bit 0: Use repeater 0 output (instead of OBUF 0).
    --! Bit 1: Enable repeater 0 (send repeat data instead of idles).
    --! Bits 2, 3: repeater 1, ...
    REPEATER       : out std_logic_vector(31 downto 0);
    --! Bank select for sysmon
    SYSMON_BANK    : out std_logic_vector(1 downto 0);

    --! \name Interrupt interface

    --! Interrupt input, each one-cycle pulse sets INTERRUPT register and is forwarded to INTERRUPT_OUT
    INTERRUPT_IN   : in  std_logic_vector(31 downto 0);
    --! Allows INTERRUPT_IN
    INTR_RDY_IN   : out std_logic;
    --! Output interface Interrupt request
    INTERRUPT_OUT  : out std_logic;
    --! Output interface Data
    INTR_DATA_OUT  : out std_logic_vector(4 downto 0);
    --! Output interface Ready for next request
    INTR_RDY_OUT   : in  std_logic;

    --! \name MI32 interface

    --! Data to write.
    MI_DWR        : in  std_logic_vector(31 downto 0);
    --! Read/write address.
    MI_ADDR       : in  std_logic_vector(31 downto 0);
    --! Read valid.
    MI_RD         : in  std_logic;
    --! Write valid.
    MI_WR         : in  std_logic;
    --! Write data byte enable (not supported).
    MI_BE         : in  std_logic_vector(3 downto 0);
    --! Read data.
    MI_DRD        : out std_logic_vector(31 downto 0);
    --! Read/write address ready.
    MI_ARDY       : out std_logic;
    --! Read data ready.
    MI_DRDY       : out std_logic
  );
end entity;

--! \brief Architecture implementing full design identification component with MI32 interface.
architecture full of ID_COMP is

  --! \name Choosed local bus data
  signal mx_string_data   : std_logic_vector(31 downto 0);
  signal mx_ctrl_data     : std_logic_vector(31 downto 0);
  signal mx_ctrl2_data    : std_logic_vector(31 downto 0);
  signal mx_ctrl3_data    : std_logic_vector(31 downto 0);
  signal mx_dout          : std_logic_vector(31 downto 0);
  signal reg_mx_dout      : std_logic_vector(31 downto 0);

  --! \name Auxiliary wires
  signal neg_data_in      : std_logic_vector(31 downto 0);

  --! \name Register
  signal reg_string_data  : std_logic_vector(31 downto 0);
  signal reg_ctrl_data    : std_logic_vector(31 downto 0);
  signal reg_ctrl2_data   : std_logic_vector(31 downto 0);
  signal reg_ctrl3_data   : std_logic_vector(31 downto 0);
  signal reg_cmd          : std_logic_vector(31 downto 0);
  signal reg_address      : std_logic_vector(31 downto 0) := (others => '0');
  signal reg_status       : std_logic_vector(127 downto 0);
  signal reg_repeater     : std_logic_vector(31 downto 0);
  signal reg_rep_we       : std_logic;
  signal reg_rep_cs       : std_logic;
  signal reg_neg    : std_logic_vector(31 downto 0);
  signal reg_neg_we : std_logic;
  signal neg_cs     : std_logic;
  signal reg_drdy   : std_logic;
  signal reg_drdy2  : std_logic;

  --! \name Sysmon
  signal sig_sysmon_bank : std_logic_vector( 1 downto 0);

  --! \name Interrupts
  signal reg_intr         : std_logic_vector(31 downto 0);
  signal reg_intr_rd      : std_logic;
  signal sig_intr_in      : std_logic_vector(31 downto 0);
  signal sig_intr_rdy_in  : std_logic;
  signal reg_intr_mask    : std_logic_vector(31 downto 0);
  signal sig_interrupt_out  : std_logic;
  signal sig_intr_data_out  : std_logic_vector(4 downto 0);

begin
   -- --------------- Output and auxiliary -------------------------
   neg_data_in <= not MI_DWR;

   --! Register with sysmon bank select
   reg_sysmon_bank : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if MI_WR = '1' and MI_ADDR(6 downto 2) = "10001" and MI_BE(0) = '1' then
            sig_sysmon_bank <= MI_DWR(1 downto 0);
         end if;
      end if;
   end process;
   SYSMON_BANK <= sig_sysmon_bank;

   --! Register with inverted MI32 data
   reg_negp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_neg( 7 downto  0) <= (others => '1');
            reg_neg(15 downto  8) <= (others => '1');
            reg_neg(23 downto 16) <= (others => '1');
            reg_neg(31 downto 24) <= (others => '1');
         else
            if (reg_neg_we = '1') then
               if MI_BE(0) = '1' then
                  reg_neg(7 downto 0) <= neg_data_in(7 downto 0);
               end if;
               if MI_BE(1) = '1' then
                  reg_neg(15 downto 8) <= neg_data_in(15 downto 8);
               end if;
               if MI_BE(2) = '1' then
                  reg_neg(23 downto 16) <= neg_data_in(23 downto 16);
               end if;
               if MI_BE(3) = '1' then
                  reg_neg(31 downto 24) <= neg_data_in(31 downto 24);
               end if;
            end if;
         end if;
      end if;
   end process;

   neg_cs <= '1' when (MI_ADDR(5 downto 2) = 0) else '0';
   reg_neg_we <= neg_cs and MI_WR;

   --! Command register
   reg_cmd_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if MI_WR = '1' and MI_ADDR(5 downto 2) = "0011"
         then
            if MI_BE(0) = '1' then
               reg_cmd(7 downto 0) <= MI_DWR(7 downto 0);
            end if;
            if MI_BE(1) = '1' then
               reg_cmd(15 downto 8) <= MI_DWR(15 downto 8);
            end if;
            if MI_BE(2) = '1' then
               reg_cmd(23 downto 16) <= MI_DWR(23 downto 16);
            end if;
            if MI_BE(3) = '1' then
               reg_cmd(31 downto 24) <= MI_DWR(31 downto 24);
            end if;
         end if;
      end if;
   end process;


   reg_rep_cs <= '1' when MI_ADDR(6 downto 0) = "1110000" else '0';
   reg_rep_we <= reg_rep_cs and MI_WR;
   --! Repeater register
   reg_repeater_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_repeater <= (others => '0');
         else
            if reg_rep_we = '1' then
               if MI_BE(0) = '1' then
                  reg_repeater(7 downto 0) <= MI_DWR(7 downto 0);
               end if;
               if MI_BE(1) = '1' then
                  reg_repeater(15 downto 8) <= MI_DWR(15 downto 8);
               end if;
               if MI_BE(2) = '1' then
                  reg_repeater(23 downto 16) <= MI_DWR(23 downto 16);
               end if;
               if MI_BE(3) = '1' then
                  reg_repeater(31 downto 24) <= MI_DWR(31 downto 24);
               end if;
            end if;
         end if;
      end if;
   end process;

   REPEATER <= reg_repeater;

   --! Interrupt mask register
   reg_intr_mask_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            -- Default: Pass interrupts from DMA and nothing else.
            reg_intr_mask <= X"FFFFFFFC";
         else
            if MI_ADDR(6 downto 0) = "1111000" and MI_WR = '1' then
               if MI_BE(0) = '1' then
                  reg_intr_mask(7 downto 0) <= reg_intr_mask(7 downto 0)
                     and MI_DWR(7 downto 0);
               end if;
               if MI_BE(1) = '1' then
                  reg_intr_mask(15 downto 8) <= reg_intr_mask(15 downto 8)
                     and MI_DWR(15 downto 8);
               end if;
               if MI_BE(2) = '1' then
                  reg_intr_mask(23 downto 16) <= reg_intr_mask(23 downto 16)
                     and MI_DWR(23 downto 16);
               end if;
               if MI_BE(3) = '1' then
                  reg_intr_mask(31 downto 24) <= reg_intr_mask(31 downto 24)
                     and MI_DWR(31 downto 24);
               end if;
            elsif MI_ADDR(6 downto 0) = "1111100" and MI_WR = '1' then
               if MI_BE(0) = '1' then
                  reg_intr_mask(7 downto 0) <= reg_intr_mask(7 downto 0)
                     or MI_DWR(7 downto 0);
               end if;
               if MI_BE(1) = '1' then
                  reg_intr_mask(15 downto 8) <= reg_intr_mask(15 downto 8)
                     or MI_DWR(15 downto 8);
               end if;
               if MI_BE(2) = '1' then
                  reg_intr_mask(23 downto 16) <= reg_intr_mask(23 downto 16)
                     or MI_DWR(23 downto 16);
               end if;
               if MI_BE(3) = '1' then
                  reg_intr_mask(31 downto 24) <= reg_intr_mask(31 downto 24)
                     or MI_DWR(31 downto 24);
               end if;
            end if;
         end if;
      end if;
   end process;


   --! Status registers
   reg_status_gen : for i in 0 to 3 generate
      reg_status_p : process(CLK)
      begin
         if CLK'event and CLk = '1' then
            if WE(i) = '1' then
               reg_status((32*i)+31 downto 32*i) <= STATUS((32*i)+31 downto 32*i);
            end if;
         end if;
      end process;
   end generate;

   --! Control data multiplex
   mx_ctrl_data_p : process(MI_ADDR, reg_neg, reg_cmd, reg_status)
   begin
         mx_ctrl_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" =>   mx_ctrl_data  <= reg_neg;
            when "001" =>   mx_ctrl_data  <= PROJECT_ID&SW_MAJOR&SW_MINOR;
            when "010" =>   mx_ctrl_data  <= HW_MAJOR&HW_MINOR;
            when "011" =>   mx_ctrl_data  <= reg_cmd;
            when "100" =>   mx_ctrl_data  <= reg_status(31 downto 0);
            when "101" =>   mx_ctrl_data  <= reg_status(63 downto 32);
            when "110" =>   mx_ctrl_data  <= reg_status(95 downto 64);
            when others =>  mx_ctrl_data  <= reg_status(127 downto 96);
         end case;
   end process mx_ctrl_data_p;

   --! Control data 2 multiplex
   mx_ctrl2_data_p : process(MI_ADDR, sig_sysmon_bank, reg_intr)
   begin
         mx_ctrl2_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" => mx_ctrl2_data <= ICS_FREQUENCY -- 0x040
                                             & TX_CHANNELS & RX_CHANNELS;
            when "001" => mx_ctrl2_data <= (31 downto 2 => '0')  -- 0x044
                                             & sig_sysmon_bank;
            when "010" => mx_ctrl2_data <= NETCOPE_MAJOR & NETCOPE_MINOR &
                                           ID_MAJOR & ID_MINOR;  -- 0x48
            when "011" => mx_ctrl2_data <= BUILD_TIME;           -- 0x4C
            when "100" => mx_ctrl2_data <= BUILD_UID;            -- 0x50
            when "101" => mx_ctrl2_data <= reg_intr;             -- 0x54
            when "110" => mx_ctrl2_data <= USER_GENERIC0;        -- 0x58
            when "111" => mx_ctrl2_data <= USER_GENERIC1;        -- 0x5C
            when others => mx_ctrl2_data <= (others => '0');
         end case;
   end process mx_ctrl2_data_p;

   --! Control data 3 multiplex
   mx_ctrl3_data_p : process(MI_ADDR, reg_repeater, reg_intr_mask)
   begin
         mx_ctrl3_data  <= (others => '0');
         case MI_ADDR(4 downto 2) is
            when "000" => mx_ctrl3_data <= USER_GENERIC2;        -- 0x60
            when "001" => mx_ctrl3_data <= USER_GENERIC3;        -- 0x64
            when "010" => mx_ctrl3_data <= MAX_MTU_RX;           -- 0x68
            when "011" => mx_ctrl3_data <= MAX_MTU_TX;           -- 0x6C
            when "100" => mx_ctrl3_data <= reg_repeater;         -- 0x70
            when "101" => mx_ctrl3_data <= reg_intr_mask;        -- 0x74
            -- SR-IOV: DMA channels count for VFs
            when "110" => mx_ctrl3_data <= X"00000101";          -- 0x78
            when others => mx_ctrl3_data <= (others => '0');
         end case;
   end process mx_ctrl3_data_p;

   --! Pipelined data registers
   reg_ctrl_data_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_ctrl_data <= mx_ctrl_data;
         reg_string_data <= mx_string_data;
         reg_ctrl2_data <= mx_ctrl2_data;
         reg_ctrl3_data <= mx_ctrl3_data;
      end if;
   end process reg_ctrl_data_p;

   --! MI32 address register
   reg_address_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (MI_WR = '1') or (MI_RD = '1') then
            reg_address(6 downto 5) <= MI_ADDR(6 downto 5);
         end if;
      end if;
   end process reg_address_p;

   --! MI32 data ready pipeline registers
   reg_drdy_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_drdy <= '0';
            reg_drdy2 <= '0';
         else
            reg_drdy  <= MI_RD;
            reg_drdy2 <= reg_drdy;
         end if;
      end if;
   end process;

   --! Output multiplex
   mx_dout_p : process(reg_address, reg_ctrl_data, reg_string_data, reg_ctrl2_data, reg_ctrl3_data)
   begin
      case reg_address(6 downto 5) is
         when "00"   => mx_dout <= reg_ctrl_data;  -- 0x00...0x1f
         when "01"   => mx_dout <= reg_string_data;-- 0x20...0x3f
         when "10"   => mx_dout <= reg_ctrl2_data; -- 0x40...0x5f
         when "11"   => mx_dout <= reg_ctrl3_data; -- 0x60...0x7f
         when others => mx_dout <= (others => '0');
      end case;
   end process;

   --! MI32 read data register
   reg_dout_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_mx_dout <= mx_dout;
      end if;
   end process reg_dout_p;

   MI_DRD <= reg_mx_dout;
   MI_ARDY <= MI_RD or MI_WR;
   MI_DRDY <= reg_drdy2;

   COMMAND <= reg_cmd;

   -- -----------------------------------------------------------------
   --! String address decoder
   -- -----------------------------------------------------------------
   mx_str_data_p : process(MI_ADDR) -- Synchronous write ro regx
   begin
      mx_string_data  <= (others => '0');
      case MI_ADDR(4 downto 2) is
         when "000" => mx_string_data  <= PROJECT_TEXT(239 downto 224)&PROJECT_TEXT(255 downto 240);
         when "001" => mx_string_data  <= PROJECT_TEXT(207 downto 192)&PROJECT_TEXT(223 downto 208);
         when "010" => mx_string_data  <= PROJECT_TEXT(175 downto 160)&PROJECT_TEXT(191 downto 176);
         when "011" => mx_string_data  <= PROJECT_TEXT(143 downto 128)&PROJECT_TEXT(159 downto 144);
         when "100" => mx_string_data  <= PROJECT_TEXT(111 downto  96)&PROJECT_TEXT(127 downto 112);
         when "101" => mx_string_data  <= PROJECT_TEXT( 79 downto  64)&PROJECT_TEXT( 95 downto  80);
         when "110" => mx_string_data  <= PROJECT_TEXT( 47 downto  32)&PROJECT_TEXT( 63 downto  48);
         when "111" => mx_string_data  <= PROJECT_TEXT( 15 downto   0)&PROJECT_TEXT( 31 downto  16);
         when others => mx_string_data  <= (others => '0');
      end case;
   end process mx_str_data_p;

   --! \brief Interrupt manager component
   intr_man_i : entity work.INTERRUPT_MANAGER
   generic map(
      PULSE    => X"FFFFFFFF" -- All inputs must be pulses
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      INTERRUPT_IN   => sig_intr_in,
      INTR_RDY_IN    => sig_intr_rdy_in,

      INTERRUPT_OUT  => sig_interrupt_out,
      INTR_DATA_OUT  => sig_intr_data_out,
      INTR_RDY_OUT   => INTR_RDY_OUT
   );

   INTERRUPT_OUT <= sig_interrupt_out;
   INTR_DATA_OUT <= sig_intr_data_out;

   INTR_RDY_IN <= sig_intr_rdy_in;

   sig_intr_in <= INTERRUPT_IN and not reg_intr_mask;

   reg_intr_gen : for i in 0 to 31 generate
      --! Interrupt registers
      reg_intr_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_intr(i) <= '0';
            else
               if sig_intr_rdy_in = '1' and INTERRUPT_IN(i) = '1' then
                  reg_intr(i) <= '1'; -- Setting to 1 has higher priority ...
               elsif reg_intr_rd = '1' then
                  reg_intr(i) <= '0'; -- ... than resetting to zero.
               end if;
            end if;
         end if;
      end process;
   end generate;

   --! Interrupt read register
   reg_intr_rd_p : process(MI_ADDR, MI_RD)
   begin
      if MI_RD = '1' and MI_ADDR(6 downto 2) = "10101" then -- 0x54
         reg_intr_rd <= '1';
      else
         reg_intr_rd <= '0';
      end if;
   end process;

end architecture;
