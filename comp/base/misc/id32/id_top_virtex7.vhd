-- id_top_virtex7.vhd
--!
--! @file
--! \brief Design identification with MI32 interface for Virtex-7
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2013
--!
--! @section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
--! Part of IEEE standard library.
use IEEE.numeric_std.all;

--! \brief Design identification component with MI32 interface for Virtex-7.
--! \details FPGA component SYSMON is connected inside and reachable throught MI32 interface.
entity ID_COMP_MI32_NOREC is
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
    --! \brief Enable SYSMON component connection
    --! \details Sysmon component is mapped into addresses 0x80-0xff.
    --! On address 0x44 there is sysmon bank select register as lowest 2 bits.
    --! Sysmon bank register is used as highest 2 bits of address into sysmon.
    --! When sysmon is disabled, all zeros are readed from its address space.
    SYSMON_EN      : boolean := true;
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
    --! \brief Number of cycles when input INTERRUPT_IN is ignored
    --! \details Not used in architecture.
    INTERRUPT_IGNORE : std_logic_vector(15 downto 0) := X"00FF";
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
    --! Sysmon raised alarm, as programmed by SW
    SYSMON_ALARM   : out std_logic;

    --! \name Interrupt interface

    --! Interrupt input, each one-cycle pulse sets INTERRUPT register and is forwarded to INTERRUPT_OUT
    INTERRUPT_IN   : in  std_logic_vector(31 downto 0);
    --! Allows INTERRUPT_IN
    INTR_RDY_IN    : out std_logic;
    --! Output interface Interrupt request (pulse)
    INTERRUPT_OUT  : out std_logic_vector(31 downto 0);
    --! Output interface Ready for next request
    INTR_SENT      : in  std_logic;

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

--! \brief Architecture implementing full design identification component with MI32 interface for Virtex-5.
architecture full of ID_COMP_MI32_NOREC is
  --! \name IDCOMP signals
  signal idcomp_drd  : std_logic_vector(31 downto 0);
  signal idcomp_drdy : std_logic;
  signal idcomp_ardy : std_logic;
  signal idcomp_wr   : std_logic;
  signal idcomp_rd   : std_logic;

  --! \name SYSMON signals
  signal sysmon_bank : std_logic_vector( 1 downto 0);
  signal sysmon_drd  : std_logic_vector(31 downto 0);
  signal sysmon_drdy : std_logic;
  signal sysmon_ardy : std_logic;
  signal sysmon_wr   : std_logic;
  signal sysmon_rd   : std_logic;

  signal sig_interrupt_out : std_logic_vector(31 downto 0);
  signal reg_intr_pending  : std_logic;

begin
  --! \brief Design identification component accessible throught MI32 interface
  --! \details Component mapped into addresses 0x00-0x7f of MI32 address space.
  id_comp_i : entity work.ID_COMP
    generic map(
      PROJECT_ID     => PROJECT_ID,
      SW_MAJOR       => SW_MAJOR,
      SW_MINOR       => SW_MINOR,
      HW_MAJOR       => HW_MAJOR,
      HW_MINOR       => HW_MINOR,
      PROJECT_TEXT   => PROJECT_TEXT,
      RX_CHANNELS    => RX_CHANNELS,
      TX_CHANNELS    => TX_CHANNELS,
      ID_MAJOR       => ID_MAJOR,
      ID_MINOR       => ID_MINOR,
      NETCOPE_MAJOR  => NETCOPE_MAJOR,
      NETCOPE_MINOR  => NETCOPE_MINOR,
      BUILD_TIME     => BUILD_TIME,
      BUILD_UID      => BUILD_UID,
      ICS_FREQUENCY  => ICS_FREQUENCY,
      USER_GENERIC0  => USER_GENERIC0,
      USER_GENERIC1  => USER_GENERIC1,
      USER_GENERIC2  => USER_GENERIC2,
      USER_GENERIC3  => USER_GENERIC3,
      MAX_MTU_RX     => MAX_MTU_RX,
      MAX_MTU_TX     => MAX_MTU_TX
    ) port map (
      CLK            => CLK,
      RESET          => RESET,

      COMMAND        => COMMAND,
      STATUS         => STATUS,
      WE             => WE,
      REPEATER       => REPEATER,
      SYSMON_BANK    => sysmon_bank,

      INTERRUPT_IN   => sig_interrupt_out, --Just for setting the internal regs.
      INTR_RDY_IN    => open,             -- Real interrupt path is below.
      INTERRUPT_OUT  => open,
      INTR_DATA_OUT  => open,
      INTR_RDY_OUT   => '1',

      MI_DWR         => MI_DWR,
      MI_ADDR        => MI_ADDR,
      MI_RD          => idcomp_rd,
      MI_WR          => idcomp_wr,
      MI_BE          => MI_BE,
      MI_DRD         => idcomp_drd,
      MI_ARDY        => idcomp_ardy,
      MI_DRDY        => idcomp_drdy
    );

  INTR_RDY_IN <= not reg_intr_pending;
  INTERRUPT_OUT <= INTERRUPT_IN when reg_intr_pending = '0' else sig_interrupt_out;

  --! Store waiting for the INTR_SENT signal
  reg_intr_pending_p : process(CLK)
  begin
    if CLK'event and CLK = '1' then
      if RESET = '1' then
         reg_intr_pending <= '0';
      else
         if INTERRUPT_IN /= X"00000000" and reg_intr_pending = '0' then
            reg_intr_pending <= '1';
            sig_interrupt_out <= INTERRUPT_IN;
         elsif INTR_SENT = '1' then
            reg_intr_pending <= '0';
         end if;
      end if;
    end if;
  end process;

  --! \brief Sysmon component accessible throught MI32 interface
  --! \details Component mapped into addresses 0x80-0xff of MI32 address space.
  sysmon_i : entity work.SYSMON_MI32
    generic map(
      SYSMON_EN      => SYSMON_EN
    ) port map (
      CLK            => CLK,
      RESET          => RESET,

      BANK           => sysmon_bank,
      ALARM          => SYSMON_ALARM,

      MI_DWR         => MI_DWR,
      MI_ADDR        => MI_ADDR,
      MI_RD          => sysmon_rd,
      MI_WR          => sysmon_wr,
      MI_BE          => MI_BE,
      MI_DRD         => sysmon_drd,
      MI_ARDY        => sysmon_ardy,
      MI_DRDY        => sysmon_drdy
    );

  sysmon_rd  <= MI_ADDR(7) and MI_RD;
  sysmon_wr  <= MI_ADDR(7) and MI_WR;
  idcomp_rd  <= not MI_ADDR(7) and MI_RD;
  idcomp_wr  <= not MI_ADDR(7) and MI_WR;
  MI_ARDY    <= sysmon_ardy or idcomp_ardy;
  MI_DRDY    <= sysmon_drdy or idcomp_drdy;
  MI_DRD     <= idcomp_drd when idcomp_drdy='1' else sysmon_drd;
end architecture;
