-- id_top_virtex6.vhd
--!
--! @file
--! \brief Design identification with MI32 interface for Virtex-6
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

--! \brief Design identification component with MI32 interface for Virtex-6.
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
    --! \brief SYSMON clock.
    --! \details For Virtex-6 the clock frequency must be in range from 2 MHz to 80 MHz. Note that initial 250 MHz maximum has been changed (see http://www.xilinx.com/support/answers/36642.htm).
    SYSMON_CLK     : in std_logic;
    --! SYSMON reset.
    SYSMON_RESET   : in std_logic;

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

--! \brief Architecture implementing full design identification component with MI32 interface for Virtex-5.
architecture full of ID_COMP_MI32_NOREC is

  --! \name MI32 interface to ID component.
  signal mi_idcomp_dwr       : std_logic_vector(31 downto 0);
  signal mi_idcomp_addr      : std_logic_vector(31 downto 0);
  signal mi_idcomp_rd        : std_logic;
  signal mi_idcomp_wr        : std_logic;
  signal mi_idcomp_ardy      : std_logic;
  signal mi_idcomp_be        : std_logic_vector(3 downto 0);
  signal mi_idcomp_drd       : std_logic_vector(31 downto 0);
  signal mi_idcomp_drdy      : std_logic;

  --! \name MI32 interface to SYSMON component.
  signal mi_sysmon_dwr       : std_logic_vector(31 downto 0);
  signal mi_sysmon_addr      : std_logic_vector(31 downto 0);
  signal mi_sysmon_rd        : std_logic;
  signal mi_sysmon_wr        : std_logic;
  signal mi_sysmon_ardy      : std_logic;
  signal mi_sysmon_be        : std_logic_vector(3 downto 0);
  signal mi_sysmon_drd       : std_logic_vector(31 downto 0);
  signal mi_sysmon_drdy      : std_logic;

  --! \name MI32 interface to SYSMON synchronized to SYSMON clock.
  signal mi_sysmon_sync_dwr       : std_logic_vector(31 downto 0);
  signal mi_sysmon_sync_addr      : std_logic_vector(31 downto 0);
  signal mi_sysmon_sync_rd        : std_logic;
  signal mi_sysmon_sync_wr        : std_logic;
  signal mi_sysmon_sync_ardy      : std_logic;
  signal mi_sysmon_sync_be        : std_logic_vector(3 downto 0);
  signal mi_sysmon_sync_drd       : std_logic_vector(31 downto 0);
  signal mi_sysmon_sync_drdy      : std_logic;

  --! \name Misc signals.
  signal sysmon_bank         : std_logic_vector(1 downto 0);
  signal sysmon_bank_reg     : std_logic_vector(1 downto 0);
  signal sysmon_alarm_sig    : std_logic;

begin
  --! \brief MI32 address space splitter.
  --! \details Divides address space between SYSMON and ID component.
  MI_SPLITTER_I: entity work.MI_SPLITTER
    generic map(
      ITEMS       => 2,
      ADDR_WIDTH  => 7,
      DATA_WIDTH  => 32,
      PIPE        => false,
      PIPE_OUTREG => false
    ) port map(
      CLK           => CLK,
      RESET         => RESET,

      IN_DWR    => MI_DWR,
      IN_ADDR   => MI_ADDR(7 downto 0),
      IN_RD     => MI_RD,
      IN_WR     => MI_WR,
      IN_ARDY   => MI_ARDY,
      IN_BE     => MI_BE,
      IN_DRD    => MI_DRD,
      IN_DRDY   => MI_DRDY,

      OUT_DWR(31 downto  0)  => mi_idcomp_dwr,
      OUT_DWR(63 downto 32)  => mi_sysmon_dwr,
      OUT_ADDR( 6 downto 0)  => mi_idcomp_addr(6 downto 0),
      OUT_ADDR(13 downto 7)  => mi_sysmon_addr(6 downto 0),
      OUT_RD(0)   => mi_idcomp_rd,
      OUT_RD(1)   => mi_sysmon_rd,
      OUT_WR(0)   => mi_idcomp_wr,
      OUT_WR(1)   => mi_sysmon_wr,
      OUT_ARDY(0) => mi_idcomp_ardy,
      OUT_ARDY(1) => mi_sysmon_ardy,
      OUT_BE( 3 downto  0)  => mi_idcomp_be,
      OUT_BE( 7 downto  4)  => mi_sysmon_be,
      OUT_DRD(31 downto  0) => mi_idcomp_drd,
      OUT_DRD(63 downto 32) => mi_sysmon_drd,
      OUT_DRDY(0) => mi_idcomp_drdy,
      OUT_DRDY(1) => mi_sysmon_drdy
    );
  mi_idcomp_addr(31 downto 7) <= (others => '0');
  mi_sysmon_addr(31 downto 7) <= (others => '0');


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

      INTERRUPT_IN   => INTERRUPT_IN,
      INTR_RDY_IN    => INTR_RDY_IN,
      INTERRUPT_OUT  => INTERRUPT_OUT,
      INTR_DATA_OUT  => INTR_DATA_OUT,
      INTR_RDY_OUT   => INTR_RDY_OUT,

      MI_DWR         => mi_idcomp_dwr,
      MI_ADDR        => mi_idcomp_addr,
      MI_RD          => mi_idcomp_rd,
      MI_WR          => mi_idcomp_wr,
      MI_BE          => mi_idcomp_be,
      MI_DRD         => mi_idcomp_drd,
      MI_ARDY        => mi_idcomp_ardy,
      MI_DRDY        => mi_idcomp_drdy
    );

  -- No SYSMON -----------------------------------------------------------------
  NO_SYSMON_GEN : if (not SYSMON_EN) generate
    mi_sysmon_drd  <= (others => '0');
    --! Register of mi_sysmon_rd signal as mi_sysmon_drdy signal
    mi_drdy_reg : process(CLK)
    begin
      if CLK'event and CLK = '1' then
        mi_sysmon_drdy <= mi_sysmon_rd;
      end if;
    end process;
    mi_sysmon_ardy <= mi_sysmon_rd or mi_sysmon_wr;
    SYSMON_ALARM   <= '0';
  end generate;

  -- Real SYSMON ---------------------------------------------------------------
  REAL_SYSMON_GEN : if SYSMON_EN generate
    --! \brief Async register for SYSMON_BANK signal
    --! \details For signal sysmon_bank from CLK region to SYSMON_CLK region.
    sysmon_bank_reg_p : process(SYSMON_CLK)
    begin
      if SYSMON_CLK'event and SYSMON_CLK = '1' then
        sysmon_bank_reg <= sysmon_bank;
      end if;
    end process;

    --! \brief Async register for SYSMON_ALARM signal
    --! \details For signal sysmon_alarm from SYSMON_CLK region to CLK region.
    sysmon_alarm_reg_p : process(CLK)
    begin
      if CLK'event and CLK = '1' then
        SYSMON_ALARM <= sysmon_alarm_sig;
      end if;
    end process;

    --! Async MI32 for SYSMON
    SYSMON_ASYNC_MI : entity work.MI_ASYNC
      port map (
        CLK_M            => CLK,
        RESET_M          => RESET,
        MI_M_DWR         => mi_sysmon_dwr,
        MI_M_ADDR        => mi_sysmon_addr,
        MI_M_RD          => mi_sysmon_rd,
        MI_M_WR          => mi_sysmon_wr,
        MI_M_BE          => mi_sysmon_be,
        MI_M_DRD         => mi_sysmon_drd,
        MI_M_ARDY        => mi_sysmon_ardy,
        MI_M_DRDY        => mi_sysmon_drdy,

        CLK_S            => SYSMON_CLK,
        RESET_S          => SYSMON_RESET,
        MI_S_DWR         => mi_sysmon_sync_dwr,
        MI_S_ADDR        => mi_sysmon_sync_addr,
        MI_S_RD          => mi_sysmon_sync_rd,
        MI_S_WR          => mi_sysmon_sync_wr,
        MI_S_BE          => mi_sysmon_sync_be,
        MI_S_DRD         => mi_sysmon_sync_drd,
        MI_S_ARDY        => mi_sysmon_sync_ardy,
        MI_S_DRDY        => mi_sysmon_sync_drdy
      );


    --! \brief Sysmon component accessible throught MI32 interface
    --! \details Component mapped into addresses 0x80-0xff of MI32 address space.
    sysmon_i : entity work.SYSMON_MI32
      generic map(
        SYSMON_EN      => true
      ) port map (
        CLK            => SYSMON_CLK,
        RESET          => SYSMON_RESET,

        BANK           => sysmon_bank_reg,
        ALARM          => sysmon_alarm_sig,

        MI_DWR         => mi_sysmon_sync_dwr,
        MI_ADDR        => mi_sysmon_sync_addr,
        MI_RD          => mi_sysmon_sync_rd,
        MI_WR          => mi_sysmon_sync_wr,
        MI_BE          => mi_sysmon_sync_be,
        MI_DRD         => mi_sysmon_sync_drd,
        MI_ARDY        => mi_sysmon_sync_ardy,
        MI_DRDY        => mi_sysmon_sync_drdy
      );
  end generate;

end architecture;
