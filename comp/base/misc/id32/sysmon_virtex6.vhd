-- sysmon_virtex6.vhd
--!
--! @file
--! \brief System monitor component for Virtex-6 FPGAs
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

--! Library containing SYSMON component.
library unisim;
--! Library containing SYSMON component.
use unisim.vcomponents.ALL;

--! \brief Architecture implementing system monitor component for Virtex-6 FPGAs.
architecture virtex6 of SYSMON_MI32 is
  --! \name Sysmon signals
  signal sysmon_den      : std_logic;
  signal sysmon_drdy     : std_logic;
  signal reg_sysmon_wen  : std_logic;
  signal sysmon_alm      : std_logic_vector(2 downto 0);
  signal sysmon_addr     : std_logic_vector(6 downto 0);
begin
  -- real sysmon generate
  sysmon_gen : if (SYSMON_EN) generate
    -- MI connection
    MI_ARDY              <= MI_RD or MI_WR;
    MI_DRDY              <= sysmon_drdy and (not reg_sysmon_wen);
    MI_DRD(31 downto 16) <= (others => '0');
    reg_sysmon_wen_p : process(CLK)
    begin
      if CLK'event and CLK = '1' then
        if sysmon_den = '1' then
          reg_sysmon_wen <= MI_WR;
        end if;
      end if;
    end process;


    -- sysmon signals
    sysmon_den     <= MI_RD or MI_WR;
    sysmon_addr    <= BANK & MI_ADDR(6 downto 2);
    --! Alarm register
    alarm_reg : process(CLK)
    begin
      if CLK'event and CLK = '1' then
        ALARM <= sysmon_alm(0) or sysmon_alm(1) or sysmon_alm(2);
      end if;
    end process;


    -- sysmon component
    SYSMON_INST : SYSMON
    generic map(
      INIT_40 => X"0000",
      INIT_41 => X"20FF",
      INIT_42 => X"1800",
      INIT_48 => X"0100",
      INIT_49 => X"0000",
      INIT_4A => X"0000",
      INIT_4B => X"0000",
      INIT_4C => X"0000",
      INIT_4D => X"0000",
      INIT_4E => X"0000",
      INIT_4F => X"0000",
      INIT_50 => X"b5ed",
      INIT_51 => X"5999",
      INIT_52 => X"e000",
      INIT_54 => X"a93a",
      INIT_55 => X"5111",
      INIT_56 => X"caaa",
      INIT_57 => X"ae4e"
    ) port map (
      RESET             => RESET,

      DADDR(6 downto 0) => sysmon_addr,
      DCLK              => CLK,
      DEN               => sysmon_den,
      DI(15 downto 0)   => MI_DWR(15 downto 0),
      DWE               => MI_WR,
      DO(15 downto 0)   => MI_DRD(15 downto 0),
      DRDY              => sysmon_drdy,

      ALM(2 downto 0)   => sysmon_alm,
      OT                => open,

      VAUXN(15 downto 0)  => "0000000000000000",
      VAUXP(15 downto 0)  => "0000000000000000",
      CHANNEL(4 downto 0) => open,
      VN                  => '0',
      VP                  => '0',
      CONVST              => '0',
      CONVSTCLK           => '0',
      BUSY                => open,
      EOC                 => open,
      EOS                 => open,
      JTAGBUSY            => open,
      JTAGLOCKED          => open,
      JTAGMODIFIED        => open
    );
  end generate;


  -- fake sysmon generate
  no_sysmon_gen : if (not SYSMON_EN) generate
    MI_DRD  <= (others => '0');
    --! Register of MI_RD signal as MI_DRDY signal
    mi_drdy_reg : process(CLK)
    begin
      if CLK'event and CLK = '1' then
        MI_DRDY <= MI_RD;
      end if;
    end process;
    MI_ARDY <= MI_RD or MI_WR;
    ALARM   <= '0';
  end generate;

end architecture;
