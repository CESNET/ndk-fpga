-- sysmon_virtex5.vhd
--!
--! @file
--! \brief System monitor component for Virtex-5 FPGAs
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

--! \brief Architecture implementing system monitor component for Virtex-5 FPGAs.
architecture ultrascaleplus of SYSMON_MI32 is
  --! \name Sysmon signals
  signal sysmon_den      : std_logic;
  signal sysmon_drdy     : std_logic;
  signal reg_sysmon_wen  : std_logic;
  signal sysmon_alm      : std_logic_vector(15 downto 0);
  signal sysmon_addr     : std_logic_vector(7 downto 0);
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
    sysmon_addr    <= "0" & BANK & MI_ADDR(6 downto 2);
    ALARM          <= sysmon_alm(0) or sysmon_alm(1) or sysmon_alm(2);


    -- sysmon component
    SYSMON_INST : SYSMONE4
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
      INIT_57 => X"ae4e",
      SIM_MONITOR_FILE => "/dev/null"
    ) port map (
      RESET             => RESET,
      CONVST            => '0',
      CONVSTCLK         => '0',

      DCLK              => CLK,
      DEN               => sysmon_den,
      DADDR(7 downto 0) => sysmon_addr,
      DI(15 downto 0)   => MI_DWR(15 downto 0),
      DO(15 downto 0)   => MI_DRD(15 downto 0),
      DWE               => MI_WR,
      DRDY              => sysmon_drdy,

      ADC_DATA          => open,
      ALM(15 downto 0)  => sysmon_alm,
      OT                => open,

      VP                => '0',
      VN                => '0',
      VAUXP(15 downto 0)=> "0000000000000000",
      VAUXN(15 downto 0)=> "0000000000000000",

      MUXADDR           => open,
      CHANNEL           => open,
      BUSY              => open,
      EOC               => open,
      EOS               => open,
      JTAGBUSY          => open,
      JTAGLOCKED        => open,
      JTAGMODIFIED      => open,

      I2C_SCLK          => '0',
      I2C_SDA           => '0',
      I2C_SCLK_TS       => open,
      I2C_SDA_TS        => open,
      SMBALERT_TS       => open
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
