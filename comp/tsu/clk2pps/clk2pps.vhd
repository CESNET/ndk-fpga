-- clk2pps.vhd
--!
--! \file
--! \brief PPS signal generator from FPGA clock
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2012
--!
--! \section License
--!
--! Copyright (C) 2012 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
--! Library containing log2 and max functions.
use work.math_pack.all;

--! \brief Entity of PPS signal generator from FPGA clock
entity CLK2PPS is
  generic (
    --! \brief Maximal supported frequency of input clock in MHz.
    --! \details Width of transformation counter is computed as log2(MAX_FREQ*1000000). Maximal supported value is 4294 (4294967296 Hz clock).
    MAX_FREQ        : integer := 268; -- 2^28 = 268435456 Hz
    --! \brief Number of input clock's ticks while PPS pulse remains active.
    --! \details Must be lower than the lowest used frequency of input clock. Value 1 means standard one tick PPS pulse.
    ACTIVE_PPS      : integer := 256
  );
  port(
    --! \name Input clock interface

    --! Reference clock signal
    CLK      : in  std_logic;
    --! Reset signal synchronized with CLK
    RESET    : in  std_logic;
    --! \brief Frequency of reference clock in Hz minus 1 Hz
    --! \details 0 means 1 Hz CLK, 1 means 2 Hz CLK ...
    CLK_FREQ : in  std_logic_vector(31 downto 0);

    --! \name Output PPS pulse interface

    --! Output PPS pulse
    PPS_N    : out std_logic
  );
end entity;

--! \brief Implementation of PPS signal generator from FPGA clock
architecture full of CLK2PPS is
  constant CNT_WIDTH        : integer :=log2(MAX_FREQ*1000000);
  constant ACTIVE_CNT_WIDTH : integer :=max(log2(ACTIVE_PPS),1);

  signal sig_pps_n  : std_logic;

  signal cnt        : std_logic_vector(CNT_WIDTH-1 downto 0) := (others => '0');
  signal cnt_zero   : std_logic;

  signal active_cnt : std_logic_vector(ACTIVE_CNT_WIDTH-1 downto 0);
  signal active_end : std_logic;
begin
  --! Core transformation counter
  cnt_i : process(CLK)
  begin
    if (CLK'event and CLK='1') then
      if (cnt_zero='1') then
        cnt <= CLK_FREQ(CNT_WIDTH-1 downto 0);
      else
        cnt <= cnt-1;
      end if;
    end if;
  end process;

  --! Register to hold active PPS pulse
  pps_holder_reg_i : process(CLK)
  begin
    if (CLK'event and CLK = '1') then
      if (RESET = '1' or active_end = '1') then
        sig_pps_n <= '1';
      elsif (cnt_zero = '1') then
        sig_pps_n <= '0';
      end if;
    end if;
  end process;

  --! Counter for delayed end of active PPS pulse
  pps_holder_cnt_i : process(CLK)
  begin
    if (CLK'event and CLK = '1') then
      if (sig_pps_n = '1') then
        active_cnt <= (others => '0');
      else
        active_cnt <= active_cnt + '1';
      end if;
    end if;
  end process;

  PPS_N      <= sig_pps_n;
  cnt_zero   <= '1' when cnt=(cnt'length-1 downto 0 => '0') else '0';
  active_end <= '1' when active_cnt=conv_std_logic_vector(ACTIVE_PPS-1,active_cnt'length) else '0';
end architecture;

