-- slr_crossing_dst.vhd: Special pipe component to cross between super logic regions (slow wire) - destination part.
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity SLR_CROSSING_DST is
  generic(
    DATA_WIDTH      : integer := 64;
    USE_OUTREG      : boolean := true;
    DEVICE          : string := "7SERIES"
  );
  port(
    CLK              : in std_logic;
    RESET            : in std_logic;
    CROSSING_DATA    : in std_logic_vector(DATA_WIDTH downto 0);
    CROSSING_DST_RDY : out std_logic;
    OUT_DATA         : out std_logic_vector(DATA_WIDTH-1 downto 0);
    OUT_SRC_RDY      : out std_logic;
    OUT_DST_RDY      : in  std_logic
  );
end entity;



library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

architecture full of SLR_CROSSING_DST is
  signal shreg_add  : std_logic;
  signal shreg_rem  : std_logic;
  signal shreg_out  : std_logic_vector(DATA_WIDTH downto 0);
  signal shreg_addr : std_logic_vector(1 downto 0);
  signal data       : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal src_rdy    : std_logic;
  signal out_ce     : std_logic;
  signal cross_ce   : std_logic;
  signal cross_ce_inreg : std_logic;
  signal dst_rdy    : std_logic;
  attribute keep : string;
  attribute keep of cross_ce_inreg  : signal is "true";
begin
  dst_rdy_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET = '1' then
        dst_rdy  <= '1';
        cross_ce_inreg <= '1';
        cross_ce <= '1';
      else
        dst_rdy  <= out_ce;
        cross_ce_inreg <= dst_rdy;
        cross_ce <= cross_ce_inreg;
      end if;
    end if;
  end process;

  CROSSING_DST_RDY <= dst_rdy;
  OUT_DATA         <= data;
  OUT_SRC_RDY      <= src_rdy;
  out_ce           <= OUT_DST_RDY or not src_rdy;
  shreg_add        <= not out_ce   and cross_ce;
  shreg_rem        <= not cross_ce and out_ce;

  SHREG_BUS : entity work.SH_REG_BASE_DYNAMIC
    generic map(
      DATA_WIDTH => DATA_WIDTH+1,
      NUM_BITS   => 4,
      INIT_TYPE  => 0,
      OPT        => "SRL",
      DEVICE     => DEVICE
    )
    port map(
      CLK  => CLK,
      CE   => cross_ce,
      ADDR(1 downto 0) => shreg_addr,

      DIN  => CROSSING_DATA,
      DOUT => shreg_out
    );

  outreg_gen : if USE_OUTREG generate
    data_reg : process(CLK)
    begin
      if CLK'event and CLK='1' then
        if out_ce = '1' then
          data <= shreg_out(DATA_WIDTH downto 1);
        end if;
      end if;
    end process;

    src_rdy_reg : process(CLK)
    begin
      if CLK'event and CLK='1' then
        if RESET = '1' then
          src_rdy <= '0';
        elsif out_ce = '1' then
          src_rdy <= shreg_out(0);
        end if;
      end if;
    end process;
  end generate;

  no_outreg_gen : if not USE_OUTREG generate
    data    <= shreg_out(DATA_WIDTH downto 1);
    src_rdy <= shreg_out(0);
  end generate;

  fsm_sync : process(CLK)
  begin
    if CLK'event and CLK = '1' then
      if RESET = '1' then
        shreg_addr <= "00";
      else
        if shreg_add = '1' then
          shreg_addr <= shreg_addr + 1;
        elsif shreg_rem = '1' then
          shreg_addr <= shreg_addr - 1;
        end if;
      end if;
    end if;
  end process;

  -- pragma synthesis_off
  assert not CLK'event or CLK /= '1' or shreg_addr /= "11" or shreg_add = '0' report "SLR Crossing overflow!"  severity failure;
  assert not CLK'event or CLK /= '1' or shreg_addr /= "00" or shreg_rem = '0' or RESET /= '0' report "SLR Crossing underflow!" severity failure;
  -- pragma synthesis_on
end architecture;
