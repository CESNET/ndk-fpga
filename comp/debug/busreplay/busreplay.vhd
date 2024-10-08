-- busreplay.vhd: Syntetisable data bus active replay from MI32 accessible memory
-- Copyright (C) 2016 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use ieee.std_logic_1164.ALL;
use ieee.std_logic_unsigned.ALL;
use ieee.std_logic_arith.ALL;
use work.math_pack.all;



entity busreplay is
  generic (
    DATA_WIDTH    : integer:=512;
    STORAGE_ITEMS : integer:=512
  );
  port(
    -- Common signals
    CLK            : in  std_logic;
    RESET          : in  std_logic;
    -- Monitored FLU interface
    OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    OUT_VLD        : out std_logic;
    -- MI32 interface to read dumped data
    MI_DWR         : in  std_logic_vector(31 downto 0);
    MI_ADDR        : in  std_logic_vector(31 downto 0);
    MI_RD          : in  std_logic;
    MI_WR          : in  std_logic;
    MI_BE          : in  std_logic_vector(3 downto 0);
    MI_DRD         : out std_logic_vector(31 downto 0);
    MI_ARDY        : out std_logic;
    MI_DRDY        : out std_logic
  );
end entity;



architecture full of busreplay is

  constant MEM_WIDTH : integer := DATA_WIDTH + 16;
  constant DATA_REGS : integer := ((DATA_WIDTH - 1) / 32) + 2;
  constant ALL_REGS : integer := DATA_REGS + 1;

  type std_logic32_vector is array(natural range <>) of std_logic_vector(32-1 downto 0);

  signal replay_data : std_logic_vector(MEM_WIDTH-1 downto 0) := (others => '0');
  signal replay_vld : std_logic;
  signal replay_rd : std_logic;

  signal same_cnt, same_req : std_logic_vector(16-1 downto 0) := (others => '0');
  signal same_cnt_max : std_logic;

  signal mi_we : std_logic_vector(ALL_REGS-1 downto 0);
  signal start_replay, stop_replay, active_replay : std_logic := '0';
  signal regs : std_logic32_vector(ALL_REGS-1 downto 0) := (others => (others => '0'));
  signal write_req : std_logic;
  signal write_data, write_data2 : std_logic_vector(DATA_REGS*32-1 downto 0);
  signal write_full : std_logic;

begin

  -- Memory to store output data
  replay_memory : entity work.fifo_bram
    generic map (
      ITEMS          => STORAGE_ITEMS,
      DATA_WIDTH     => MEM_WIDTH,
      AUTO_PIPELINE  => true
    ) port map (
      CLK      => CLK,
      RESET    => RESET,
      WR       => write_req,
      DI       => write_data2(MEM_WIDTH-1 downto 0),
      FULL     => write_full,
      RD       => replay_rd,
      DO       => replay_data,
      DV       => replay_vld,
      EMPTY    => open
    );
  OUT_DATA <= replay_data(DATA_WIDTH-1 downto 0);
  OUT_VLD <= replay_vld and active_replay;
  same_req <= replay_data(16+DATA_WIDTH-1 downto DATA_WIDTH);
  replay_rd <= same_cnt_max and active_replay and replay_vld;

  -- Counter of same data ticks
  idle_counter : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if active_replay='0' or replay_vld='0' or replay_rd='1' then
        same_cnt <= (others => '0');
      elsif same_cnt_max='0' then
        same_cnt <= same_cnt + 1;
      end if;
    end if;
  end process;
  same_cnt_max <= '1' when same_cnt = same_req else '0';

  -- MI processing
  mi_ctrl_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        MI_DRDY <= '1';
      else
        MI_DRDY <= MI_RD;
      end if;
    end if;
  end process;
  MI_DRD <= regs(0);
  MI_ARDY <= '1';
  mi_wr_dec : entity work.dec1fn_enable
    generic map (ALL_REGS)
    port map (MI_ADDR(log2(ALL_REGS)+1 downto 2), MI_WR, mi_we);
  start_replay <= mi_we(0) and MI_DWR(0);
  stop_replay <= mi_we(0) and MI_DWR(1);
  write_req <= mi_we(0) and MI_DWR(2);

  -- MI registers
  mi_active_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      active_replay <= (active_replay and not stop_replay) or start_replay;
    end if;
  end process;
  regs(0) <= "00000" & write_full & active_replay & replay_vld & X"00" & conv_std_logic_vector(DATA_WIDTH, 16);
  regs_connect_gen : for i in 0 to DATA_REGS-1 generate
    mi_data_reg : process(CLK)
    begin
      if CLK'event and CLK='1' then
        if mi_we(i+1)='1' then
          regs(i+1) <= MI_DWR;
        end if;
      end if;
    end process;
    write_data((i+1)*32-1 downto i*32) <= regs(i+1);
  end generate;
  write_data2(DATA_WIDTH-1 downto 0) <= write_data(DATA_WIDTH-1 downto 0);
  write_data2(DATA_WIDTH+16-1 downto DATA_WIDTH) <= write_data(DATA_REGS*32-16-1 downto DATA_REGS*32-32);

end architecture;
