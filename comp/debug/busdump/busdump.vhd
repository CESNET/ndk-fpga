-- busdump.vhd: Syntetisable pasive dumping of generic data bus into MI32 accessible memory
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



entity busdump is
  generic (
    DATA_WIDTH    : integer:=512;
    STORAGE_ITEMS : integer:=512
  );
  port(
    -- Common signals
    CLK            : in  std_logic;
    RESET          : in  std_logic;
    -- Monitored data bus
    IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
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



architecture full of busdump is

  constant MEM_WIDTH : integer := DATA_WIDTH + 16;
  constant DATA_REGS : integer := ((DATA_WIDTH - 1) / 32) + 2;
  constant ALL_REGS : integer := DATA_REGS + 1;

  type std_logic32_vector is array(natural range <>) of std_logic_vector(32-1 downto 0);
  signal data_reg : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal data_cmp : std_logic;

  signal dump_data : std_logic_vector(MEM_WIDTH-1 downto 0);
  signal dump_vld : std_logic;
  signal dump_full : std_logic;

  signal same_cnt : std_logic_vector(16-1 downto 0) := (others => '0');
  signal same_cnt_max : std_logic;

  signal addr_reg : std_logic_vector(log2(ALL_REGS)-1 downto 0);
  signal start_dump, stop_dump, active_dump : std_logic := '0';
  signal regs : std_logic32_vector(ALL_REGS-1 downto 0) := (others => (others => '0'));
  signal read_data, read_data2 : std_logic_vector(DATA_REGS*32-1 downto 0) := (others => '0');
  signal read_vld : std_logic;
  signal read_req : std_logic;

begin

  -- Input data register
  in_data_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      data_reg <= IN_DATA;
    end if;
  end process;
  data_cmp <= '1' when data_reg = IN_DATA else '0';

  -- Memory to store input data
  dump_memory : entity work.fifo_bram
    generic map (
      ITEMS          => STORAGE_ITEMS,
      DATA_WIDTH     => MEM_WIDTH,
      AUTO_PIPELINE  => true
    ) port map (
      CLK      => CLK,
      RESET    => RESET,
      WR       => dump_vld,
      DI       => dump_data,
      FULL     => dump_full,
      RD       => read_req,
      DO       => read_data(MEM_WIDTH-1 downto 0),
      DV       => read_vld,
      EMPTY    => open
    );
  dump_vld <= not data_cmp and not dump_full and active_dump;
  dump_data <= same_cnt & data_reg;
  read_data2(DATA_WIDTH-1 downto 0) <= read_data(DATA_WIDTH-1 downto 0);
  read_data2(DATA_REGS*32-16-1 downto DATA_REGS*32-32) <= read_data(DATA_WIDTH+16-1 downto DATA_WIDTH);

  -- Counter of same data ticks
  same_counter : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if active_dump='0' or data_cmp='0' then
        same_cnt <= (others => '0');
      elsif same_cnt_max='0' then
        same_cnt <= same_cnt + 1;
      end if;
    end if;
  end process;
  same_cnt_max <= '1' when same_cnt = (16-1 downto 0 => '1') else '0';

  -- MI processing
  mi_ctrl_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      if RESET='1' then
        MI_DRDY <= '1';
      else
        MI_DRDY <= MI_RD;
      end if;
      addr_reg <= MI_ADDR(log2(ALL_REGS)+1 downto 2);
    end if;
  end process;
  MI_DRD <= regs(conv_integer(addr_reg));
  MI_ARDY <= '1';
  start_dump <= MI_WR and MI_DWR(0);
  stop_dump <= MI_WR and MI_DWR(1);
  read_req <= MI_WR and MI_DWR(2);

  -- MI registers
  mi_active_reg : process(CLK)
  begin
    if CLK'event and CLK='1' then
      active_dump <= (active_dump and not stop_dump) or start_dump;
    end if;
  end process;
  regs(0) <= "00000" & dump_full & active_dump & read_vld & X"00" & conv_std_logic_vector(DATA_WIDTH, 16);
  regs_connect_gen : for i in 0 to DATA_REGS-1 generate
    mi_data_reg : process(CLK)
    begin
      if CLK'event and CLK='1' then
        if read_req='1' then
          regs(i+1) <= read_data2((i+1)*32-1 downto i*32);
        end if;
      end if;
    end process;
  end generate;

end architecture;
