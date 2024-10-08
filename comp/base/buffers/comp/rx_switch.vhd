--
-- rx_swith.vhd - switching data and logic from several input components with zero output latency to memory
-- Copyright (C) 2008 CESNET
-- Author(s): Vozenilek Jan  <xvozen00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------
entity RX_SWITCH is
  generic(
    DATA_WIDTH : integer := 64;
    FLOWS      : integer := 2;
    BLOCK_SIZE : integer := 512
  );

  port(
    CLK      : in  std_logic;
    RESET    : in  std_logic;

    -- Write interface (to input component)
    DATA_IN  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    DIN_VLD  : in  std_logic_vector(FLOWS-1 downto 0);
    RD_REQ   : out std_logic_vector(FLOWS-1 downto 0);

    -- Read interface (to storage memory)
    DATA_OUT : out std_logic_vector(DATA_WIDTH-1 downto 0);
    DOUT_VLD : out std_logic_vector(FLOWS-1 downto 0);
    WR_ADDR  : out std_logic_vector(log2(BLOCK_SIZE*FLOWS)*FLOWS-1 downto 0);
    CNT_WR   : out std_logic_vector((log2(BLOCK_SIZE)+1)*FLOWS-1 downto 0);
    REG_WR   : out std_logic_vector((log2(BLOCK_SIZE)+log2(FLOWS)+1)*FLOWS-1 downto 0);
    BLK_FULL : in  std_logic_vector(FLOWS-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of RX_SWITCH is

  constant FLOW_WIDTH   : integer := DATA_WIDTH / FLOWS;
  constant BLOCK_SIZE_W : integer := log2(BLOCK_SIZE);
  constant FLOWS_W      : integer := log2(FLOWS);

  subtype MEM_RANGE  is natural range FLOWS_W-1 downto 0;
  subtype ADDR_RANGE is natural range FLOWS_W+BLOCK_SIZE_W-1 downto FLOWS_W;

  type t_data       is array(FLOWS-1 downto 0) of std_logic_vector(FLOW_WIDTH-1 downto 0);
  type t_mem_cnt    is array(FLOWS-1 downto 0) of std_logic_vector(FLOWS_W-1 downto 0);
  type t_item_cnt   is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W-1 downto 0);
  type t_write_cnt  is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W+FLOWS_W downto 0);
  type t_write_addr is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);

  signal din                 : t_data;
  signal dout                : t_data;
  signal blk_write_allow     : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_mem_rst   : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_item_rst  : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_addr_mem  : t_mem_cnt;
  signal cnt_write_addr_item : t_item_cnt;
  signal cnt_write_addr_msb  : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_addr      : t_write_cnt;
  signal blk_write_addr      : t_write_cnt;
  signal mem_cnt             : t_mem_cnt;
  signal mem_write_addr      : t_write_addr;

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity FAILURE;

SWITCH : for j in 0 to FLOWS-1 generate

  -- transformations between arrays and vectors
  din(j) <= DATA_IN((j*FLOW_WIDTH)+FLOW_WIDTH-1 downto j*FLOW_WIDTH);
  DATA_OUT((j*FLOW_WIDTH)+FLOW_WIDTH-1 downto j*FLOW_WIDTH) <= dout(j);
  WR_ADDR((j*log2(BLOCK_SIZE*FLOWS))+log2(BLOCK_SIZE*FLOWS)-1 downto j*log2(BLOCK_SIZE*FLOWS)) <= mem_write_addr(j);
  CNT_WR((j*(BLOCK_SIZE_W+1))+BLOCK_SIZE_W downto j*(BLOCK_SIZE_W+1)) <= cnt_write_addr(j)(FLOWS_W+BLOCK_SIZE_W downto FLOWS_W);
  REG_WR((j*(BLOCK_SIZE_W+FLOWS_W+1))+BLOCK_SIZE_W+FLOWS_W downto j*(BLOCK_SIZE_W+FLOWS_W+1)) <= blk_write_addr(j);

  -- block write allow signal
  process(blk_write_addr, mem_cnt, DIN_VLD, BLK_FULL)
  begin
    if ((mem_cnt(conv_integer(blk_write_addr(j)(MEM_RANGE))) = conv_std_logic_vector(j, FLOWS_W)) and
        (DIN_VLD(j) = '1') and (BLK_FULL(j) = '0')) then
      blk_write_allow(j) <= '1';
    else
      blk_write_allow(j) <= '0';
    end if;
  end process;

  -- allow and switching logic
  dout(j)           <= din(conv_integer(mem_cnt(j)));
  DOUT_VLD(j)       <= blk_write_allow(conv_integer(mem_cnt(j)));
  mem_write_addr(j) <= mem_cnt(j) & blk_write_addr(conv_integer(mem_cnt(j)))(ADDR_RANGE);

  -- write address counter ----------------------------------------------------
  process(cnt_write_addr_mem)
  begin
    if (cnt_write_addr_mem(j) = conv_std_logic_vector(FLOWS-1, FLOWS_W)) then
      cnt_write_mem_rst(j) <= '1';
    else
      cnt_write_mem_rst(j) <= '0';
    end if;
  end process;

  process(cnt_write_addr_item)
  begin
    if (cnt_write_addr_item(j) = conv_std_logic_vector(BLOCK_SIZE-1, BLOCK_SIZE_W)) then
      cnt_write_item_rst(j) <= '1';
    else
      cnt_write_item_rst(j) <= '0';
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_write_addr_mem(j) <= conv_std_logic_vector(1, cnt_write_addr_mem(j)'length);
      else
        if (blk_write_allow(j) = '1') then
          if (cnt_write_mem_rst(j) = '1') then
            cnt_write_addr_mem(j) <= (others => '0');
          else
            cnt_write_addr_mem(j) <= cnt_write_addr_mem(j) + 1;
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_write_addr_item(j) <= (others => '0');
      else
        if (blk_write_allow(j) = '1') then
          if (cnt_write_mem_rst(j) = '1') then
            cnt_write_addr_item(j) <= cnt_write_addr_item(j) + 1;
            if (cnt_write_item_rst(j) = '1') then
              cnt_write_addr_item(j) <= (others => '0');
            end if;
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_write_addr_msb(j) <= '0';
      else
        if (blk_write_allow(j) = '1') then
          if ((cnt_write_mem_rst(j) = '1') and (cnt_write_item_rst(j) = '1')) then
            cnt_write_addr_msb(j) <= not cnt_write_addr_msb(j);
          end if;
        end if;
      end if;
    end if;
  end process;

  cnt_write_addr(j) <= cnt_write_addr_msb(j) & cnt_write_addr_item(j) & cnt_write_addr_mem(j);

  -- block write address register ---------------------------------------------
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        blk_write_addr(j) <= (others => '0');
      else
        if (blk_write_allow(j) = '1') then
          blk_write_addr(j) <= cnt_write_addr(j);
        end if;
      end if;
    end if;
  end process;

  -- mem_cnt counter
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        mem_cnt(j) <= conv_std_logic_vector(j, mem_cnt(j)'length);
      else
        if (DIN_VLD /= conv_std_logic_vector(0, FLOWS)) then
          mem_cnt(j) <= mem_cnt(j) - 1;
          if (mem_cnt(j) = conv_std_logic_vector(0, mem_cnt(j)'length)) then
            mem_cnt(j) <= conv_std_logic_vector(FLOWS-1, mem_cnt(j)'length);
          end if;
        end if;
      end if;
    end if;
  end process;

end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
RD_REQ <= blk_write_allow;

end architecture;
-- ----------------------------------------------------------------------------
