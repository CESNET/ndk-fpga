--
-- tx_swith.vhd - switching data and logic from memory to several output components (typically FIFOs)
-- Copyright (C) 2007 CESNET
-- Author(s): Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
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
entity TX_SWITCH is
  generic(
    DATA_WIDTH    : integer := 64;
    FLOWS         : integer := 2;
    BLOCK_SIZE    : integer := 512;
    MEM_LATENCY   : integer := 1;
    OUTCOMP_ITEMS : integer := 4
  );

  port(
    CLK         : in  std_logic;
    RESET       : in  std_logic;

    -- Write interface (to storage memory)
    DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    DIN_VLD     : in  std_logic_vector(FLOWS-1 downto 0);
    RD_ADDR     : out std_logic_vector(log2(BLOCK_SIZE*FLOWS)*FLOWS-1 downto 0);
    CNT_RD      : out std_logic_vector((log2(BLOCK_SIZE)+1)*FLOWS-1 downto 0);
    REG_RD      : out std_logic_vector((log2(BLOCK_SIZE)+log2(FLOWS)+1)*FLOWS-1 downto 0);
    MEM_RD_REQ  : out std_logic_vector(FLOWS-1 downto 0);
    BLK_RD_REQ  : out std_logic_vector(FLOWS-1 downto 0);
    BLK_EMPTY   : in  std_logic_vector(FLOWS-1 downto 0);

    -- Read interface (to output component)
    DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);
    DOUT_VLD    : out std_logic_vector(FLOWS-1 downto 0);
    COMP_STATUS : in  std_logic_vector(log2(OUTCOMP_ITEMS+1)*FLOWS-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of TX_SWITCH is

  constant FLOW_WIDTH   : integer := DATA_WIDTH / FLOWS;
  constant BLOCK_SIZE_W : integer := log2(BLOCK_SIZE);
  constant FLOWS_W      : integer := log2(FLOWS);

  subtype MEM_RANGE  is natural range FLOWS_W-1 downto 0;
  subtype ADDR_RANGE is natural range FLOWS_W+BLOCK_SIZE_W-1 downto FLOWS_W;

  type t_data      is array(FLOWS-1 downto 0) of std_logic_vector(FLOW_WIDTH-1 downto 0);
  type t_mem_cnt   is array(FLOWS-1 downto 0) of std_logic_vector(FLOWS_W-1 downto 0);
  type t_item_cnt  is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W-1 downto 0);
  type t_read_cnt  is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W+FLOWS_W downto 0);
  type t_read_addr is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);
  type t_status    is array(FLOWS-1 downto 0) of std_logic_vector(log2(OUTCOMP_ITEMS+1)-1 downto 0);

  signal din                : t_data;
  signal dout               : t_data;
  signal blk_read_allow     : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_read_mem_rst   : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_read_item_rst  : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_read_addr_mem  : t_mem_cnt;
  signal cnt_read_addr_item : t_item_cnt;
  signal cnt_read_addr_msb  : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_read_addr      : t_read_cnt;
  signal blk_read_addr      : t_read_cnt;
  signal mem_cnt_rd_ce      : std_logic;
  signal mem_cnt_dv_ce      : std_logic;
  signal mem_cnt_dv         : t_mem_cnt;
  signal mem_cnt_rd         : t_mem_cnt;
  signal mem_read_addr      : t_read_addr;
  signal outcomp_stat       : t_status;

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity FAILURE;

SWITCH : for j in 0 to FLOWS-1 generate

  -- transformations between arrays and vectors
  din(j) <= DATA_IN((j*FLOW_WIDTH)+FLOW_WIDTH-1 downto j*FLOW_WIDTH);
  DATA_OUT((j*FLOW_WIDTH)+FLOW_WIDTH-1 downto j*FLOW_WIDTH) <= dout(j);
  RD_ADDR((j*log2(BLOCK_SIZE*FLOWS))+log2(BLOCK_SIZE*FLOWS)-1 downto j*log2(BLOCK_SIZE*FLOWS)) <= mem_read_addr(j);
  CNT_RD((j*(BLOCK_SIZE_W+1))+BLOCK_SIZE_W downto j*(BLOCK_SIZE_W+1)) <= cnt_read_addr(j)(FLOWS_W+BLOCK_SIZE_W downto FLOWS_W);
  REG_RD((j*(BLOCK_SIZE_W+FLOWS_W+1))+BLOCK_SIZE_W+FLOWS_W downto j*(BLOCK_SIZE_W+FLOWS_W+1)) <= blk_read_addr(j);
  outcomp_stat(j) <= COMP_STATUS((j*log2(OUTCOMP_ITEMS+1))+log2(OUTCOMP_ITEMS+1)-1 downto j*log2(OUTCOMP_ITEMS+1));

  -- block read allow signal
  process(mem_cnt_rd, blk_read_addr, outcomp_stat, BLK_EMPTY)
  begin
    if ((mem_cnt_rd(conv_integer(blk_read_addr(j)(MEM_RANGE))) = conv_std_logic_vector(j, FLOWS_W))
        and (outcomp_stat(j) < OUTCOMP_ITEMS) and (BLK_EMPTY(j) = '0')) then
      blk_read_allow(j) <= '1';
    else
      blk_read_allow(j) <= '0';
    end if;
  end process;

  MEM_RD_REQ(j)    <= blk_read_allow(conv_integer(mem_cnt_rd(j)));
  mem_read_addr(j) <= mem_cnt_rd(j) & blk_read_addr(conv_integer(mem_cnt_rd(j)))(ADDR_RANGE);

  dout(j)     <= din(conv_integer(mem_cnt_dv(j)));
  DOUT_VLD(j) <= DIN_VLD(conv_integer(mem_cnt_dv(j)));

  -- mem_cnt_rd counter
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        mem_cnt_rd(j) <= conv_std_logic_vector(j, mem_cnt_rd(j)'length);
      else
        if (mem_cnt_rd_ce = '1') then
          mem_cnt_rd(j) <= mem_cnt_rd(j) - 1;
          if (mem_cnt_rd(j) = conv_std_logic_vector(0, mem_cnt_rd(j)'length)) then
            mem_cnt_rd(j) <= conv_std_logic_vector(FLOWS-1, mem_cnt_rd(j)'length);
          end if;
        end if;
      end if;
    end if;
  end process;

  -- mem_cnt_dv counter
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        mem_cnt_dv(j) <= conv_std_logic_vector(j, mem_cnt_dv(j)'length);
      else
        if (mem_cnt_dv_ce = '1') then
          mem_cnt_dv(j) <= mem_cnt_dv(j) + 1;
          if (mem_cnt_dv(j) = conv_std_logic_vector(FLOWS-1, mem_cnt_dv(j)'length)) then
            mem_cnt_dv(j) <= (others => '0');
          end if;
        end if;
      end if;
    end if;
  end process;

  -- read address counter -----------------------------------------------------
  process(cnt_read_addr_mem)
  begin
    if (cnt_read_addr_mem(j) = conv_std_logic_vector(FLOWS-1, FLOWS_W)) then
      cnt_read_mem_rst(j) <= '1';
    else
      cnt_read_mem_rst(j) <= '0';
    end if;
  end process;

  process(cnt_read_addr_item)
  begin
    if (cnt_read_addr_item(j) = conv_std_logic_vector(BLOCK_SIZE-1, BLOCK_SIZE_W)) then
      cnt_read_item_rst(j) <= '1';
    else
      cnt_read_item_rst(j) <= '0';
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_read_addr_mem(j) <= conv_std_logic_vector(1, cnt_read_addr_mem(j)'length);
      else
        if (blk_read_allow(j) = '1') then
          if (cnt_read_mem_rst(j) = '1') then
            cnt_read_addr_mem(j) <= (others => '0');
          else
            cnt_read_addr_mem(j) <= cnt_read_addr_mem(j) + 1;
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_read_addr_item(j) <= (others => '0');
      else
        if (blk_read_allow(j) = '1') then
          if (cnt_read_mem_rst(j) = '1') then
            cnt_read_addr_item(j) <= cnt_read_addr_item(j) + 1;
            if (cnt_read_item_rst(j) = '1') then
              cnt_read_addr_item(j) <= (others => '0');
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
        cnt_read_addr_msb(j) <= '0';
      else
        if (blk_read_allow(j) = '1') then
          if ((cnt_read_mem_rst(j) = '1') and (cnt_read_item_rst(j) = '1')) then
            cnt_read_addr_msb(j) <= not cnt_read_addr_msb(j);
          end if;
        end if;
      end if;
    end if;
  end process;

  cnt_read_addr(j) <= cnt_read_addr_msb(j) & cnt_read_addr_item(j) & cnt_read_addr_mem(j);

  -- block read address register ----------------------------------------------
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        blk_read_addr(j) <= (others => '0');
      else
        if (blk_read_allow(j) = '1') then
          blk_read_addr(j) <= cnt_read_addr(j);
        end if;
      end if;
    end if;
  end process;

end generate;


process(BLK_EMPTY)
begin
  if ((not BLK_EMPTY) /= conv_std_logic_vector(0, FLOWS)) then
    mem_cnt_rd_ce <= '1';
  else
    mem_cnt_rd_ce <= '0';
  end if;
end process;

noLatency : if (MEM_LATENCY = 0) generate

  mem_cnt_dv_ce <= mem_cnt_rd_ce;

end generate;

latency : if (MEM_LATENCY > 0) generate

  latency: entity work.SH_REG_BASE_STATIC
    generic map(
      DATA_WIDTH => 1,
      NUM_BITS   => MEM_LATENCY,
      INIT_TYPE  => 0 --all zeros
    )
    port map(
      CLK     => CLK,
      DIN(0)  => mem_cnt_rd_ce,
      CE      => '1',
      DOUT(0) => mem_cnt_dv_ce
    );

end generate;

-- ----------------------------------------------------------------------------
-- interface mapping
BLK_RD_REQ <= blk_read_allow;

end architecture;
-- ----------------------------------------------------------------------------
