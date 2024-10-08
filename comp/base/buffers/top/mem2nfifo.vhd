--
-- mem2nfifo.vhd - top entity, data from memory send to several FIFOs
-- Copyright (C) 2008 CESNET
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
entity MEM2NFIFO is
  generic(
    DATA_WIDTH : integer := 64;
    FLOWS      : integer := 2;
    BLOCK_SIZE : integer := 512;
    LUT_MEMORY : boolean := false;
    GLOB_STATE : boolean := false
  );

  port(
    CLK        : in  std_logic;
    RESET      : in  std_logic;

    -- Write interface
    DATA_IN    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    BLOCK_ADDR : in  std_logic_vector(abs(log2(FLOWS)-1) downto 0);
    WR_ADDR    : in  std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);
    NEW_LEN    : in  std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);
    NEW_LEN_DV : in  std_logic_vector(FLOWS-1 downto 0);
    WRITE      : in  std_logic;
    FULL       : out std_logic_vector(FLOWS-1 downto 0);

    -- Read interface
    DATA_OUT   : out std_logic_vector(DATA_WIDTH-1 downto 0);
    DATA_VLD   : out std_logic_vector(FLOWS-1 downto 0);
    READ       : in  std_logic_vector(FLOWS-1 downto 0);
    EMPTY      : out std_logic_vector(FLOWS-1 downto 0);

    STATUS     : out std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of MEM2NFIFO is

  -- memory latency
  function MEM_LATENCY
    return integer is
  begin
    if (LUT_MEMORY = true) then return 1;
    else return 2;
    end if;
  end function;

  -- data width of one flow
  constant FLOW_WIDTH    : integer := DATA_WIDTH / FLOWS;
  -- maximal number of items in output component
  constant OUTCOMP_ITEMS : integer := FLOWS + MEM_LATENCY + 1;
  constant BLOCK_SIZE_W  : integer := log2(BLOCK_SIZE);

  function FLOWS_W
    return integer is
  begin
    if (FLOWS = 1) then return 1;
    else return log2(FLOWS);
    end if;
  end function;

  -- used when BLOCK_SIZE is not a power of 2
  function ADDR_FIX_CONST (FLOW_ID: integer)
    return integer is
  begin
    return FLOW_ID*(2**log2(BLOCK_SIZE)-BLOCK_SIZE);
  end function;

  function glob_addr_mem_reset
    return std_logic_vector is
  begin
    if (FLOWS = 1) then return conv_std_logic_vector(0, FLOWS_W);
    else return conv_std_logic_vector(1, FLOWS_W);
    end if;
  end function;

  function glob_addr_item_reset
    return std_logic_vector is
  begin
    if (FLOWS = 1) then return conv_std_logic_vector(1, BLOCK_SIZE_W);
    else return conv_std_logic_vector(0, BLOCK_SIZE_W);
    end if;
  end function;

  type t_data         is array(FLOWS-1 downto 0) of std_logic_vector(FLOW_WIDTH-1 downto 0);
  type t_addr         is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);
  type t_mem_cnt      is array(FLOWS-1 downto 0) of std_logic_vector(FLOWS_W-1 downto 0);
  type t_addr_low_cnt is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W-1 downto 0);
  type t_addr_cnt     is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W downto 0);
  type t_glob         is array(FLOWS-1 downto 0) of std_logic_vector(BLOCK_SIZE_W+FLOWS_W downto 0);
  type t_out_stat     is array(FLOWS-1 downto 0) of std_logic_vector(log2(OUTCOMP_ITEMS+1)-1 downto 0);
  type t_status       is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE+1)-1 downto 0);
  type t_fix          is array(FLOWS-1 downto 0) of integer;

  subtype ADDR_RANGE      is natural range BLOCK_SIZE_W-1 downto 0;
  subtype GLOB_MEM_RANGE  is natural range FLOWS_W-1 downto 0;
  subtype GLOB_ADDR_RANGE is natural range FLOWS_W+BLOCK_SIZE_W-1 downto FLOWS_W;

  signal addr_fix           : t_fix;

  signal switch_in          : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal switch_out         : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal switch_valid       : std_logic_vector(FLOWS-1 downto 0);
  signal switch_rd_addr     : std_logic_vector((log2(BLOCK_SIZE*FLOWS))*FLOWS-1 downto 0);

  signal mem_read_allow     : std_logic_vector(FLOWS-1 downto 0);
  signal mem_out            : t_data;
  signal mem_valid          : std_logic_vector(FLOWS-1 downto 0);

  signal write_allow        : std_logic;
  signal read_allow         : std_logic_vector(FLOWS-1 downto 0);
  signal blk_read_allow     : std_logic_vector(FLOWS-1 downto 0);
  signal last_mem_rd_en     : std_logic_vector(FLOWS-1 downto 0);
  signal glob_lm_rd_en      : std_logic_vector(FLOWS-1 downto 0);
  signal write_addr         : std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);
  signal read_addr          : t_addr;
  signal cnt_rd_addr_rst    : std_logic;
  signal cnt_rd_addr_low    : std_logic_vector(BLOCK_SIZE_W-1 downto 0);
  signal cnt_rd_addr_high   : std_logic;
  signal cnt_rd_addr        : std_logic_vector((BLOCK_SIZE_W+1)*FLOWS-1 downto 0);
  signal blk_rd_addr        : std_logic_vector((BLOCK_SIZE_W+FLOWS_W+1)*FLOWS-1 downto 0);
  signal cnt_read_addr      : t_addr_cnt;
  signal blk_read_addr      : t_glob;
  signal reg_write_addr     : t_addr_cnt;
  signal glob_read_mem_rst  : std_logic_vector(FLOWS-1 downto 0);
  signal glob_read_item_rst : std_logic_vector(FLOWS-1 downto 0);
  signal glob_read_cnt_mem  : t_mem_cnt;
  signal glob_read_cnt_item : t_addr_low_cnt;
  signal glob_read_cnt_msb  : std_logic_vector(FLOWS-1 downto 0);
  signal glob_read_cnt      : t_glob;
  signal glob_read_addr     : t_glob;

  signal blk_empty          : std_logic_vector(FLOWS-1 downto 0);
  signal blk_full           : std_logic_vector(FLOWS-1 downto 0);
  signal blk_status         : t_status;
  signal glob_full          : std_logic_vector(FLOWS-1 downto 0);
  signal glob_status        : t_status;
  signal sig_full           : std_logic_vector(FLOWS-1 downto 0);
  signal status_sig         : t_status;

  signal outcomp_din        : t_data;
  signal outcomp_valid      : std_logic_vector(FLOWS-1 downto 0);
  signal outcomp_empty      : std_logic_vector(FLOWS-1 downto 0);
  signal outcomp_full       : std_logic_vector(FLOWS-1 downto 0);
  signal outcomp_stat       : t_out_stat;
  signal outcomp_status     : std_logic_vector(log2(OUTCOMP_ITEMS+1)*FLOWS-1 downto 0);

  signal newlen             : t_status;
  signal newlen_dv          : std_logic_vector(FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity ERROR;

ONE_FLOW : if (FLOWS = 1) generate

  process(outcomp_status, blk_empty)
  begin
    if ((outcomp_status < OUTCOMP_ITEMS) and (blk_empty(0) = '0')) then
      mem_read_allow(0) <= '1';
    else
      mem_read_allow(0) <= '0';
    end if;
  end process;

  write_allow    <= WRITE and (not sig_full(0));
  write_addr     <= WR_ADDR;
  switch_out     <= switch_in;
  switch_valid   <= mem_valid;
  switch_rd_addr <= blk_rd_addr(GLOB_ADDR_RANGE);
  read_addr(0)   <= switch_rd_addr - addr_fix(0);
  blk_read_allow <= mem_read_allow;

  -- read address counter -----------------------------------------------------
  process(cnt_rd_addr_low)
  begin
    if (cnt_rd_addr_low = conv_std_logic_vector(BLOCK_SIZE-1, BLOCK_SIZE_W)) then
      cnt_rd_addr_rst <= '1';
    else
      cnt_rd_addr_rst <= '0';
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_rd_addr_low <= conv_std_logic_vector(1, cnt_rd_addr_low'length);
      else
        if (blk_read_allow(0) = '1') then
          if (cnt_rd_addr_rst = '1') then
            cnt_rd_addr_low <= (others => '0');
          else
            cnt_rd_addr_low <= cnt_rd_addr_low + 1;
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_rd_addr_high <= '0';
      else
        if (blk_read_allow(0) = '1') then
          if (cnt_rd_addr_rst = '1') then
            cnt_rd_addr_high <= not cnt_rd_addr_high;
          end if;
        end if;
      end if;
    end if;
  end process;

  cnt_rd_addr <= cnt_rd_addr_high & cnt_rd_addr_low;

  -- read address register ----------------------------------------------------
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        blk_rd_addr <= (others => '0');
      else
        if (mem_read_allow(0) = '1') then
          blk_rd_addr(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W) <= cnt_rd_addr;
        end if;
      end if;
    end if;
  end process;

end generate;

MORE_FLOWS : if (FLOWS > 1) generate

  write_allow <= WRITE and (not sig_full(conv_integer(BLOCK_ADDR)));
  write_addr  <= (BLOCK_ADDR & WR_ADDR) - addr_fix(conv_integer(BLOCK_ADDR));

  switch : entity work.TX_SWITCH
    generic map (
      DATA_WIDTH    => DATA_WIDTH,
      FLOWS         => FLOWS,
      BLOCK_SIZE    => BLOCK_SIZE,
      MEM_LATENCY   => MEM_LATENCY,
      OUTCOMP_ITEMS => OUTCOMP_ITEMS
    )
    port map (
      CLK         => CLK,
      RESET       => RESET,

      -- Write interface (to storage memory)
      DATA_IN     => switch_in,
      DIN_VLD     => mem_valid,
      RD_ADDR     => switch_rd_addr,
      CNT_RD      => cnt_rd_addr,
      REG_RD      => blk_rd_addr,
      MEM_RD_REQ  => mem_read_allow,
      BLK_RD_REQ  => blk_read_allow,
      BLK_EMPTY   => blk_empty,

      -- Read interface (to output component)
      DATA_OUT    => switch_out,
      DOUT_VLD    => switch_valid,
      COMP_STATUS => outcomp_status
    );

  MORE_FLOWS_FIELD : for j in 0 to FLOWS-1 generate
    read_addr(j)     <= switch_rd_addr((j*log2(BLOCK_SIZE*FLOWS))+log2(BLOCK_SIZE*FLOWS)-1 downto j*log2(BLOCK_SIZE*FLOWS))
                        - addr_fix(conv_integer(switch_rd_addr((j*log2(BLOCK_SIZE*FLOWS))+log2(BLOCK_SIZE*FLOWS)-1 downto j*log2(BLOCK_SIZE*FLOWS)+BLOCK_SIZE_W)));
  end generate;

end generate;

FIELD : for j in 0 to FLOWS-1 generate

  memory : entity work.BUF_MEM
    generic map (
      LUT_MEMORY => LUT_MEMORY,
      DATA_WIDTH => FLOW_WIDTH,
      ITEMS      => BLOCK_SIZE*FLOWS,
      OUTPUT_REG => true
    )
    port map (
      CLK      => CLK,
      RESET    => RESET,

      -- Write interface
      WR_ADDR  => write_addr,
      DATA_IN  => DATA_IN(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j),
      WRITE    => write_allow,

      -- Read interface
      RD_ADDR  => read_addr(j),
      DATA_OUT => mem_out(j),
      DATA_VLD => mem_valid(j),
      READ     => mem_read_allow(j),
      PIPE_EN  => '1'
    );

  outcomp : entity work.SH_FIFO
    generic map (
      FIFO_WIDTH => FLOW_WIDTH,
      FIFO_DEPTH => OUTCOMP_ITEMS,
      USE_INREG  => false,
      USE_OUTREG => false
    )
    port map (
      CLK    => CLK,
      RESET  => RESET,

      WE     => switch_valid(j),
      DIN    => outcomp_din(j),

      RE     => read_allow(j),
      DOUT   => DATA_OUT(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j),

      FULL   => outcomp_full(j),
      EMPTY  => outcomp_empty(j)
    );

  -- fifo status (sh_fifo does not have its own)
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        outcomp_stat(j) <= (others => '0');
      else
        if ((blk_read_allow(j) = '1') and (read_allow(j) = '0')) then
          outcomp_stat(j) <= outcomp_stat(j) + 1;
        end if;
        if ((blk_read_allow(j) = '0') and (read_allow(j) = '1')) then
          outcomp_stat(j) <= outcomp_stat(j) - 1;
        end if;
      end if;
    end if;
  end process;

  outcomp_status(j*(log2(OUTCOMP_ITEMS+1))+log2(OUTCOMP_ITEMS+1)-1 downto j*log2(OUTCOMP_ITEMS+1)) <= outcomp_stat(j);

  -- outcomp valid signal (sh_fifo does not have a valid signal)
  outcomp_valid(j) <= not outcomp_empty(j);

  -- transformations between arrays and vectors
  addr_fix(j)      <= ADDR_FIX_CONST(j);
  cnt_read_addr(j) <= cnt_rd_addr((j*(BLOCK_SIZE_W+1))+BLOCK_SIZE_W downto j*(BLOCK_SIZE_W+1));
  blk_read_addr(j) <= blk_rd_addr((j*(BLOCK_SIZE_W+FLOWS_W+1))+BLOCK_SIZE_W+FLOWS_W downto j*(BLOCK_SIZE_W+FLOWS_W+1));
  newlen(j) <= NEW_LEN(j*log2(BLOCK_SIZE+1)+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1));
  STATUS((j*log2(BLOCK_SIZE+1))+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1)) <= blk_status(j);
  switch_in(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j) <= mem_out(j);
  outcomp_din(j) <= switch_out(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j);


  is2pow: if (2**log2(BLOCK_SIZE) = BLOCK_SIZE) generate

    -- write address register
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          reg_write_addr(j) <= (others => '0');
        else
          if (NEW_LEN_DV(j) = '1') then
            reg_write_addr(j) <= reg_write_addr(j) + newlen(j);
          end if;
        end if;
      end if;
    end process;

  end generate;


  not2pow: if (2**log2(BLOCK_SIZE) /= BLOCK_SIZE) generate

    -- write address register
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          reg_write_addr(j) <= (others => '0');
        else
          if (NEW_LEN_DV(j) = '1') then
            if ((BLOCK_SIZE - reg_write_addr(j)(ADDR_RANGE)) <= newlen(j)) then
              reg_write_addr(j)(ADDR_RANGE) <= newlen(j) - (BLOCK_SIZE - reg_write_addr(j)(ADDR_RANGE));
              reg_write_addr(j)(BLOCK_SIZE_W) <= not reg_write_addr(j)(BLOCK_SIZE_W);
            else
              reg_write_addr(j) <= reg_write_addr(j) + newlen(j);
            end if;
          end if;
        end if;
      end if;
    end process;

  end generate;


  -- reading from last memory allowed
  process(blk_read_allow, blk_read_addr)
  begin
    if ((blk_read_allow(j) = '1') and
        (blk_read_addr(j)(GLOB_MEM_RANGE) = conv_std_logic_vector(FLOWS-1, FLOWS_W))) then
      last_mem_rd_en(j) <= '1';
    else
      last_mem_rd_en(j) <= '0';
    end if;
  end process;

  -- global reading from last memory allowed
  process(read_allow, glob_read_addr)
  begin
    if ((read_allow(j) = '1') and
        (glob_read_addr(j)(GLOB_MEM_RANGE) = conv_std_logic_vector(FLOWS-1, FLOWS_W))) then
      glob_lm_rd_en(j) <= '1';
    else
      glob_lm_rd_en(j) <= '0';
    end if;
  end process;

  blk_status_sigs : entity work.BUF_STATUS
    generic map (
      ITEMS       => BLOCK_SIZE,
      MULTI_WRITE => true,
      MULTI_READ  => false
    )
    port map (
      CLK      => CLK,
      RESET    => RESET,

      WRITE_EN => newlen_dv(j),
      READ_EN  => last_mem_rd_en(j),
      WR_CNT   => reg_write_addr(j),
      WR_REG   => reg_write_addr(j),
      RD_CNT   => cnt_read_addr(j),
      RD_REG   => blk_read_addr(j)(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W),

      EMPTY    => blk_empty(j),
      FULL     => blk_full(j),
      STATUS   => blk_status(j)
    );


  notGlobState : if (GLOB_STATE = false) generate

    glob_read_cnt(j)  <= (others => '0');
    glob_read_addr(j) <= (others => '0');

    sig_full(j) <= blk_full(j);

    status_sig(j) <= blk_status(j);

  end generate;


  globState : if (GLOB_STATE = true) generate

    glob_status_sigs : entity work.BUF_STATUS
      generic map (
        ITEMS => BLOCK_SIZE
      )
      port map (
        CLK      => CLK,
        RESET    => RESET,

        WRITE_EN => newlen_dv(j),
        READ_EN  => glob_lm_rd_en(j),
        WR_CNT   => reg_write_addr(j),
        WR_REG   => reg_write_addr(j),
        RD_CNT   => glob_read_cnt(j)(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W),
        RD_REG   => glob_read_addr(j)(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W),

        EMPTY    => open,
        FULL     => glob_full(j),
        STATUS   => glob_status(j)
      );

    -- global address counter -------------------------------------------------
    process(glob_read_cnt_mem)
    begin
      if (glob_read_cnt_mem(j) = conv_std_logic_vector(FLOWS-1, FLOWS_W)) then
        glob_read_mem_rst(j) <= '1';
      else
        glob_read_mem_rst(j) <= '0';
      end if;
    end process;

    process(glob_read_cnt_item)
    begin
      if (glob_read_cnt_item(j) = conv_std_logic_vector(BLOCK_SIZE-1, BLOCK_SIZE_W)) then
        glob_read_item_rst(j) <= '1';
      else
        glob_read_item_rst(j) <= '0';
      end if;
    end process;

    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          glob_read_cnt_mem(j) <= glob_addr_mem_reset;
        else
          if (read_allow(j) = '1') then
            if (glob_read_mem_rst(j) = '1') then
              glob_read_cnt_mem(j) <= (others => '0');
            else
              glob_read_cnt_mem(j) <= glob_read_cnt_mem(j) + 1;
            end if;
          end if;
        end if;
      end if;
    end process;

    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          glob_read_cnt_item(j) <= glob_addr_item_reset;
        else
          if (read_allow(j) = '1') then
            if (glob_read_mem_rst(j) = '1') then
              glob_read_cnt_item(j) <= glob_read_cnt_item(j) + 1;
              if (glob_read_item_rst(j) = '1') then
                glob_read_cnt_item(j) <= (others => '0');
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
          glob_read_cnt_msb(j) <= '0';
        else
          if (read_allow(j) = '1') then
            if ((glob_read_mem_rst(j) = '1') and (glob_read_item_rst(j) = '1')) then
              glob_read_cnt_msb(j) <= not glob_read_cnt_msb(j);
            end if;
          end if;
        end if;
      end if;
    end process;

    glob_read_cnt(j) <= glob_read_cnt_msb(j) & glob_read_cnt_item(j) & glob_read_cnt_mem(j);

    -- global address register ------------------------------------------------
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          glob_read_addr(j) <= (others => '0');
        else
          if (read_allow(j) = '1') then
            glob_read_addr(j) <= glob_read_cnt(j);
          end if;
        end if;
      end if;
    end process;

    sig_full(j) <= glob_full(j);

    status_sig(j) <= glob_status(j);

  end generate;

end generate;


-- newlen valid register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    newlen_dv <= NEW_LEN_DV;
  end if;
end process;

-- allow logic
read_allow  <= READ and (not outcomp_empty);

-- ----------------------------------------------------------------------------
-- interface mapping
DATA_VLD <= outcomp_valid;
EMPTY    <= outcomp_empty;
FULL     <= sig_full;

end architecture;
-- ----------------------------------------------------------------------------
