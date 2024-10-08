--
-- nfifo2mem.vhd - top entity, data from several FIFOs to memory - read as from memory
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
entity NFIFO2MEM is
  generic(
    DATA_WIDTH : integer := 64;
    FLOWS      : integer := 2;
    BLOCK_SIZE : integer := 512;
    LUT_MEMORY : boolean := false;
    OUTPUT_REG : boolean := false;
    GLOB_STATE : boolean := true
  );

  port(
    CLK        : in  std_logic;
    RESET      : in  std_logic;

    -- Write interface
    DATA_IN    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    WRITE      : in  std_logic_vector(FLOWS-1 downto 0);
    FULL       : out std_logic_vector(FLOWS-1 downto 0);

    -- Read interface
    DATA_OUT   : out std_logic_vector(DATA_WIDTH-1 downto 0);
    DATA_VLD   : out std_logic;
    BLOCK_ADDR : in  std_logic_vector(abs(log2(FLOWS)-1) downto 0);
    RD_ADDR    : in  std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);
    READ       : in  std_logic;
    REL_LEN    : in  std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);
    REL_LEN_DV : in  std_logic_vector(FLOWS-1 downto 0);
    EMPTY      : out std_logic_vector(FLOWS-1 downto 0);
    PIPE_EN    : in  std_logic;

    STATUS     : out std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of NFIFO2MEM is

  constant FLOW_WIDTH   : integer := DATA_WIDTH / FLOWS;
  constant INCOMP_ITEMS : integer := FLOWS+1;
  constant BLOCK_SIZE_W : integer := log2(BLOCK_SIZE);

  function FLOWS_W
    return integer is
  begin
    if (FLOWS = 1) then return 1;
    else return log2(FLOWS);
    end if;
  end function;

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
  type t_status       is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE+1)-1 downto 0);
  type t_fix          is array(FLOWS-1 downto 0) of integer;

  subtype ADDR_RANGE      is natural range BLOCK_SIZE_W-1 downto 0;
  subtype GLOB_MEM_RANGE  is natural range FLOWS_W-1 downto 0;
  subtype GLOB_ADDR_RANGE is natural range FLOWS_W+BLOCK_SIZE_W-1 downto FLOWS_W;

  signal addr_fix            : t_fix;

  signal incomp_dout         : t_data;
  signal incomp_valid        : std_logic_vector(FLOWS-1 downto 0);
  signal incomp_empty        : std_logic_vector(FLOWS-1 downto 0);
  signal incomp_full         : std_logic_vector(FLOWS-1 downto 0);

  signal switch_in           : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal switch_out          : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal switch_valid        : std_logic_vector(FLOWS-1 downto 0);
  signal switch_wr_addr      : std_logic_vector((log2(BLOCK_SIZE*FLOWS))*FLOWS-1 downto 0);

  signal mem_in              : t_data;
  signal mem_valid           : std_logic_vector(FLOWS-1 downto 0);

  signal write_allow         : std_logic_vector(FLOWS-1 downto 0);
  signal read_allow          : std_logic;
  signal blk_write_allow     : std_logic_vector(FLOWS-1 downto 0);
  signal last_mem_wr_en      : std_logic_vector(FLOWS-1 downto 0);
  signal glob_lm_wr_en       : std_logic_vector(FLOWS-1 downto 0);
  signal write_addr          : t_addr;
  signal read_addr           : std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);
  signal cnt_wr_addr_rst     : std_logic;
  signal cnt_wr_addr_low     : std_logic_vector(BLOCK_SIZE_W-1 downto 0);
  signal cnt_wr_addr_high    : std_logic;
  signal cnt_wr_addr         : std_logic_vector((BLOCK_SIZE_W+1)*FLOWS-1 downto 0);
  signal blk_wr_addr         : std_logic_vector((BLOCK_SIZE_W+FLOWS_W+1)*FLOWS-1 downto 0);
  signal cnt_write_addr      : t_addr_cnt;
  signal blk_write_addr      : t_glob;
  signal reg_read_addr       : t_addr_cnt;
  signal glob_write_mem_rst  : std_logic_vector(FLOWS-1 downto 0);
  signal glob_write_item_rst : std_logic_vector(FLOWS-1 downto 0);
  signal glob_write_cnt_mem  : t_mem_cnt;
  signal glob_write_cnt_item : t_addr_low_cnt;
  signal glob_write_cnt_msb  : std_logic_vector(FLOWS-1 downto 0);
  signal glob_write_cnt      : t_glob;
  signal glob_write_addr     : t_glob;

  signal blk_empty           : std_logic_vector(FLOWS-1 downto 0);
  signal blk_full            : std_logic_vector(FLOWS-1 downto 0);
  signal blk_status          : t_status;
  signal glob_full           : std_logic_vector(FLOWS-1 downto 0);
  signal glob_status         : t_status;
  signal sig_full            : std_logic_vector(FLOWS-1 downto 0);
  signal status_sig          : t_status;

  signal rellen              : t_status;
  signal rellen_dv           : std_logic_vector(FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
begin

assert (DATA_WIDTH mod FLOWS = 0)
report "DATA_WIDTH / FLOWS is not an integer."
severity ERROR;

ONE_FLOW : if (FLOWS = 1) generate

--   read_allow     <= READ and (not blk_empty(0));
  read_addr      <= RD_ADDR;
  blk_write_allow(0) <= incomp_valid(0) and (not blk_full(0));
  switch_out     <= switch_in;
  switch_valid   <= blk_write_allow;
  switch_wr_addr <= blk_wr_addr(GLOB_ADDR_RANGE);
  write_addr(0)  <= switch_wr_addr - addr_fix(0);

  -- write address counter ----------------------------------------------------
  process(cnt_wr_addr_low)
  begin
    if (cnt_wr_addr_low = conv_std_logic_vector(BLOCK_SIZE-1, BLOCK_SIZE_W)) then
      cnt_wr_addr_rst <= '1';
    else
      cnt_wr_addr_rst <= '0';
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_wr_addr_low <= conv_std_logic_vector(1, cnt_wr_addr_low'length);
      else
        if (blk_write_allow(0) = '1') then
          if (cnt_wr_addr_rst = '1') then
            cnt_wr_addr_low <= (others => '0');
          else
            cnt_wr_addr_low <= cnt_wr_addr_low + 1;
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        cnt_wr_addr_high <= '0';
      else
        if (blk_write_allow(0) = '1') then
          if (cnt_wr_addr_rst = '1') then
            cnt_wr_addr_high <= not cnt_wr_addr_high;
          end if;
        end if;
      end if;
    end if;
  end process;

  cnt_wr_addr <= cnt_wr_addr_high & cnt_wr_addr_low;

  -- write address register ---------------------------------------------------
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (RESET = '1') then
        blk_wr_addr <= (others => '0');
      else
        if (blk_write_allow(0) = '1') then
          blk_wr_addr(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W) <= cnt_wr_addr;
        end if;
      end if;
    end if;
  end process;

end generate;

MORE_FLOWS : if (FLOWS > 1) generate

  read_allow <= READ and (not blk_empty(conv_integer(BLOCK_ADDR)));
  read_addr  <= (BLOCK_ADDR & RD_ADDR) - addr_fix(conv_integer(BLOCK_ADDR));

  switch : entity work.RX_SWITCH
    generic map (
      DATA_WIDTH => DATA_WIDTH,
      FLOWS      => FLOWS,
      BLOCK_SIZE => BLOCK_SIZE
    )
    port map (
      CLK      => CLK,
      RESET    => RESET,

      -- Write interface (to input component)
      DATA_IN  => switch_in,
      DIN_VLD  => incomp_valid,
      RD_REQ   => blk_write_allow,

      -- Read interface (to storage memory)
      DATA_OUT => switch_out,
      DOUT_VLD => switch_valid,
      WR_ADDR  => switch_wr_addr,
      CNT_WR   => cnt_wr_addr,
      REG_WR   => blk_wr_addr,
      BLK_FULL => blk_full
    );

  MORE_FLOWS_FIELD : for j in 0 to FLOWS-1 generate
    write_addr(j) <= switch_wr_addr((j*log2(BLOCK_SIZE*FLOWS))+log2(BLOCK_SIZE*FLOWS)-1 downto j*log2(BLOCK_SIZE*FLOWS))
                     - addr_fix(conv_integer(switch_wr_addr((j*log2(BLOCK_SIZE*FLOWS))+log2(BLOCK_SIZE*FLOWS)-1 downto j*log2(BLOCK_SIZE*FLOWS)+BLOCK_SIZE_W)));
  end generate;

end generate;

FIELD : for j in 0 to FLOWS-1 generate

  incomp : entity work.SH_FIFO
    generic map (
      FIFO_WIDTH => FLOW_WIDTH,
      FIFO_DEPTH => INCOMP_ITEMS,
      USE_INREG  => false,
      USE_OUTREG => false
    )
    port map (
      CLK    => CLK,
      RESET  => RESET,

      WE     => write_allow(j),
      DIN    => DATA_IN(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j),

      RE     => blk_write_allow(j),
      DOUT   => incomp_dout(j),

      FULL   => incomp_full(j),
      EMPTY  => incomp_empty(j)
    );

  -- sh_fifo does not have valid signal
  incomp_valid(j) <= not incomp_empty(j);

  memory : entity work.BUF_MEM
    generic map (
      LUT_MEMORY => LUT_MEMORY,
      DATA_WIDTH => FLOW_WIDTH,
      ITEMS      => BLOCK_SIZE*FLOWS,
      OUTPUT_REG => OUTPUT_REG
    )
    port map (
      CLK      => CLK,
      RESET    => RESET,

      -- Write interface
      WR_ADDR  => write_addr(j),
      DATA_IN  => mem_in(j),
      WRITE    => switch_valid(j),

      -- Read interface
      RD_ADDR  => read_addr,
      DATA_OUT => DATA_OUT(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j),
      DATA_VLD => mem_valid(j),
      READ     => READ,
      PIPE_EN  => PIPE_EN
    );

  -- transformations between arrays and vectors
  switch_in(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j) <= incomp_dout(j);
  addr_fix(j) <= ADDR_FIX_CONST(j);
  mem_in(j)   <= switch_out(FLOW_WIDTH*j+FLOW_WIDTH-1 downto FLOW_WIDTH*j);
  cnt_write_addr(j) <= cnt_wr_addr((j*(BLOCK_SIZE_W+1))+BLOCK_SIZE_W downto j*(BLOCK_SIZE_W+1));
  blk_write_addr(j) <= blk_wr_addr((j*(BLOCK_SIZE_W+FLOWS_W+1))+BLOCK_SIZE_W+FLOWS_W downto j*(BLOCK_SIZE_W+FLOWS_W+1));
  rellen(j) <= REL_LEN(j*log2(BLOCK_SIZE+1)+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1));
  STATUS((j*log2(BLOCK_SIZE+1))+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1)) <= blk_status(j);


  is2pow: if (2**log2(BLOCK_SIZE) = BLOCK_SIZE) generate

    -- read address register
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          reg_read_addr(j) <= (others => '0');
        else
          if (REL_LEN_DV(j) = '1') then
            reg_read_addr(j) <= reg_read_addr(j) + rellen(j);
          end if;
        end if;
      end if;
    end process;

  end generate;


  not2pow: if (2**log2(BLOCK_SIZE) /= BLOCK_SIZE) generate

    -- read address register
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          reg_read_addr(j) <= (others => '0');
        else
          if (REL_LEN_DV(j) = '1') then
            if ((BLOCK_SIZE - reg_read_addr(j)(ADDR_RANGE)) <= rellen(j)) then
              reg_read_addr(j)(ADDR_RANGE)   <= rellen(j) - (BLOCK_SIZE - reg_read_addr(j)(ADDR_RANGE));
              reg_read_addr(j)(BLOCK_SIZE_W) <= not reg_read_addr(j)(BLOCK_SIZE_W);
            else
              reg_read_addr(j) <= reg_read_addr(j) + rellen(j);
            end if;
          end if;
        end if;
      end if;
    end process;

  end generate;


  -- writing to last memory allowed
  process(blk_write_allow, blk_write_addr)
  begin
    if ((blk_write_allow(j) = '1') and
        (blk_write_addr(j)(GLOB_MEM_RANGE) = conv_std_logic_vector(FLOWS-1, FLOWS_W))) then
      last_mem_wr_en(j) <= '1';
    else
      last_mem_wr_en(j) <= '0';
    end if;
  end process;

  -- global reading from last memory allowed
  process(write_allow, glob_write_addr)
  begin
    if ((write_allow(j) = '1') and
        (glob_write_addr(j)(GLOB_MEM_RANGE) = conv_std_logic_vector(FLOWS-1, FLOWS_W))) then
      glob_lm_wr_en(j) <= '1';
    else
      glob_lm_wr_en(j) <= '0';
    end if;
  end process;

  blk_status_sigs : entity work.BUF_STATUS
    generic map (
      ITEMS       => BLOCK_SIZE,
      MULTI_WRITE => false,
      MULTI_READ  => true
    )
    port map (
      CLK      => CLK,
      RESET    => RESET,

      WRITE_EN => last_mem_wr_en(j),
      READ_EN  => rellen_dv(j),
      WR_CNT   => cnt_write_addr(j),
      WR_REG   => blk_write_addr(j)(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W),
      RD_CNT   => reg_read_addr(j),
      RD_REG   => reg_read_addr(j),

      EMPTY    => blk_empty(j),
      FULL     => blk_full(j),
      STATUS   => blk_status(j)
    );


  notGlobState : if (GLOB_STATE = false) generate

    glob_write_cnt(j)  <= (others => '0');
    glob_write_addr(j) <= (others => '0');

    sig_full(j) <= incomp_full(j);

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

      WRITE_EN => glob_lm_wr_en(j),
      READ_EN  => rellen_dv(j),
      WR_CNT   => glob_write_cnt(j)(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W),
      WR_REG   => glob_write_addr(j)(BLOCK_SIZE_W+FLOWS_W downto FLOWS_W),
      RD_CNT   => reg_read_addr(j),
      RD_REG   => reg_read_addr(j),

      EMPTY    => open,
      FULL     => glob_full(j),
      STATUS   => glob_status(j)
    );

    -- global address counter -------------------------------------------------
    process(glob_write_cnt_mem)
    begin
      if (glob_write_cnt_mem(j) = conv_std_logic_vector(FLOWS-1, FLOWS_W)) then
        glob_write_mem_rst(j) <= '1';
      else
        glob_write_mem_rst(j) <= '0';
      end if;
    end process;

    process(glob_write_cnt_item)
    begin
      if (glob_write_cnt_item(j) = conv_std_logic_vector(BLOCK_SIZE-1, BLOCK_SIZE_W)) then
        glob_write_item_rst(j) <= '1';
      else
        glob_write_item_rst(j) <= '0';
      end if;
    end process;

    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          glob_write_cnt_mem(j) <= glob_addr_mem_reset;
        else
          if (write_allow(j) = '1') then
            if (glob_write_mem_rst(j) = '1') then
              glob_write_cnt_mem(j) <= (others => '0');
            else
              glob_write_cnt_mem(j) <= glob_write_cnt_mem(j) + 1;
            end if;
          end if;
        end if;
      end if;
    end process;

    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          glob_write_cnt_item(j) <= glob_addr_item_reset;
        else
          if (write_allow(j) = '1') then
            if (glob_write_mem_rst(j) = '1') then
              glob_write_cnt_item(j) <= glob_write_cnt_item(j) + 1;
              if (glob_write_item_rst(j) = '1') then
                glob_write_cnt_item(j) <= (others => '0');
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
          glob_write_cnt_msb(j) <= '0';
        else
          if (write_allow(j) = '1') then
            if ((glob_write_mem_rst(j) = '1') and (glob_write_item_rst(j) = '1')) then
              glob_write_cnt_msb(j) <= not glob_write_cnt_msb(j);
            end if;
          end if;
        end if;
      end if;
    end process;

    glob_write_cnt(j) <= glob_write_cnt_msb(j) & glob_write_cnt_item(j) & glob_write_cnt_mem(j);

    -- global address register ------------------------------------------------
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (RESET = '1') then
          glob_write_addr(j) <= (others => '0');
        else
          if (write_allow(j) = '1') then
            glob_write_addr(j) <= glob_write_cnt(j);
          end if;
        end if;
      end if;
    end process;

    sig_full(j) <= glob_full(j) or incomp_full(j);

    status_sig(j) <= glob_status(j);

  end generate;

end generate;


-- rellen valid register
process(CLK)
begin
  if ((CLK'event) and (CLK = '1')) then
    rellen_dv <= REL_LEN_DV;
  end if;
end process;

-- allow logic
write_allow <= WRITE and (not sig_full);

-- valid signal for memory
process(mem_valid)
begin
  if ((not mem_valid) = conv_std_logic_vector(0, FLOWS)) then
    DATA_VLD <= '1';
  else
    DATA_VLD <= '0';
  end if;
end process;

-- ----------------------------------------------------------------------------
-- interface mapping
EMPTY <= blk_empty;
FULL  <= sig_full;

end architecture;
-- ----------------------------------------------------------------------------
