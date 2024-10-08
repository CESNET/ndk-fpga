-- $Id$
-- mfifo2mem.vhd - ...
-- Copyright (C) 2009 CESNET
-- Author(s): Koranda Karel <xkoran01@stud.fit.vutbr.cz>
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
entity MFIFO2MEM_ALMOST_FULL is
  generic(
    DATA_WIDTH : integer := 64;
    FLOWS      : integer := 2;
    BLOCK_SIZE : integer := 512;
    LUT_MEMORY : boolean := false;
    -- use OUTPUT_REG carefully - combined with PIPE_EN not in '1' can cause
    -- reading data from different block than given by RD_BLK_ADDR
    OUTPUT_REG : boolean := false;
    -- number of free items in fifo when fifo is declared ALMOST_FULL
    FREE_ITEMS : integer := 1
  );

  port(
    CLK         : in  std_logic;
    RESET       : in  std_logic;
    INIT        : in  std_logic_vector(FLOWS-1 downto 0);

    -- Write interface
    DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    WR_BLK_ADDR : in  std_logic_vector(abs(log2(FLOWS)-1) downto 0);
    WRITE       : in  std_logic;
    FULL        : out std_logic_vector(FLOWS-1 downto 0);
    ALMOST_FULL : out std_logic_vector(FLOWS-1 downto 0);

    -- Read interface
    DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0);
    DATA_VLD    : out std_logic;
    RD_BLK_ADDR : in  std_logic_vector(abs(log2(FLOWS)-1) downto 0);
    READ        : in  std_logic;
    PIPE_EN     : in  std_logic;
    EMPTY       : out std_logic_vector(FLOWS-1 downto 0);

    -- new interface
    RD_ADDR       : in  std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);
    REL_LEN       : in  std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);
    REL_LEN_DV    : in  std_logic_vector(FLOWS-1 downto 0);

    STATUS      : out std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);
    STATUS_ALMOST_FULL      : out std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0)
  );
end entity;

-- ----------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of MFIFO2MEM_ALMOST_FULL is

	-- constant BLOCK_SIZE_W : integer := log2(BLOCK_SIZE);
  -- used if BLOCK_SIZE is not a power of 2
  function ADDR_FIX_CONST (FLOW_ID: integer)
    return integer is
  begin
    return FLOW_ID*(2**log2(BLOCK_SIZE) - BLOCK_SIZE);
  end function;

  subtype ADDR_RANGE is natural range log2(BLOCK_SIZE)-1 downto 0;

  type t_addr_low_cnt is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);
  type t_addr_cnt     is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE) downto 0);
  type t_status       is array(FLOWS-1 downto 0) of std_logic_vector(log2(BLOCK_SIZE+1)-1 downto 0);
  type t_fix          is array(FLOWS-1 downto 0) of integer;

	-- write signals
  signal blk_write_allow     : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_addr_rst  : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_addr_low  : t_addr_low_cnt;
  signal cnt_write_addr_high : std_logic_vector(FLOWS-1 downto 0);
  signal cnt_write_addr      : t_addr_cnt;
  signal reg_write_addr      : t_addr_cnt;
  signal write_allow         : std_logic;
  signal write_addr          : std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);

	-- status signals
  signal sig_init            : std_logic_vector(FLOWS-1 downto 0);
  signal blk_full            : std_logic_vector(FLOWS-1 downto 0);
  signal blk_almost_full     : std_logic_vector(FLOWS-1 downto 0);
  signal blk_empty           : std_logic_vector(FLOWS-1 downto 0);
  signal blk_status          : t_status;
  signal blk_status_almost_full          : t_status;
  signal sig_status          : std_logic_vector(log2(BLOCK_SIZE+1)*FLOWS-1 downto 0);

	-- read signals
  signal read_allow          : std_logic;
  signal read_addr           : std_logic_vector(log2(BLOCK_SIZE*FLOWS)-1 downto 0);
  signal reg_read_addr       : t_addr_cnt;

  signal addr_fix            : t_fix;
  signal rellen              : t_status;
  signal rellen_dv           : std_logic_vector(FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------------------------------
-- -- ONE FLOW
-- ----------------------------------------------------------------------------
GEN_ONE_FLOW: if (FLOWS = 1) generate

  blk_write_allow(0) <= WRITE and (not blk_full(0));
  -- blk_read_allow(0)  <= READ and PIPE_EN and (not blk_empty(0));

  write_allow <= blk_write_allow(0);
	read_allow <= READ and (not blk_empty(0));
  -- read_allow  <= blk_read_allow(0);

  write_addr <= reg_write_addr(0)(ADDR_RANGE);
	read_addr <= RD_ADDR;

end generate;
-- ----------------------------------------------------------------------------
-- -- MORE FLOWS
-- ----------------------------------------------------------------------------
GEN_MORE_FLOWS: if (FLOWS > 1) generate

  write_allow <= blk_write_allow(conv_integer(WR_BLK_ADDR));
	read_allow <= READ and (not blk_empty(conv_integer(RD_BLK_ADDR)));
  -- read_allow  <= blk_read_allow(conv_integer(RD_BLK_ADDR));

  write_addr <= (WR_BLK_ADDR & reg_write_addr(conv_integer(WR_BLK_ADDR))(ADDR_RANGE)) - addr_fix(conv_integer(WR_BLK_ADDR));
	read_addr  <= (RD_BLK_ADDR & RD_ADDR) - addr_fix(conv_integer(RD_BLK_ADDR));
  -- read_addr  <= (RD_BLK_ADDR & reg_read_addr(conv_integer(RD_BLK_ADDR))(ADDR_RANGE)) - addr_fix(conv_integer(RD_BLK_ADDR));

end generate;
-- ----------------------------------------------------------------------------
-- -- BLOCK'S GENERATOR
-- ----------------------------------------------------------------------------
GEN_BLOCKS: for j in 0 to FLOWS-1 generate

  GEN_MORE_FLOWS_BLOCKS: if (FLOWS > 1) generate

    -- block write allow
    process(WR_BLK_ADDR, WRITE, blk_full)
    begin
      if (WR_BLK_ADDR = conv_std_logic_vector(j, WR_BLK_ADDR'length)) then
        blk_write_allow(j) <= WRITE and (not blk_full(j));
      else
        blk_write_allow(j) <= '0';
      end if;
    end process;

  end generate;

  -- init signals
  sig_init(j) <= RESET or INIT(j);

  -- write address counter ----------------------------------------------------
  process(cnt_write_addr_low)
  begin
    if (cnt_write_addr_low(j) = conv_std_logic_vector(BLOCK_SIZE-1, log2(BLOCK_SIZE))) then
      cnt_write_addr_rst(j) <= '1';
    else
      cnt_write_addr_rst(j) <= '0';
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (sig_init(j) = '1') then
        cnt_write_addr_low(j) <= conv_std_logic_vector(1, cnt_write_addr_low(j)'length);
      else
        if (blk_write_allow(j) = '1') then
          if (cnt_write_addr_rst(j) = '1') then
            cnt_write_addr_low(j) <= (others => '0');
          else
            cnt_write_addr_low(j) <= cnt_write_addr_low(j) + 1;
          end if;
        end if;
      end if;
    end if;
  end process;

  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (sig_init(j) = '1') then
        cnt_write_addr_high(j) <= '0';
      else
        if (blk_write_allow(j) = '1') then
          if (cnt_write_addr_rst(j) = '1') then
            cnt_write_addr_high(j) <= not cnt_write_addr_high(j);
          end if;
        end if;
      end if;
    end if;
  end process;

  cnt_write_addr(j) <= cnt_write_addr_high(j) & cnt_write_addr_low(j);

  -- write address register ---------------------------------------------------
  process(CLK)
  begin
    if ((CLK'event) and (CLK = '1')) then
      if (sig_init(j) = '1') then
        reg_write_addr(j) <= (others => '0');
      else
        if (blk_write_allow(j) = '1') then
          reg_write_addr(j) <= cnt_write_addr(j);
        end if;
      end if;
    end if;
  end process;

  -- read address counter -----------------------------------------------------
  -- read address register ----------------------------------------------------
  is2pow: if (2**log2(BLOCK_SIZE) = BLOCK_SIZE) generate

    -- read address register
    process(CLK)
    begin
      if ((CLK'event) and (CLK = '1')) then
        if (sig_init(j) = '1') then
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
        if (sig_init(j) = '1') then
          reg_read_addr(j) <= (others => '0');
        else
          if (REL_LEN_DV(j) = '1') then
            if ((BLOCK_SIZE - reg_read_addr(j)(ADDR_RANGE)) <= rellen(j)) then
              reg_read_addr(j)(ADDR_RANGE)   <= rellen(j) - (BLOCK_SIZE - reg_read_addr(j)(ADDR_RANGE));
              reg_read_addr(j)(log2(BLOCK_SIZE)) <= not reg_read_addr(j)(log2(BLOCK_SIZE));
            else
              reg_read_addr(j) <= reg_read_addr(j) + rellen(j);
            end if;
          end if;
        end if;
      end if;
    end process;

  end generate;

  -- status bloky
  blk_status_sigs : entity work.BUF_STATUS_ALMOST_FULL
    generic map (
      ITEMS       => BLOCK_SIZE,
      MULTI_WRITE => false,
      MULTI_READ  => true,
      FREE_ITEMS => FREE_ITEMS
    )
    port map (
      CLK         => CLK,
      RESET       => sig_init(j),

      WRITE_EN    => blk_write_allow(j),
      READ_EN     => rellen_dv(j),
      WR_CNT      => cnt_write_addr(j),
      WR_REG      => reg_write_addr(j),
      RD_CNT      => reg_read_addr(j),
      RD_REG      => reg_read_addr(j),

      EMPTY       => blk_empty(j),
      FULL        => blk_full(j),
      ALMOST_FULL => blk_almost_full(j),
      STATUS      => blk_status(j),
      STATUS_ALMOST_FULL      => blk_status_almost_full(j)
    );

  STATUS_ALMOST_FULL((j*log2(BLOCK_SIZE+1))+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1)) <= blk_status_almost_full(j);

  STATUS((j*log2(BLOCK_SIZE+1))+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1)) <= blk_status(j);
  --sig_status((j+1)*log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1)) <= blk_status(j);
  addr_fix(j) <= ADDR_FIX_CONST(j);
	-- rellen
  rellen(j) <= REL_LEN(j*log2(BLOCK_SIZE+1)+log2(BLOCK_SIZE+1)-1 downto j*log2(BLOCK_SIZE+1));

end generate;

-- ---------------------------------------------------------------------------
-- -- RELLEN VALID REGISTER
-- ---------------------------------------------------------------------------
process (CLK) is
begin
	if CLK'event and CLK = '1' then
		rellen_dv <= REL_LEN_DV;
	end if;
end process;

-- ---------------------------------------------------------------------------
-- -- MEMORY BLOCKS
-- ---------------------------------------------------------------------------
buf_mem_i : entity work.BUF_MEM
  generic map (
    LUT_MEMORY => LUT_MEMORY,
    DATA_WIDTH => DATA_WIDTH,
    ITEMS      => BLOCK_SIZE*FLOWS,
    OUTPUT_REG => OUTPUT_REG
  )
  port map (
    CLK      => CLK,
    RESET    => RESET,

    -- Write interface
    WR_ADDR  => write_addr,
    DATA_IN  => DATA_IN,
    WRITE    => write_allow,

    -- Read interface
    RD_ADDR  => read_addr,
    DATA_OUT => DATA_OUT,
    DATA_VLD => DATA_VLD,
    READ     => READ,
    PIPE_EN  => PIPE_EN
  );

-- ----------------------------------------------------------------------------
-- interface mapping
FULL   <= blk_full;
ALMOST_FULL   <= blk_almost_full;
EMPTY  <= blk_empty;
--STATUS <= sig_status;
-- debug DATA_OUT <= (others => '1');
end architecture;
-- ----------------------------------------------------------------------------
