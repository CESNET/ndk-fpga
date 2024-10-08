-- asfifo_bram_xilinx.vhd: Asynchronous FIFO implemented in Xilinx BRAMs
-- Copyright (C) 2016 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;
use work.math_pack.all;
use work.type_pack.all;

Library UNISIM;
use UNISIM.vcomponents.all;



entity ASFIFO_BRAM_XILINX is
  generic(
    DEVICE                  : string := "ULTRASCALE"; --! "VIRTEX6", "7SERIES", "ULTRASCALE"
    DATA_WIDTH              : integer := 64; --! any possitive value
    ITEMS                   : integer := 512; --! 512, 1024, 2048, 4096, 8192 (less effective)
    FIRST_WORD_FALL_THROUGH : boolean := true;
    DO_REG                  : boolean := true; -- forced true when FIRST_WORD_FALL_THROUGH is true on VIRTEX6 or 7SERIES devices
    ALMOST_FULL_OFFSET      : integer := 128;
    ALMOST_EMPTY_OFFSET     : integer := 128;
    IS_RD_INVERTED          : boolean := false;
    IS_WR_INVERTED          : boolean := false;
    -- Precision of FULL signal (write interface) assertion.
    --    true = full FIFO's depth can be used, but timing on WR and FULL is worse for high DATA_WIDTH
    --   false = FIFO is 4 items shallower (take this into accont when setting a value of ALMOST_FULL_OFFSET!), but timing on WR and FULL is better
    -- NOTE: disabling makes a difference only when DATA_WIDTH is more than 72
    PRECISE_FULL            : boolean := true;
    -- Timing speed of EMPTY signal (read interface) assertion.
    --   false = standard ORing of flags (just a few LUTs), but timing on RD anf EMPTY is worse for high DATA_WIDTH
    --    true = more extra resources (mainly registers or SRL), but timing on RD and EMPTY is better
    -- NOTE: enabling makes a difference only when FIRST_WORD_FALL_THROUGH is true, DEVICE is VIRTEX6 or 7SERIES and FIFO size (DATA_WIDTH*ITEMS) is more than 36Kb
    FAST_EMPTY              : boolean := false;
    -- Parameter required to be correctly set when FAST_EMPTY is true.
    --   CLK_RD_PERIOD <= CLK_WR_PERIOD : value of 1 is sufficient
    --    CLK_RD_PERIOD > CLK_WR_PERIOD : value must be at least roundup(CLK_RD_PERIOD/CLK_WR_PERIOD)
    FAST_EMPTY_DEPTH        : integer := 1
  );
  port(
    RST_WR   : in  std_logic; -- can be async reset on VIRTEX6 and 7SERIES devices
    CLK_WR   : in  std_logic;
    DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    WR       : in  std_logic;
    AFULL    : out std_logic;
    FULL     : out std_logic;

    RST_RD   : in  std_logic; -- not used!
    CLK_RD   : in  std_logic;
    DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    RD       : in  std_logic;
    AEMPTY   : out std_logic;
    EMPTY    : out std_logic
  );
end entity;



architecture arch of ASFIFO_BRAM_XILINX is

  signal reset_async : std_logic; -- Ignore timing at this signal
  attribute dont_touch : string;
  attribute dont_touch of reset_async : signal is "true";

begin

  v6_v7_gen : if DEVICE = "VIRTEX6" or DEVICE = "7SERIES" generate

    constant I : integer := tsel(
        ITEMS <= 512,   512, tsel(
        ITEMS <= 1024, 1024, tsel(
        ITEMS <= 2048, 2048, tsel(
        ITEMS <= 4096, 4096, 8192
      ))));
    constant DW36D : integer := 32768 / I;
    constant DW36P : integer := DW36D / 8;
    constant DW36 : integer := DW36D + DW36P;
    constant DW18D : integer := tsel(I = 8192, 0, 16384 / I);
    constant DW18P : integer := DW18D / 8;
    constant DW18 : integer := DW18D + DW18P;
    constant ROWS : integer := ((DATA_WIDTH-1) / DW36) + 1;
    constant LAST_WIDTH : integer := DATA_WIDTH - ((ROWS-1)*DW36);
    constant LAST18 : boolean := LAST_WIDTH <= DW18;
    constant DO_REG_FINAL : integer := tsel(DO_REG or FIRST_WORD_FALL_THROUGH, 1, 0);

    signal di_rows : std_logic_vector(DW36*ROWS-1 downto 0) := (others => '0');
    signal di_last : std_logic_vector(DW36-1 downto 0) := (others => '0');
    signal do_rows : std_logic_vector(DW36*ROWS-1 downto 0) := (others => '0');
    signal full_vec, afull_vec : std_logic_vector(ROWS-1 downto 0);
    signal full_agr, afull_agr : std_logic;
    signal empty_vec, aempty_vec : std_logic_vector(ROWS-1 downto 0);
    signal empty_agr, aempty_agr : std_logic;
    signal rden, wren, wren_rst, wren_last : std_logic;

  begin

    di_rows(DATA_WIDTH-1 downto 0) <= DI;
    AFULL <= afull_agr;
    FULL <= full_agr;
    DO <= do_rows(DATA_WIDTH-1 downto 0);
    AEMPTY <= aempty_agr;
    EMPTY <= empty_agr;

    -- falling-edge flag uncertainty (UG473)
    afull_agr <= afull_vec(0);
    precise_full_gen : if PRECISE_FULL or ROWS=1 generate
      full_agr <= or_reduce(full_vec);
    end generate;
    fast_full_gen : if not PRECISE_FULL and ROWS>1 generate
      full_agr <= afull_vec(1);
    end generate;
    wr_al_gen : if IS_WR_INVERTED generate
      wren <= not WR and not full_agr;
    end generate;
    wr_ah_gen : if not IS_WR_INVERTED generate
      wren <= WR and not full_agr;
    end generate;
    aempty_agr <= aempty_vec(0);
    slow_empty_gen : if not FAST_EMPTY or ROWS<3 generate
      empty_agr <= or_reduce(empty_vec);
      wren_last <= wren;
      di_last(LAST_WIDTH-1 downto 0) <= di_rows(DW36*(ROWS-1)+LAST_WIDTH-1 downto DW36*(ROWS-1));
    end generate;
    fast_empty_gen : if FAST_EMPTY and ROWS>2 generate
      empty_agr <= empty_vec(ROWS-1);
      wren_reg : entity work.SH_REG_BASE_STATIC
        generic map (
          DATA_WIDTH      => 1,
          NUM_BITS        => FAST_EMPTY_DEPTH,
          OPT             => tsel(FAST_EMPTY_DEPTH>1, "SRL", "REG")
        ) port map (
          CLK      => CLK_WR,
          CE       => '1',
          DIN(0)   => wren_rst,
          DOUT(0)  => wren_last
        );
      wren_rst <= wren and not RST_WR;
      data_reg : entity work.SH_REG_BASE_STATIC
        generic map (
          DATA_WIDTH      => LAST_WIDTH,
          NUM_BITS        => FAST_EMPTY_DEPTH,
          OPT             => tsel(FAST_EMPTY_DEPTH>1, "SRL", "REG")
        ) port map (
          CLK      => CLK_WR,
          CE       => '1',
          DIN      => di_rows(DW36*(ROWS-1)+LAST_WIDTH-1 downto DW36*(ROWS-1)),
          DOUT     => di_last(LAST_WIDTH-1 downto 0)
        );
    end generate;
    rd_al_gen : if IS_RD_INVERTED generate
      rden <= not RD and not empty_agr;
    end generate;
    rd_ah_gen : if not IS_RD_INVERTED generate
      rden <= RD and not empty_agr;
    end generate;

    reset_async <= RST_WR;

    rows_gen : for i in 0 to ROWS-1 generate

      half_gen : if i = ROWS-1 and LAST18 generate
        signal di_local, do_local : std_logic_vector(32-1 downto 0) := (others => '0');
        signal dip_local, dop_local : std_logic_vector(4-1 downto 0) := (others => '0');
      begin
        fifo_i : FIFO18E1
          generic map (
            ALMOST_EMPTY_OFFSET => conv_bit_vector(ALMOST_EMPTY_OFFSET,13),
            ALMOST_FULL_OFFSET  => conv_bit_vector(tsel(i=0, ALMOST_FULL_OFFSET, 4),13),
            DATA_WIDTH          => DW18,
            DO_REG              => DO_REG_FINAL,
            EN_SYN              => false,
            FIFO_MODE           => tsel(DW18 = 36, "FIFO18_36", "FIFO18"),
            FIRST_WORD_FALL_THROUGH => FIRST_WORD_FALL_THROUGH,
            SIM_DEVICE          => "7SERIES"
          ) port map (
            DO                  => do_local,
            DOP                 => dop_local,
            ALMOSTEMPTY         => aempty_vec(i),
            ALMOSTFULL          => afull_vec(i),
            EMPTY               => empty_vec(i),
            FULL                => full_vec(i),
            RDCOUNT             => open,
            RDERR               => open,
            WRCOUNT             => open,
            WRERR               => open,
            RDCLK               => CLK_RD,
            RDEN                => rden,
            REGCE               => '1',
            RST                 => reset_async,
            RSTREG              => '0', -- not used when EN_SYN is false
            WRCLK               => CLK_WR,
            WREN                => wren_last,
            DI                  => di_local,
            DIP                 => dip_local
          );
        do_rows(i*DW36+DW18D-1 downto i*DW36) <= do_local(DW18D-1 downto 0);
        di_local(DW18D-1 downto 0) <= di_last(DW18D-1 downto 0);
        parity_connect_gen : if DW18P > 0 generate
          do_rows(i*DW36+DW18-1 downto i*DW36+DW18D) <= dop_local(DW18P-1 downto 0);
          dip_local(DW18P-1 downto 0) <= di_last(DW18-1 downto DW18D);
        end generate;
      end generate;

      full_gen : if not(i = ROWS-1 and LAST18) generate
        signal di_local, do_local : std_logic_vector(64-1 downto 0) := (others => '0');
        signal dip_local, dop_local : std_logic_vector(8-1 downto 0) := (others => '0');
        signal wren_local : std_logic;
      begin
        fifo_i : FIFO36E1
          generic map (
            ALMOST_EMPTY_OFFSET => conv_bit_vector(ALMOST_EMPTY_OFFSET,13),
            ALMOST_FULL_OFFSET  => conv_bit_vector(tsel(i=0, ALMOST_FULL_OFFSET, 4),13),
            DATA_WIDTH          => DW36,
            DO_REG              => DO_REG_FINAL,
            EN_ECC_READ         => false,
            EN_ECC_WRITE        => false,
            EN_SYN              => false,
            FIFO_MODE           => tsel(DW36 = 72, "FIFO36_72", "FIFO36"),
            FIRST_WORD_FALL_THROUGH => FIRST_WORD_FALL_THROUGH,
            SIM_DEVICE          => "7SERIES"
          ) port map (
            DBITERR             => open,
            ECCPARITY           => open,
            SBITERR             => open,
            DO                  => do_local,
            DOP                 => dop_local,
            ALMOSTEMPTY         => aempty_vec(i),
            ALMOSTFULL          => afull_vec(i),
            EMPTY               => empty_vec(i),
            FULL                => full_vec(i),
            RDCOUNT             => open,
            RDERR               => open,
            WRCOUNT             => open,
            WRERR               => open,
            INJECTDBITERR       => '0',
            INJECTSBITERR       => '0',
            RDCLK               => CLK_RD,
            RDEN                => rden,
            REGCE               => '1',
            RST                 => reset_async,
            RSTREG              => '0', -- not used when EN_SYN is false
            WRCLK               => CLK_WR,
            WREN                => wren_local,
            DI                  => di_local,
            DIP                 => dip_local
          );
        inloop_gen : if i /= (ROWS-1) generate
          wren_local <= wren;
          do_rows(i*DW36+DW36D-1 downto i*DW36) <= do_local(DW36D-1 downto 0);
          di_local(DW36D-1 downto 0) <= di_rows(i*DW36+DW36D-1 downto i*DW36);
          parity_connect_gen : if DW36P > 0 generate
            do_rows(i*DW36+DW36-1 downto i*DW36+DW36D) <= dop_local(DW36P-1 downto 0);
            dip_local(DW36P-1 downto 0) <= di_rows(i*DW36+DW36-1 downto i*DW36+DW36D);
          end generate;
        end generate;
        last_gen : if i = (ROWS-1) generate
          wren_local <= wren_last;
          do_rows(i*DW36+DW36D-1 downto i*DW36) <= do_local(DW36D-1 downto 0);
          di_local(DW36D-1 downto 0) <= di_last(DW36D-1 downto 0);
          parity_connect_gen : if DW36P > 0 generate
            do_rows(i*DW36+DW36-1 downto i*DW36+DW36D) <= dop_local(DW36P-1 downto 0);
            dip_local(DW36P-1 downto 0) <= di_last(DW36-1 downto DW36D);
          end generate;
        end generate;
      end generate;
    end generate;
  end generate;



  us_gen : if DEVICE = "ULTRASCALE" generate

    constant I : integer := tsel(
        ITEMS <= 512,   512, tsel(
        ITEMS <= 1024, 1024, tsel(
        ITEMS <= 2048, 2048, tsel(
        ITEMS <= 4096, 4096, 8192
      ))));
    constant DW36D : integer := 32768 / I;
    constant DW36P : integer := DW36D / 8;
    constant DW36 : integer := DW36D + DW36P;
    constant DW18D : integer := tsel(I = 8192, 0, 16384 / I);
    constant DW18P : integer := DW18D / 8;
    constant DW18 : integer := DW18D + DW18P;
    constant ROWS : integer := ((DATA_WIDTH-1) / DW36) + 1;
    constant LAST_WIDTH : integer := DATA_WIDTH - ((ROWS-1)*DW36);
    constant LAST18 : boolean := LAST_WIDTH <= DW18;
    constant PROG_FULL_THRESH : integer := I - ALMOST_FULL_OFFSET;
    constant PROG_FULL_THRESH_FF : integer := I - 4;

    signal di_rows : std_logic_vector(DW36*ROWS-1 downto 0) := (others => '0');
    signal di_last : std_logic_vector(DW36-1 downto 0) := (others => '0');
    signal do_rows : std_logic_vector(DW36*ROWS-1 downto 0) := (others => '0');
    signal full_vec, afull_vec : std_logic_vector(ROWS-1 downto 0);
    signal full_agr, afull_agr : std_logic;
    signal empty_vec, aempty_vec : std_logic_vector(ROWS-1 downto 0);
    signal empty_agr, aempty_agr : std_logic;
    signal rdrstbusy_vec, wrrstbusy_vec : std_logic_vector(ROWS-1 downto 0);
    signal rdrstbusy_agr, wrrstbusy_agr : std_logic;
    signal rdrstbusy_reg, wrrstbusy_reg : std_logic;
    signal rden, wren, wren_rst, wren_last : std_logic;

  begin

    di_rows(DATA_WIDTH-1 downto 0) <= DI;
    AFULL <= afull_agr;
    FULL <= full_agr;
    DO <= do_rows(DATA_WIDTH-1 downto 0);
    AEMPTY <= aempty_agr;
    EMPTY <= empty_agr;

    -- reset falling-edge uncertainty solution
    single_row_gen : if ROWS = 1 generate
      wrrstbusy_agr <= wrrstbusy_vec(0);
      rdrstbusy_agr <= rdrstbusy_vec(0);
    end generate;
    many_rows_gen : if ROWS > 1 generate
      wr_reg : process(CLK_WR)
      begin
        if CLK_WR'event and CLK_WR='1' then
          wrrstbusy_reg <= or_reduce(wrrstbusy_vec);
        end if;
      end process;
      rd_reg : process(CLK_RD)
      begin
        if CLK_RD'event and CLK_RD='1' then
          rdrstbusy_reg <= or_reduce(rdrstbusy_vec);
        end if;
      end process;
      wrrstbusy_agr <= wrrstbusy_reg;
      rdrstbusy_agr <= rdrstbusy_reg;
    end generate;

    afull_agr <= afull_vec(0) or wrrstbusy_agr;
    precise_full_gen : if PRECISE_FULL or ROWS=1 generate
      full_agr <= or_reduce(full_vec) or wrrstbusy_agr;
    end generate;
    fast_full_gen : if not PRECISE_FULL and ROWS>1 generate
      full_agr <= afull_vec(1) or wrrstbusy_agr;
    end generate;
    wr_al_gen : if IS_WR_INVERTED generate
      wren <= WR or full_agr;
      wren_rst <= wren or RST_WR;
    end generate;
    wr_ah_gen : if not IS_WR_INVERTED generate
      wren <= WR and not full_agr;
      wren_rst <= wren and not RST_WR;
    end generate;
    aempty_agr <= aempty_vec(0) or rdrstbusy_agr;
    slow_empty_gen : if not FAST_EMPTY or ROWS<3 generate
      empty_agr <= or_reduce(empty_vec) or rdrstbusy_agr;
      wren_last <= wren;
      di_last(LAST_WIDTH-1 downto 0) <= di_rows(DW36*(ROWS-1)+LAST_WIDTH-1 downto DW36*(ROWS-1));
    end generate;
    fast_empty_gen : if FAST_EMPTY and ROWS>2 generate
      empty_agr <= empty_vec(ROWS-1) or rdrstbusy_agr;
      wren_reg : entity work.SH_REG_BASE_STATIC
        generic map (
          DATA_WIDTH      => 1,
          NUM_BITS        => FAST_EMPTY_DEPTH,
          OPT             => tsel(FAST_EMPTY_DEPTH>1, "SRL", "REG")
        ) port map (
          CLK      => CLK_WR,
          CE       => '1',
          DIN(0)   => wren_rst,
          DOUT(0)  => wren_last
        );
      data_reg : entity work.SH_REG_BASE_STATIC
        generic map (
          DATA_WIDTH      => LAST_WIDTH,
          NUM_BITS        => FAST_EMPTY_DEPTH,
          OPT             => tsel(FAST_EMPTY_DEPTH>1, "SRL", "REG")
        ) port map (
          CLK      => CLK_WR,
          CE       => '1',
          DIN      => di_rows(DW36*(ROWS-1)+LAST_WIDTH-1 downto DW36*(ROWS-1)),
          DOUT     => di_last(LAST_WIDTH-1 downto 0)
        );
    end generate;
    rd_al_gen : if IS_RD_INVERTED generate
      rden <= RD or empty_agr;
    end generate;
    rd_ah_gen : if not IS_RD_INVERTED generate
      rden <= RD and not empty_agr;
    end generate;

    reset_async <= '0';

    rows_gen : for i in 0 to ROWS-1 generate

      half_gen : if i = ROWS-1 and LAST18 generate
        signal di_local, do_local : std_logic_vector(32-1 downto 0) := (others => '0');
        signal dip_local, dop_local : std_logic_vector(4-1 downto 0) := (others => '0');
      begin
        fifo_i : FIFO18E2
          generic map (
            CASCADE_ORDER           => "NONE",
            CLOCK_DOMAINS           => "INDEPENDENT",
            FIRST_WORD_FALL_THROUGH => tsel(FIRST_WORD_FALL_THROUGH, "TRUE", "FALSE"),
            PROG_EMPTY_THRESH       => ALMOST_EMPTY_OFFSET,
            PROG_FULL_THRESH        => tsel(i=0, PROG_FULL_THRESH, PROG_FULL_THRESH_FF),
            IS_RDCLK_INVERTED       => '0',
            IS_RDEN_INVERTED        => tsel(IS_RD_INVERTED, '1', '0'),
            IS_RSTREG_INVERTED      => '0',
            IS_RST_INVERTED         => '0',
            IS_WRCLK_INVERTED       => '0',
            IS_WREN_INVERTED        => tsel(IS_WR_INVERTED, '1', '0'),
            RDCOUNT_TYPE            => "RAW_PNTR", -- ignored
            READ_WIDTH              => DW18,
            REGISTER_MODE           => tsel(DO_REG, "REGISTERED", "UNREGISTERED"),
            RSTREG_PRIORITY         => "RSTREG", -- ignored
            SLEEP_ASYNC             => "FALSE", -- ignored
            WRCOUNT_TYPE            => "RAW_PNTR", -- ignored
            WRITE_WIDTH             => DW18
          )port map (
            CASDOUT        => open,
            CASDOUTP       => open,
            CASNXTEMPTY    => open,
            CASPRVRDEN     => open,
            DOUT           => do_local,
            DOUTP          => dop_local,
            EMPTY          => empty_vec(i),
            FULL           => full_vec(i),
            PROGEMPTY      => aempty_vec(i),
            PROGFULL       => afull_vec(i),
            RDCOUNT        => open,
            RDERR          => open,
            RDRSTBUSY      => rdrstbusy_vec(i),
            WRCOUNT        => open,
            WRERR          => open,
            WRRSTBUSY      => wrrstbusy_vec(i),
            CASDIN         => (others => '0'),
            CASDINP        => (others => '0'),
            CASDOMUX       => '0',
            CASDOMUXEN     => '1',
            CASNXTRDEN     => '0',
            CASOREGIMUX    => '0',
            CASOREGIMUXEN  => '1',
            CASPRVEMPTY    => '0',
            RDCLK          => CLK_RD,
            RDEN           => rden,
            REGCE          => '1',
            RSTREG         => '0',
            SLEEP          => '0',
            RST            => RST_WR,
            WRCLK          => CLK_WR,
            WREN           => wren_last,
            DIN            => di_local,
            DINP           => dip_local
          );
        do_rows(i*DW36+DW18D-1 downto i*DW36) <= do_local(DW18D-1 downto 0);
        di_local(DW18D-1 downto 0) <= di_last(DW18D-1 downto 0);
        parity_connect_gen : if DW18P > 0 generate
          do_rows(i*DW36+DW18-1 downto i*DW36+DW18D) <= dop_local(DW18P-1 downto 0);
          dip_local(DW18P-1 downto 0) <= di_last(DW18-1 downto DW18D);
        end generate;
      end generate;

      full_gen : if not(i = ROWS-1 and LAST18) generate
        signal di_local, do_local : std_logic_vector(64-1 downto 0) := (others => '0');
        signal dip_local, dop_local : std_logic_vector(8-1 downto 0) := (others => '0');
        signal wren_local : std_logic;
      begin
        fifo_i : FIFO36E2
          generic map (
            CASCADE_ORDER           => "NONE",
            CLOCK_DOMAINS           => "INDEPENDENT",
            EN_ECC_PIPE             => "FALSE", -- ignored
            EN_ECC_READ             => "FALSE", -- ignored
            EN_ECC_WRITE            => "FALSE", -- ignored
            FIRST_WORD_FALL_THROUGH => tsel(FIRST_WORD_FALL_THROUGH, "TRUE", "FALSE"),
            PROG_EMPTY_THRESH       => ALMOST_EMPTY_OFFSET,
            PROG_FULL_THRESH        => tsel(i=0, PROG_FULL_THRESH, PROG_FULL_THRESH_FF),
            IS_RDCLK_INVERTED       => '0',
            IS_RDEN_INVERTED        => tsel(IS_RD_INVERTED, '1', '0'),
            IS_RSTREG_INVERTED      => '0',
            IS_RST_INVERTED         => '0',
            IS_WRCLK_INVERTED       => '0',
            IS_WREN_INVERTED        => tsel(IS_WR_INVERTED, '1', '0'),
            RDCOUNT_TYPE            => "RAW_PNTR", -- ignored
            READ_WIDTH              => DW36,
            REGISTER_MODE           => tsel(DO_REG, "REGISTERED", "UNREGISTERED"),
            RSTREG_PRIORITY         => "RSTREG", -- ignored
            SLEEP_ASYNC             => "FALSE", -- ignored
            WRCOUNT_TYPE            => "RAW_PNTR", -- ignored
            WRITE_WIDTH             => DW36
          )port map (
            CASDOUT        => open,
            CASDOUTP       => open,
            CASNXTEMPTY    => open,
            CASPRVRDEN     => open,
            DBITERR        => open,
            ECCPARITY      => open,
            SBITERR        => open,
            DOUT           => do_local,
            DOUTP          => dop_local,
            EMPTY          => empty_vec(i),
            FULL           => full_vec(i),
            PROGEMPTY      => aempty_vec(i),
            PROGFULL       => afull_vec(i),
            RDCOUNT        => open,
            RDERR          => open,
            RDRSTBUSY      => rdrstbusy_vec(i),
            WRCOUNT        => open,
            WRERR          => open,
            WRRSTBUSY      => wrrstbusy_vec(i),
            CASDIN         => (others => '0'),
            CASDINP        => (others => '0'),
            CASDOMUX       => '0',
            CASDOMUXEN     => '1',
            CASNXTRDEN     => '0',
            CASOREGIMUX    => '0',
            CASOREGIMUXEN  => '1',
            CASPRVEMPTY    => '0',
            INJECTDBITERR  => '0',
            INJECTSBITERR  => '0',
            RDCLK          => CLK_RD,
            RDEN           => rden,
            REGCE          => '1',
            RSTREG         => '0',
            SLEEP          => '0',
            RST            => RST_WR,
            WRCLK          => CLK_WR,
            WREN           => wren_local,
            DIN            => di_local,
            DINP           => dip_local
          );
        inloop_gen : if i /= (ROWS-1) generate
          wren_local <= wren;
          do_rows(i*DW36+DW36D-1 downto i*DW36) <= do_local(DW36D-1 downto 0);
          di_local(DW36D-1 downto 0) <= di_rows(i*DW36+DW36D-1 downto i*DW36);
          parity_connect_gen : if DW36P > 0 generate
            do_rows(i*DW36+DW36-1 downto i*DW36+DW36D) <= dop_local(DW36P-1 downto 0);
            dip_local(DW36P-1 downto 0) <= di_rows(i*DW36+DW36-1 downto i*DW36+DW36D);
          end generate;
        end generate;
        last_gen : if i = (ROWS-1) generate
          wren_local <= wren_last;
          do_rows(i*DW36+DW36D-1 downto i*DW36) <= do_local(DW36D-1 downto 0);
          di_local(DW36D-1 downto 0) <= di_last(DW36D-1 downto 0);
          parity_connect_gen : if DW36P > 0 generate
            do_rows(i*DW36+DW36-1 downto i*DW36+DW36D) <= dop_local(DW36P-1 downto 0);
            dip_local(DW36P-1 downto 0) <= di_last(DW36-1 downto DW36D);
          end generate;
        end generate;
      end generate;
    end generate;
  end generate;



  error_gen : if DEVICE /= "ULTRASCALE" and DEVICE /= "VIRTEX6" and DEVICE /= "7SERIES" generate
    assert false report "ASFIFO_BRAM_XILINX: DEVICE not supported!" severity failure;
  end generate;

end architecture;
