-- asfifox.vhd: Universal asynchronous (dual clock) FIFO
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- pragma translate_off
library XPM;
use XPM.vcomponents.all;
-- pragma translate_on

-- A universal asynchronous (dual clock) FIFO, suitable both for Xilinx and Intel
-- (Altera) FPGA. Can be parametrically implemented in BRAM or LUTRAM (MLAB on
-- Intel FPGA = 32 items, distributed memory in Xilinx FPGA = 64 items).
entity ASFIFOX is
    generic(
        -- Data word width in bits.
        DATA_WIDTH          : natural := 512;
        -- FIFO depth in number of data words, must be a power of two!
        -- Minimum value is 2.
        ITEMS               : natural := 512;
        -- Select memory implementation. Options:
        --
        -- - "LUT"  - effective for shallow FIFO (approx. ITEMS <= 64),
        -- - "BRAM" - effective for deep FIFO (approx. ITEMS > 64).
        RAM_TYPE            : string  := "BRAM";
        -- First Word Fall Through mode. If FWFT_MODE=True, valid data will be
        -- ready at the ASFIFOX output without RD_EN requests.
        FWFT_MODE           : boolean := True;
        -- Enabled output registers allow better timing for a few flip-flops.
        OUTPUT_REG          : boolean := True;
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        --
        -- - "7SERIES"
        -- - "ULTRASCALE"
        -- - "STRATIX10"
        -- - "ARRIA10"
        -- - "AGILEX"
        DEVICE              : string  := "ULTRASCALE";
        -- Determines how few data words must be left free for
        -- :vhdl:portsignal:`WR_AFULL <asfifox.wr_afull>` to be triggered.
        --
        -- (``currently_stored >= (`` :vhdl:genconstant:`ITEMS <asfifox.items>` ``- ALMOST_FULL_OFFSET)``
        ALMOST_FULL_OFFSET  : natural := ITEMS/2;
        -- Determines how few data words must be stored for
        -- :vhdl:portsignal:`RD_AEMPTY <asfifox.rd_aempty>` to be triggered.
        --
        -- ( ``currently_stored <= ALMOST_EMPTY_OFFSET`` )
        ALMOST_EMPTY_OFFSET : natural := ITEMS/2
    );
    port(
        -- =====================================================================
        --  WRITE INTERFACE
        -- =====================================================================

        -- Clock for write interface
        WR_CLK    : in  std_logic;
        -- Reset for write interface. Does not affect reset on read side
        WR_RST    : in  std_logic;
        -- Data to be written; must be valid when ``WR_EN = '1'``
        WR_DATA   : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Indicates the validity of ``WR_DATA``. Can be connected as SRC_RDY.
        WR_EN     : in  std_logic;
        -- Writing is accepted only when WR_FULL=0, otherwise it is ignored.
        -- Can be connected as "not DST_RDY".
        WR_FULL   : out std_logic;
        -- Set to ``'1'`` when less than
        -- :vhdl:genconstant:`ALMOST_FULL_OFFSET <asfifox.almost_full_offset>`
        -- space is left for writing items.
        WR_AFULL  : out std_logic;
        -- Indicates the number of items currently stored in the FIFO
        WR_STATUS : out std_logic_vector(log2(ITEMS) downto 0);

        -- =====================================================================
        --  READ INTERFACE
        -- =====================================================================

        -- Clock for read interface
        RD_CLK    : in  std_logic;
        -- Reset for read interface. Does not affect reset on write side
        RD_RST    : in  std_logic;
        -- Data available for reading; valid when ``RD_EMPTY = '0'``
        RD_DATA   : out std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Set to ``'1'`` to request or accept valid data on RD_DATA.
        -- Can be connected as DST_RDY.
        RD_EN     : in  std_logic;
        -- When in ``'0'`` indicates valid data on ``RD_DATA``.
        -- Can be connected as "not SRC_RDY".
        RD_EMPTY  : out std_logic;
        -- Set to ``'1'`` when less than
        -- :vhdl:genconstant:`ALMOST_EMPTY_OFFSET <asfifox.almost_empty_offset>`
        -- items are left for reading.
        RD_AEMPTY : out std_logic;
        -- Indicates the number of items currently stored in the FIFO. Items in
        -- output registers are also included in the calculation. There may be
        -- cases where ``RD_STATUS > 0`` and data are not yet available at the
        -- output (``RD_EMPTY = '1'``).
        RD_STATUS : out std_logic_vector(log2(ITEMS) downto 0)
    );
end entity;

architecture behavioral of ASFIFOX is

    component xpm_memory_sdpram
    generic (
        MEMORY_SIZE             : integer := 2048           ;
        MEMORY_PRIMITIVE        : string  := "auto"         ;
        CLOCKING_MODE           : string  := "common_clock" ;
        ECC_MODE                : string  := "no_ecc"       ;
        MEMORY_INIT_FILE        : string  := "none"         ;
        MEMORY_INIT_PARAM       : string  := ""             ;
        USE_MEM_INIT            : integer := 1              ;
        WAKEUP_TIME             : string  := "disable_sleep";
        AUTO_SLEEP_TIME         : integer := 0              ;
        MESSAGE_CONTROL         : integer := 0              ;
        USE_EMBEDDED_CONSTRAINT : integer := 0              ;
        MEMORY_OPTIMIZATION     : string  := "true";
        CASCADE_HEIGHT          : integer := 0               ;
        SIM_ASSERT_CHK          : integer := 0               ;
        WRITE_DATA_WIDTH_A      : integer := 32 ;
        BYTE_WRITE_WIDTH_A      : integer := 32 ;
        ADDR_WIDTH_A            : integer := 6  ;
        RST_MODE_A              : string  := "SYNC";
        READ_DATA_WIDTH_B       : integer := 32          ;
        ADDR_WIDTH_B            : integer := 6           ;
        READ_RESET_VALUE_B      : string  := "0"         ;
        READ_LATENCY_B          : integer := 2           ;
        WRITE_MODE_B            : string  := "no_change" ;
        RST_MODE_B              : string  := "SYNC"
    );
    port (
        sleep          : in  std_logic;
        clka           : in  std_logic;
        ena            : in  std_logic;
        wea            : in  std_logic_vector((WRITE_DATA_WIDTH_A/BYTE_WRITE_WIDTH_A)-1 downto 0);
        addra          : in  std_logic_vector(ADDR_WIDTH_A-1 downto 0);
        dina           : in  std_logic_vector(WRITE_DATA_WIDTH_A-1 downto 0);
        injectsbiterra : in  std_logic;
        injectdbiterra : in  std_logic;
        clkb           : in  std_logic;
        rstb           : in  std_logic;
        enb            : in  std_logic;
        regceb         : in  std_logic;
        addrb          : in  std_logic_vector(ADDR_WIDTH_B-1 downto 0);
        doutb          : out std_logic_vector(READ_DATA_WIDTH_B-1 downto 0);
        sbiterrb       : out std_logic;
        dbiterrb       : out std_logic
    );
    end component;

    constant MEM_ADDR_WIDTH : natural := log2(ITEMS);
    constant ADDR_WIDTH     : natural := MEM_ADDR_WIDTH+1;
    constant AFULL_CAPACITY : natural := ITEMS - ALMOST_FULL_OFFSET;

    signal arst                : std_logic;
    signal rd_arst             : std_logic;
    signal wr_arst             : std_logic;

    signal write_allow         : std_logic;
    signal read_request        : std_logic;
    signal read_allow          : std_logic;

    signal lutram_dout         : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal lutram_dout_reg     : std_logic_vector(DATA_WIDTH-1 downto 0);

    signal ram_vld             : std_logic;
    signal ram_dout_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal ram_vld_reg         : std_logic;
    signal ram_dout_reg2       : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal ram_vld_reg2        : std_logic;
    signal rd_data_vld         : std_logic;

    signal full_msb_equal      : std_logic;
    signal full_addr_equal     : std_logic;
    signal full_flag           : std_logic;
    signal full_flag_reg       : std_logic;

    signal wr_addr_cnt         : unsigned(ADDR_WIDTH-1 downto 0);
    signal wr_addr_cnt_next    : unsigned(ADDR_WIDTH-1 downto 0);
    signal wr_addr_mem         : std_logic_vector(MEM_ADDR_WIDTH-1 downto 0);
    signal wr_addr_gray        : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal wr_addr_gray_synced : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal wr_addr_synced      : unsigned(ADDR_WIDTH-1 downto 0);
    signal wr_addr_synced_reg  : unsigned(ADDR_WIDTH-1 downto 0);

    signal rd_addr_cnt         : unsigned(ADDR_WIDTH-1 downto 0);
    signal rd_addr_cnt_next    : unsigned(ADDR_WIDTH-1 downto 0);
    signal rd_addr_cnt_mem     : unsigned(MEM_ADDR_WIDTH-1 downto 0);
    signal rd_addr_mem         : std_logic_vector(MEM_ADDR_WIDTH-1 downto 0);
    signal rd_addr_gray        : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal rd_addr_gray_synced : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal rd_addr_synced      : unsigned(ADDR_WIDTH-1 downto 0);
    signal rd_addr_synced_reg  : unsigned(ADDR_WIDTH-1 downto 0);

    signal out_reg_valids      : std_logic_vector(2-1 downto 0);
    signal out_reg_status_uns  : unsigned(2-1 downto 0);

    signal wr_status_uns       : unsigned(log2(ITEMS) downto 0);
    signal rd_status_uns       : unsigned(log2(ITEMS) downto 0);

    attribute preserve : boolean;
    attribute preserve of rd_addr_cnt_mem: signal is true;

begin

    arst <= RD_RST or WR_RST;

    wr_arst_i : entity work.ASYNC_RESET
    generic map(
       TWO_REG => false
    )
    port map(
       CLK        => WR_CLK,
       ASYNC_RST  => arst,
       OUT_RST(0) => wr_arst
    );

    rd_arst_i : entity work.ASYNC_RESET
    generic map(
       TWO_REG => false
    )
    port map(
       CLK        => RD_CLK,
       ASYNC_RST  => arst,
       OUT_RST(0) => rd_arst
    );

    fwft_mode_on_g : if FWFT_MODE generate
        read_request <= RD_EN or not rd_data_vld;
    end generate;

    fwft_mode_off_g : if not FWFT_MODE generate
        read_request <= RD_EN;
    end generate;

    read_allow  <= (read_request and ram_vld);
    write_allow <= (WR_EN and not full_flag_reg);

    -- =========================================================================
    --  SIMPLE DUAL PORT MEMORY
    -- =========================================================================

    sdp_bram_g : if (RAM_TYPE = "BRAM") or (RAM_TYPE = "AUTO") generate
        sdp_bram_i : entity work.SDP_BRAM_BEHAV
        generic map(
            DATA_WIDTH => DATA_WIDTH,
            ITEMS      => ITEMS,
            OUTPUT_REG => False
        )
        port map(
            WR_CLK      => WR_CLK,
            WR_ADDR     => wr_addr_mem,
            WR_EN       => write_allow,
            WR_DIN      => WR_DATA,

            RD_CLK      => RD_CLK,
            RD_RST      => rd_arst,
            RD_CE       => read_request,
            RD_REG_CE   => read_request,
            RD_ADDR     => rd_addr_mem,
            RD_EN       => '1',
            RD_DOUT     => ram_dout_reg,
            RD_DOUT_VLD => open
        );
    end generate;

    sdp_lutram_g : if (RAM_TYPE = "LUT") generate
        device_g : if (DEVICE = "7SERIES") or (DEVICE = "ULTRASCALE") generate
            -- use Xilinx XPM macro with embedded constraints (UG974)
            sdp_lutram_xilinx_i : xpm_memory_sdpram
            generic map (
                ADDR_WIDTH_A            => MEM_ADDR_WIDTH,
                ADDR_WIDTH_B            => MEM_ADDR_WIDTH,
                AUTO_SLEEP_TIME         => 0,
                BYTE_WRITE_WIDTH_A      => DATA_WIDTH,
              --CASCADE_HEIGHT          => 0, -- not compatible with Vivado 2018 and older
                CLOCKING_MODE           => "independent_clock",
                ECC_MODE                => "no_ecc",
                MEMORY_INIT_FILE        => "none",
                MEMORY_INIT_PARAM       => "0",
                MEMORY_OPTIMIZATION     => "true",
                MEMORY_PRIMITIVE        => "distributed",
                MEMORY_SIZE             => (2**MEM_ADDR_WIDTH)*DATA_WIDTH,
                MESSAGE_CONTROL         => 0,
                READ_DATA_WIDTH_B       => DATA_WIDTH,
                READ_LATENCY_B          => 1,
                READ_RESET_VALUE_B      => "0",
              --RST_MODE_A              => "SYNC", -- not compatible with Vivado 2018 and older
              --RST_MODE_B              => "SYNC", -- not compatible with Vivado 2018 and older
              --SIM_ASSERT_CHK          => 1, -- not compatible with Vivado 2018 and older
                USE_EMBEDDED_CONSTRAINT => 1,
                USE_MEM_INIT            => 0,
                WAKEUP_TIME             => "disable_sleep",
                WRITE_DATA_WIDTH_A      => DATA_WIDTH,
                WRITE_MODE_B            => "read_first"
            )
            port map (
                dbiterrb       => open,
                doutb          => lutram_dout_reg,
                sbiterrb       => open,
                addra          => wr_addr_mem,
                addrb          => rd_addr_mem,
                clka           => WR_CLK,
                clkb           => RD_CLK,
                dina           => WR_DATA,
                ena            => '1',
                enb            => read_request,
                injectdbiterra => '0',
                injectsbiterra => '0',
                regceb         => read_request,
                rstb           => '0',
                sleep          => '0',
                wea(0)         => write_allow
            );

        else generate -- others devices
            sdp_lutram_i : entity work.GEN_LUTRAM
            generic map (
                DATA_WIDTH         => DATA_WIDTH,
                ITEMS              => ITEMS,
                RD_PORTS           => 1,
                RD_LATENCY         => 0,
                WRITE_USE_RD_ADDR0 => False,
                MLAB_CONSTR_RDW_DC => False,
                DEVICE             => DEVICE
            )
            port map (
                CLK     => WR_CLK,
                WR_EN   => write_allow,
                WR_ADDR => wr_addr_mem,
                WR_DATA => WR_DATA,
                RD_ADDR => rd_addr_mem,
                RD_DATA => lutram_dout
            );

            lutram_dout_reg_p : process (RD_CLK)
            begin
                if (rising_edge(RD_CLK)) then
                    if (read_request = '1') then
                        lutram_dout_reg <= lutram_dout;
                    end if;
                end if;
            end process;

        end generate;
        ram_dout_reg <= lutram_dout_reg;
    end generate;

    ram_vld_reg_p : process (RD_CLK, rd_arst)
    begin
        if (rd_arst = '1') then
            ram_vld_reg <= '0';
        elsif (rising_edge(RD_CLK)) then
            if (read_request = '1') then
                ram_vld_reg <= ram_vld;
            end if;
        end if;
    end process;

    output_reg_on_g : if OUTPUT_REG generate
        ram_dout_reg2_p : process (RD_CLK)
        begin
            if (rising_edge(RD_CLK)) then
                if (read_request = '1') then
                    ram_dout_reg2 <= ram_dout_reg;
                end if;
            end if;
        end process;

        ram_vld_reg2_p : process (RD_CLK, rd_arst)
        begin
            if (rd_arst = '1') then
                ram_vld_reg2 <= '0';
            elsif (rising_edge(RD_CLK)) then
                if (read_request = '1') then
                    ram_vld_reg2 <= ram_vld_reg;
                end if;
            end if;
        end process;

        RD_DATA     <= ram_dout_reg2;
        rd_data_vld <= ram_vld_reg2;
    end generate;

    output_reg_off_g : if not OUTPUT_REG generate
        ram_dout_reg2 <= (others => '0');
        ram_vld_reg2  <= '0';

        RD_DATA     <= ram_dout_reg;
        rd_data_vld <= ram_vld_reg;
    end generate;

    RD_EMPTY <= not rd_data_vld;

    -- =========================================================================
    --  WRITE ADDRESS LOGIC
    -- =========================================================================

    wr_addr_cnt_p : process (WR_CLK, wr_arst)
    begin
        if (wr_arst = '1') then
            wr_addr_cnt <= (others => '0');
        elsif (rising_edge(WR_CLK)) then
            wr_addr_cnt <= wr_addr_cnt_next;
        end if;
    end process;

    wr_addr_cnt_next <= wr_addr_cnt + write_allow;
    wr_addr_mem <= std_logic_vector(wr_addr_cnt(MEM_ADDR_WIDTH-1 downto 0));

    -- -------------------------------------------------------------------------
    --  WRITE ADDRESS TO GRAY CODE CONVERSION
    -- -------------------------------------------------------------------------

    wr_addr_gray(ADDR_WIDTH-1) <= wr_addr_cnt(ADDR_WIDTH-1);

    wr_addr_gray_g : for i in ADDR_WIDTH-2 downto 0 generate
        wr_addr_gray(i) <= wr_addr_cnt(i+1) xor wr_addr_cnt(i);
    end generate;

    -- -------------------------------------------------------------------------
    --  WRITE ADDRESS SYCHRONIZATION (CDC)
    -- -------------------------------------------------------------------------

    wr_addr_gray_synced_i : entity work.ASYNC_OPEN_LOOP_SMD
    generic map(
        DATA_WIDTH => ADDR_WIDTH,
        ASYNC_RST  => True
    )
    port map(
        ACLK     => WR_CLK,
        ARST     => wr_arst,
        ADATAIN  => wr_addr_gray,

        BCLK     => RD_CLK,
        BRST     => rd_arst,
        BDATAOUT => wr_addr_gray_synced
    );

    -- -------------------------------------------------------------------------
    --  WRITE ADDRESS TO BINARY CONVERSION
    -- -------------------------------------------------------------------------

    wr_addr_synced(ADDR_WIDTH-1) <= wr_addr_gray_synced(ADDR_WIDTH-1);

    wr_addr_synced_g : for i in ADDR_WIDTH-2 downto 0 generate
        wr_addr_synced(i) <= wr_addr_synced(i+1) xor wr_addr_gray_synced(i);
    end generate;

    wr_addr_synced_reg_p : process (RD_CLK, rd_arst)
    begin
        if (rd_arst = '1') then
            wr_addr_synced_reg <= (others => '0');
        elsif (rising_edge(RD_CLK)) then
            wr_addr_synced_reg <= wr_addr_synced;
        end if;
    end process;

    -- =========================================================================
    --  READ ADDRESS LOGIC
    -- =========================================================================

    rd_addr_cnt_p : process (RD_CLK, rd_arst)
    begin
        if (rd_arst = '1') then
            rd_addr_cnt <= (others => '0');
        elsif (rising_edge(RD_CLK)) then
            if (read_allow = '1') then
                rd_addr_cnt <= rd_addr_cnt_next;
            end if;
        end if;
    end process;

    rd_addr_cnt_next <= rd_addr_cnt + 1;

    rd_addr_cnt_mem_p : process (RD_CLK, rd_arst)
    begin
        if (rd_arst = '1') then
            rd_addr_cnt_mem <= (others => '0');
        elsif (rising_edge(RD_CLK)) then
            if (read_allow = '1') then
                rd_addr_cnt_mem <= rd_addr_cnt_mem + 1;
            end if;
        end if;
    end process;

    rd_addr_mem <= std_logic_vector(rd_addr_cnt_mem);

    -- -------------------------------------------------------------------------
    --  READ ADDRESS TO GRAY CODE CONVERSION
    -- -------------------------------------------------------------------------

    rd_addr_gray(ADDR_WIDTH-1) <= rd_addr_cnt(ADDR_WIDTH-1);

    rd_addr_gray_g : for i in ADDR_WIDTH-2 downto 0 generate
        rd_addr_gray(i) <= rd_addr_cnt(i+1) xor rd_addr_cnt(i);
    end generate;

    -- -------------------------------------------------------------------------
    --  READ ADDRESS SYCHRONIZATION (CDC)
    -- -------------------------------------------------------------------------

    rd_addr_gray_synced_i : entity work.ASYNC_OPEN_LOOP_SMD
    generic map(
        DATA_WIDTH => ADDR_WIDTH,
        ASYNC_RST  => True
    )
    port map(
        ACLK     => RD_CLK,
        ARST     => rd_arst,
        ADATAIN  => rd_addr_gray,

        BCLK     => WR_CLK,
        BRST     => wr_arst,
        BDATAOUT => rd_addr_gray_synced
    );

    -- -------------------------------------------------------------------------
    --  READ ADDRESS TO BINARY CONVERSION
    -- -------------------------------------------------------------------------

    rd_addr_synced(ADDR_WIDTH-1) <= rd_addr_gray_synced(ADDR_WIDTH-1);

    rd_addr_synced_g : for i in ADDR_WIDTH-2 downto 0 generate
        rd_addr_synced(i) <= rd_addr_synced(i+1) xor rd_addr_gray_synced(i);
    end generate;

    rd_addr_synced_reg_p : process (WR_CLK, wr_arst)
    begin
        if (wr_arst = '1') then
            rd_addr_synced_reg <= (others => '0');
        elsif (rising_edge(WR_CLK)) then
            rd_addr_synced_reg <= rd_addr_synced;
        end if;
    end process;

    -- =========================================================================
    --  READ DATA VALID AND FULL FLAG LOGIC
    -- =========================================================================

    -- RAM data valid flag logic, is high when RAM is not empty
    ram_vld <= '0' when (rd_addr_cnt = wr_addr_synced_reg) else '1';

    -- full flag logic
    full_msb_equal  <= '1' when (wr_addr_cnt_next(ADDR_WIDTH-1) = rd_addr_synced_reg(ADDR_WIDTH-1)) else '0';
    full_addr_equal <= '1' when (wr_addr_cnt_next(ADDR_WIDTH-2 downto 0) = rd_addr_synced_reg(ADDR_WIDTH-2 downto 0)) else '0';
    full_flag       <= not full_msb_equal and full_addr_equal;

    -- full flag register
    process (WR_CLK, wr_arst)
    begin
        if (wr_arst = '1') then
            full_flag_reg <= '1';
        elsif (rising_edge(WR_CLK)) then
            full_flag_reg <= full_flag;
        end if;
    end process;

    WR_FULL <= full_flag_reg;

    -- =========================================================================
    --  WRITE STATUS LOGIC
    -- =========================================================================

    wr_status_uns <= wr_addr_cnt - rd_addr_synced_reg;
    WR_STATUS     <= std_logic_vector(wr_status_uns);

    WR_AFULL <= '1' when (wr_status_uns >= AFULL_CAPACITY) else '0';

    -- =========================================================================
    --  READ STATUS LOGIC
    -- =========================================================================

    out_reg_valids <= ram_vld_reg2 & ram_vld_reg;

    with out_reg_valids select
    out_reg_status_uns <= "10" when "11",
                          "01" when "01",
                          "01" when "10",
                          "00" when others;

    rd_status_uns <= (wr_addr_synced_reg - rd_addr_cnt) + out_reg_status_uns;
    RD_STATUS     <= std_logic_vector(rd_status_uns);

    RD_AEMPTY <= '1' when (rd_status_uns <= ALMOST_EMPTY_OFFSET) else '0';

end architecture;
