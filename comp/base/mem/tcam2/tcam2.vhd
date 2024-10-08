-- tcam2.vhd: TCAM2 component
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- =====================================================================
--                            Entity declaration
-- =====================================================================
entity TCAM2 is
    Generic (
        -- TCAM2 item width in bits
        DATA_WIDTH         : integer := 36;

        -- TCAM2 storage capacity
        --     for XILINX (7SERIES, ULTRASCALE) optimal is a multiple of 2*L*(2^RS), where L is number of LUTRAMs in each SLICEM
        --     for INTEL (ARRIA10, STRATIX10) optimal is a multiple of 16*(2^RS), if memory fragmentation is not enabled, otherwise a multiple of 32*(2^RS)
        ITEMS              : integer := 16;

        -- TCAM2 resources saving
        --     higher level of resources saving means fewer FPGA resources involved and faster item write but slower matching
        --     item write speed is 2^(6-RS) cycles for XILINX and 2^(5-RS)+1 cycles for INTEL FPGAs
        --     maximum level of resources saving is 6 for XILINX and 5 for INTEL FPGAs
        --     matching speed corresponds to 2^RS cycles
        RESOURCES_SAVING   : integer := 0;

        -- set as true if item write should have higher priority when requested in the same cycle as match
        -- TCAM2 read has lower priority than write
        WRITE_BEFORE_MATCH : boolean := true;

        -- set as true to enable read from TCAM2 by adding extra WRITE_DATA and WRITE_MASK storage
        READ_FROM_TCAM     : boolean := true;

        -- set as true to enable output registers for READ INTERFACE
        --     READ_FROM_TCAM must be set as true
        --     otherwise (false) READ_DATA and READ_MASK are ready in the next clock cycle after request
        OUTPUT_READ_REGS   : boolean := true;

        -- If true, writing a masked bit (mask=0) has two different meanings:
        --    If the bit is 0, then it is don't care
        --    But if the bit is 1, then it is UNMATCHABLE!
        USE_UNMATCHABLE    : boolean := false;

        -- set as true to use the entire Intel MLAB data width (20 instead of 16), but TCAM rows are addressed discontinuously (rows 21-32 are unused)
        -- set as true to use the entire Xilinx SLICEM data width (14 instead of 8 on ULTRASCALE, 6 instead of 4), but TCAM rows are addressed discontinuously
        USE_FRAGMENTED_MEM : boolean := false;

        -- FPGA device
        --    available are "7SERIES", "ULTRASCALE", "ARRIA10", "STRATIX10", "AGILEX"
        DEVICE             : string := "ULTRASCALE"
    );
    Port (
        -- CLOCK AND RESET
        CLK            : in  std_logic;
        RST            : in  std_logic;

        -- READ INTERFACE (READ_FROM_TCAM must be set as true)
        READ_ADDR      : in  std_logic_vector(max(1,log2(ITEMS))-1 downto 0);
        READ_EN        : in  std_logic;
        READ_RDY       : out std_logic;
        READ_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        READ_MASK      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        READ_DATA_VLD  : out std_logic;

        -- WRITE INTERFACE
        WRITE_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        WRITE_MASK     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        WRITE_ADDR     : in  std_logic_vector(max(1,log2(ITEMS))-1 downto 0);
        WRITE_EN       : in  std_logic;
        WRITE_RDY      : out std_logic;

        -- MATCH INTERFACE
        MATCH_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        MATCH_EN       : in  std_logic;
        MATCH_RDY      : out std_logic;
        -- MATCH_OUT INTERFACE (Output match latency is 3 cycles)
        MATCH_OUT_HIT  : out std_logic;
        MATCH_OUT_ADDR : out std_logic_vector(ITEMS-1 downto 0);
        MATCH_OUT_VLD  : out std_logic
    );
end entity;

-- =====================================================================
--                       Architecture declaration
-- =====================================================================
architecture FULL of TCAM2 is

    -- Manufacturer of FPGA device
    constant IS_XILINX           : boolean := (DEVICE = "7SERIES" or DEVICE = "ULTRASCALE");
    constant IS_INTEL            : boolean := (DEVICE = "ARRIA10" or DEVICE = "STRATIX10" or DEVICE = "AGILEX");

    -- Optimal parameters by FPGA device
    constant INTEL_DATA_WIDTH    : integer := tsel(USE_FRAGMENTED_MEM, 20, 16);
    constant XILINX_DATA_WIDTH    : integer := tsel(DEVICE = "ULTRASCALE", tsel(USE_FRAGMENTED_MEM, 14, 8), tsel(USE_FRAGMENTED_MEM, 6, 4));
    constant MEMORY_ADDR_WIDTH   : integer := 5;
    constant MEMORY_DATA_WIDTH   : integer := tsel(IS_XILINX, XILINX_DATA_WIDTH, INTEL_DATA_WIDTH);
    constant ALIGNED_DATA_WIDTH  : integer := 2**log2(MEMORY_DATA_WIDTH);

    -- Setting TCAM2 resources parameters
    constant CELL_WIDTH          : integer := MEMORY_ADDR_WIDTH - RESOURCES_SAVING;
    constant CELL_HEIGHT         : integer := MEMORY_DATA_WIDTH * (2**RESOURCES_SAVING);
    constant ALIGNED_CELL_HEIGHT : integer := ALIGNED_DATA_WIDTH * (2**RESOURCES_SAVING);
    constant CELL_HEIGHT_RATIO   : integer := CELL_HEIGHT/MEMORY_DATA_WIDTH;
    constant COLUMNS             : integer := div_roundup(DATA_WIDTH, CELL_WIDTH);
    constant ROWS                : integer := div_roundup(ITEMS, ALIGNED_CELL_HEIGHT);

    -- --------------------------------------------------------------------------
    --  I/O data signals
    -- --------------------------------------------------------------------------

    -- Input registers
    signal input_m_data_reg          : std_logic_vector(MATCH_DATA'range);
    signal input_wr_data_reg         : std_logic_vector(WRITE_DATA'range);
    signal input_wr_mask_reg         : std_logic_vector(WRITE_MASK'range);
    signal input_wr_addr_reg         : std_logic_vector(WRITE_ADDR'range);

    -- Input registers augmented
    signal input_m_data_reg_aug      : std_logic_vector(COLUMNS*CELL_WIDTH-1 downto 0);
    signal input_wr_data_reg_aug     : std_logic_vector(COLUMNS*CELL_WIDTH-1 downto 0) := (others => '0');
    signal input_wr_mask_reg_aug     : std_logic_vector(COLUMNS*CELL_WIDTH-1 downto 0) := (others => '0');
    signal input_wr_addr_reg_aug     : std_logic_vector(log2(ROWS*ALIGNED_CELL_HEIGHT)-1 downto 0) := (others => '0');

    -- Input registers augmented arrays
    signal input_m_data_reg_aug_arr  : slv_array_t(COLUMNS-1 downto 0)(CELL_WIDTH-1 downto 0);
    signal input_wr_data_reg_aug_arr : slv_array_t(COLUMNS-1 downto 0)(CELL_WIDTH-1 downto 0);
    signal input_wr_mask_reg_aug_arr : slv_array_t(COLUMNS-1 downto 0)(CELL_WIDTH-1 downto 0);

    -- Working indicator
    signal input_tcam_idle           : std_logic;

    -- --------------------------------------------------------------------------
    --  Memory signals
    -- --------------------------------------------------------------------------

    -- memory address signal (match or write)
    signal mem_addr_arr      : slv_array_t(COLUMNS-1 downto 0)(MEMORY_ADDR_WIDTH-1 downto 0);

    -- memory match signals
    signal mem_match_data    : slv_array_t(COLUMNS-1 downto 0)(MEMORY_ADDR_WIDTH-1 downto 0);
    signal mem_match_en      : std_logic;
    signal mem_match_en_reg  : std_logic;

    -- write registers
    signal mem_wr_addr_reg   : std_logic_vector(MEMORY_ADDR_WIDTH-1 downto 0);
    signal mem_wr_data_reg   : std_logic_vector(COLUMNS-1 downto 0);
    signal mem_wr_bit_en_reg : std_logic_vector(MEMORY_DATA_WIDTH-1 downto 0);
    signal mem_wr_en_reg     : std_logic_vector(ROWS-1 downto 0);

    -- intel block write
    signal mem_wr_data_block : slv_array_2d_t(COLUMNS-1 downto 0)(ROWS-1 downto 0)(MEMORY_DATA_WIDTH-1 downto 0);

    -- match vector
    signal mem_match_vector  : slv_array_2d_t(COLUMNS-1 downto 0)(ROWS-1 downto 0)(MEMORY_DATA_WIDTH-1 downto 0);

    -- match carry
    signal mem_match_carry   : slv_array_2d_t(COLUMNS   downto 0)(ROWS-1 downto 0)(MEMORY_DATA_WIDTH-1 downto 0);

    -- output after matching process
    signal mem_match_out     : slv_array_t(ROWS-1 downto 0)(MEMORY_DATA_WIDTH-1 downto 0);

    -- --------------------------------------------------------------------------
    --  Read logic signals
    -- --------------------------------------------------------------------------

    -- control signals
    signal rd_en         : std_logic;

    -- --------------------------------------------------------------------------
    --  Write logic signals
    -- --------------------------------------------------------------------------

    -- control signals
    signal wr_en         : std_logic;
    signal wr_en_reg     : std_logic;
    signal wr_rdy        : std_logic;

    -- write counter
    signal wr_cnt        : std_logic_vector(CELL_WIDTH-1 downto 0);
    signal wr_cnt_busy   : std_logic;
    signal wr_cnt_last   : std_logic;
    signal wr_cnt_en     : std_logic;

    -- masked signals
    signal masked_cnt    : slv_array_t(COLUMNS-1 downto 0)(CELL_WIDTH-1 downto 0);
    signal masked_data   : slv_array_t(COLUMNS-1 downto 0)(CELL_WIDTH-1 downto 0);

    -- cell height address when resources saving is applied
    signal mem_sf_addr   : std_logic_vector(max(1,log2(CELL_HEIGHT_RATIO))-1 downto 0);

    -- memory write signals
    signal mem_wr_addr   : std_logic_vector(MEMORY_ADDR_WIDTH-1 downto 0);
    signal mem_wr_data   : std_logic_vector(COLUMNS-1 downto 0);
    signal mem_wr_bit_en : std_logic_vector(ALIGNED_DATA_WIDTH-1 downto 0);
    signal mem_wr_en     : std_logic_vector(ROWS-1 downto 0);

    -- --------------------------------------------------------------------------
    --  Match logic signals
    -- --------------------------------------------------------------------------

    -- control signals
    signal m_en              : std_logic;
    signal m_en_reg          : std_logic;
    signal m_rdy             : std_logic;

    -- cell height address counter
    signal sf_cnt            : std_logic_vector(max(1,log2(CELL_HEIGHT_RATIO))-1 downto 0);
    signal sf_cnt_reg        : std_logic_vector(max(1,log2(CELL_HEIGHT_RATIO))-1 downto 0);
    signal sf_cnt_busy       : std_logic;
    signal sf_cnt_last       : std_logic;
    signal sf_cnt_last_reg   : std_logic;
    signal sf_cnt_en         : std_logic;
    signal sf_cnt_en_reg     : std_logic;

    -- output match register write enable
    signal m_aug_reg_we      : std_logic_vector(CELL_HEIGHT_RATIO-1 downto 0);

    -- output match vector register
    signal m_aug_reg         : slv_array_2d_t(ROWS-1 downto 0)(CELL_HEIGHT_RATIO-1 downto 0)(ALIGNED_DATA_WIDTH-1 downto 0);

    -- fit output match
    signal m_aug             : std_logic_vector(ROWS*ALIGNED_CELL_HEIGHT-1 downto 0);

begin

    assert (IS_XILINX or IS_INTEL)
        report "TCAM2 only supports XILINX or INTEL FPGAs!"
        severity failure;

    -- tcam waits for match or write
    input_tcam_idle <= m_rdy and wr_rdy;

    -- WRITE_BEFORE_MATCH logic
    write_first_g : if WRITE_BEFORE_MATCH generate
        wr_en     <= WRITE_EN and input_tcam_idle;
        m_en      <= MATCH_EN and input_tcam_idle and not WRITE_EN;
        WRITE_RDY <= input_tcam_idle;
        MATCH_RDY <= input_tcam_idle and not WRITE_EN;
    end generate;

    match_first_g : if not WRITE_BEFORE_MATCH generate
        m_en      <= MATCH_EN and input_tcam_idle;
        wr_en     <= WRITE_EN and input_tcam_idle and not MATCH_EN;
        MATCH_RDY <= input_tcam_idle;
        WRITE_RDY <= input_tcam_idle and not MATCH_EN;
    end generate;

    -- --------------------------------------------------------------------------
    --  Memory element
    -- --------------------------------------------------------------------------

    -- memory address
    mem_addr_g : for c in 0 to COLUMNS-1 generate
        mem_addr_arr(c) <= mem_match_data(c) when (mem_match_en = '1') else mem_wr_addr;
    end generate;

    -- match enable register
    mem_match_en_reg_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                mem_match_en_reg <= '0';
            else
                mem_match_en_reg <= mem_match_en;
            end if;
        end if;
    end process;

    -- match carry initialization
    mem_match_carry(0) <= (others => (others => mem_match_en_reg));

    -- MLAB write registers
    mem_wr_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            mem_wr_addr_reg   <= mem_wr_addr;
            mem_wr_data_reg   <= mem_wr_data;
            mem_wr_bit_en_reg <= mem_wr_bit_en(mem_wr_bit_en_reg'range);
            mem_wr_en_reg     <= mem_wr_en;
        end if;
    end process;

    -- memory element generate
    mem_rows_g : for r in 0 to ROWS-1 generate
        mem_colums_g : for c in 0 to COLUMNS-1 generate

            memory_xilinx_g : if IS_XILINX generate
                -- write data block (backup other records and add new)
                mem_wr_data_block(c)(r) <= (mem_match_vector(c)(r) and not mem_wr_bit_en_reg) or ((MEMORY_DATA_WIDTH-1 downto 0 => mem_wr_data_reg(c)) and mem_wr_bit_en_reg);

                -- Xilinx Single Port RAM
                sp_distmem_i : entity work.GEN_LUTRAM
                generic map (
                    DATA_WIDTH         => MEMORY_DATA_WIDTH,
                    ITEMS              => 2**MEMORY_ADDR_WIDTH,
                    RD_PORTS           => 1,
                    RD_LATENCY         => 1,
                    WRITE_USE_RD_ADDR0 => False,
                    MLAB_CONSTR_RDW_DC => False,
                    DEVICE             => DEVICE
                )
                port map (
                    CLK        => CLK,
                    WR_EN      => mem_wr_en_reg(r),
                    WR_ADDR    => mem_wr_addr_reg,
                    WR_DATA    => mem_wr_data_block(c)(r),
                    RD_ADDR    => mem_addr_arr(c),
                    RD_DATA    => mem_match_vector(c)(r)
                );
            end generate;

            storage_intel_g : if IS_INTEL generate
                -- write data block (backup other records and add new)
                mem_wr_data_block(c)(r) <= (mem_match_vector(c)(r) and not mem_wr_bit_en_reg) or ((MEMORY_DATA_WIDTH-1 downto 0 => mem_wr_data_reg(c)) and mem_wr_bit_en_reg);

                -- INTEL MLAB simple dual port RAM
                sdp_mlab_ram_i : entity work.GEN_LUTRAM
                generic map (
                    DATA_WIDTH         => MEMORY_DATA_WIDTH,
                    ITEMS              => 2**MEMORY_ADDR_WIDTH,
                    RD_PORTS           => 1,
                    RD_LATENCY         => 1,
                    WRITE_USE_RD_ADDR0 => False,
                    MLAB_CONSTR_RDW_DC => True,
                    DEVICE             => DEVICE
                )
                port map (
                    CLK     => CLK,
                    WR_EN   => mem_wr_en_reg(r),
                    WR_ADDR => mem_wr_addr_reg,
                    WR_DATA => mem_wr_data_block(c)(r),
                    RD_ADDR => mem_addr_arr(c),
                    RD_DATA => mem_match_vector(c)(r)
                );
            end generate;

            -- propagating match
            mem_match_carry(c+1)(r) <= mem_match_carry(c)(r) and mem_match_vector(c)(r);

        end generate;
    end generate;

    -- result of match propagation
    mem_match_out <= mem_match_carry(COLUMNS);

    -- additional WRITE_DATA and WRITE_MASK storage when READ_FROM_TCAM = true
    data_and_mask_storage_g : if READ_FROM_TCAM generate

        rd_en    <= READ_EN and not WRITE_EN;
        READ_RDY <= not WRITE_EN;

        -- WRITE_DATA storage
        write_data_storage_i : entity work.SDP_BRAM_BEHAV
        generic map (
            DATA_WIDTH  => DATA_WIDTH,
            ITEMS       => ITEMS,
            OUTPUT_REG  => OUTPUT_READ_REGS
        )
        port map (
            WR_CLK      => CLK,
            WR_EN       => WRITE_EN,
            WR_ADDR     => WRITE_ADDR,
            WR_DIN      => WRITE_DATA,

            RD_CLK      => CLK,
            RD_RST      => RST,
            RD_CE       => '1',
            RD_REG_CE   => '1',
            RD_EN       => rd_en,
            RD_ADDR     => READ_ADDR,
            RD_DOUT     => READ_DATA,
            RD_DOUT_VLD => READ_DATA_VLD
        );

        -- WRITE_MASK storage
        write_mask_storage_i : entity work.SDP_BRAM_BEHAV
        generic map (
            DATA_WIDTH  => DATA_WIDTH,
            ITEMS       => ITEMS,
            OUTPUT_REG  => OUTPUT_READ_REGS
        )
        port map (
            WR_CLK      => CLK,
            WR_EN       => WRITE_EN,
            WR_ADDR     => WRITE_ADDR,
            WR_DIN      => WRITE_MASK,

            RD_CLK      => CLK,
            RD_RST      => RST,
            RD_CE       => '1',
            RD_REG_CE   => '1',
            RD_EN       => rd_en,
            RD_ADDR     => READ_ADDR,
            RD_DOUT     => READ_MASK,
            RD_DOUT_VLD => open
        );

    end generate;

    no_data_and_mask_storage_g : if not READ_FROM_TCAM generate
        READ_RDY      <= '0';
        READ_DATA_VLD <= '0';
        READ_DATA     <= (others => '0');
        READ_MASK     <= (others => '0');
    end generate;

    -- --------------------------------------------------------------------------
    --  Write logic
    -- --------------------------------------------------------------------------

    -- write inputs registers
    write_reg_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                wr_en_reg <= '0';
            else
                wr_en_reg <= wr_en;
            end if;
            if (wr_en = '1') then
                input_wr_data_reg <= WRITE_DATA;
                input_wr_mask_reg <= WRITE_MASK;
                input_wr_addr_reg <= WRITE_ADDR;
            end if;
        end if;
    end process;

    -- write signals registers padding
    input_wr_data_reg_aug(input_wr_data_reg'range) <= input_wr_data_reg;
    input_wr_mask_reg_aug(input_wr_mask_reg'range) <= input_wr_mask_reg;
    input_wr_addr_reg_aug(input_wr_addr_reg'range) <= input_wr_addr_reg;
    -- write data and mask registers arrays
    input_wr_data_reg_aug_arr <= slv_array_deser(input_wr_data_reg_aug,COLUMNS);
    input_wr_mask_reg_aug_arr <= slv_array_deser(input_wr_mask_reg_aug,COLUMNS);

    -- write counter
    wr_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                wr_cnt <= (others => '0');
            elsif (wr_cnt_en = '1') then
                wr_cnt <= std_logic_vector(unsigned(wr_cnt) + 1);
            end if;
        end if;
    end process;
    wr_cnt_busy <= or wr_cnt;
    wr_cnt_last <= and wr_cnt;
    wr_cnt_en   <= wr_en_reg or wr_cnt_busy;

    -- write ready logic
    xilinx_wr_rdy_g : if MEMORY_DATA_WIDTH = 1 generate
        wr_rdy <= (not wr_cnt_busy or wr_cnt_last) and not wr_en_reg;
    end generate;
    intel_wr_rdy_g : if MEMORY_DATA_WIDTH > 1 generate
        wr_rdy <= not wr_cnt_busy and not wr_en_reg;
    end generate;

    -- memory row address we decoder
    row_we_g : if ROWS > 1 generate
        row_we_decoder_i : entity work.dec1fn_enable
        generic map (
            ITEMS => ROWS
        )
        port map (
            ADDR   => input_wr_addr_reg_aug(input_wr_addr_reg_aug'high downto log2(ALIGNED_CELL_HEIGHT)),
            ENABLE => wr_cnt_en,
            DO     => mem_wr_en
        );
    end generate;
    fake_row_we_g : if ROWS = 1 generate
        mem_wr_en(0) <= wr_cnt_en;
    end generate;

    -- cell height address
    mem_sf_addr_g : if CELL_HEIGHT_RATIO > 1 generate
        mem_sf_addr <= input_wr_addr_reg_aug(log2(ALIGNED_CELL_HEIGHT)-1 downto log2(ALIGNED_DATA_WIDTH));
    end generate;
    fake_mem_sf_addr_g : if CELL_HEIGHT_RATIO = 1 generate
        mem_sf_addr(0) <= '0';
    end generate;

    -- memory element bit enable
    bit_en_g : if ALIGNED_DATA_WIDTH > 1 generate
        bit_en_decoder_i : entity work.dec1fn
        generic map (
            ITEMS => ALIGNED_DATA_WIDTH
        )
        port map (
            ADDR => input_wr_addr_reg_aug(log2(ALIGNED_DATA_WIDTH)-1 downto 0),
            DO   => mem_wr_bit_en
        );
    end generate;
    fake_bit_en_g : if ALIGNED_DATA_WIDTH = 1 generate
        mem_wr_bit_en(0) <= '1';
    end generate;

    -- memory element write address
    mem_wr_addr_g : if CELL_WIDTH < MEMORY_ADDR_WIDTH generate
        mem_wr_addr(MEMORY_ADDR_WIDTH-1 downto CELL_WIDTH) <= mem_sf_addr;
    end generate;
    mem_wr_addr(CELL_WIDTH-1 downto 0) <= wr_cnt;

    -- memory element write data
    mem_wr_data_g : for i in 0 to COLUMNS-1 generate
        masked_cnt(i)  <= wr_cnt and input_wr_mask_reg_aug_arr(i);
        use_unmatchable_g: if USE_UNMATCHABLE = true generate
            masked_data(i) <= input_wr_data_reg_aug_arr(i);
        else generate
            masked_data(i) <= input_wr_data_reg_aug_arr(i) and input_wr_mask_reg_aug_arr(i);
        end generate;
        mem_wr_data(i) <= '1' when (masked_cnt(i) = masked_data(i)) else '0';
    end generate;

    -- --------------------------------------------------------------------------
    --  Match logic
    -- --------------------------------------------------------------------------

    -- match inputs registers
    match_regs_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (RST = '1') then
                m_en_reg <= '0';
            else
                m_en_reg <= m_en;
            end if;
            if (m_en = '1') then
                input_m_data_reg <= MATCH_DATA;
            end if;
        end if;
    end process;

    -- match data register padding
    input_m_data_reg_aug     <= (input_m_data_reg'range => input_m_data_reg, others => '0');
    -- match data register array
    input_m_data_reg_aug_arr <= slv_array_deser(input_m_data_reg_aug,COLUMNS);

    -- cell height address counter
    sf_cnt_g : if CELL_HEIGHT_RATIO > 1 generate
        sf_cnt_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    sf_cnt <= (others => '0');
                elsif (sf_cnt_en = '1') then
                    sf_cnt <= std_logic_vector(unsigned(sf_cnt) + 1);
                end if;
            end if;
        end process;

        sf_cnt_busy <= or sf_cnt;
        sf_cnt_last <= and sf_cnt;
        sf_cnt_en   <= m_en_reg or sf_cnt_busy;
        m_rdy       <= (not sf_cnt_busy or sf_cnt_last) and not m_en_reg;

        sf_cnt_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                sf_cnt_reg    <= sf_cnt;
                sf_cnt_en_reg <= sf_cnt_en;
            end if;
        end process;
    end generate;

    -- fake counter when resource saving is not enabled (RS = 0)
    fake_sf_cnt_g : if CELL_HEIGHT_RATIO = 1 generate
        sf_cnt_reg    <= (others => '0');
        sf_cnt_busy   <= '0';
        sf_cnt_last   <= m_en_reg;
        sf_cnt_en     <= m_en_reg;
        sf_cnt_en_reg <= '1';
        m_rdy         <= '1';
    end generate;

    -- sf_cnt_last register
    sf_cnt_last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                sf_cnt_last_reg <= '0';
            else
                sf_cnt_last_reg <= sf_cnt_last;
            end if;
        end if;
    end process;

    -- data for matching in memory
    mem_match_data_g : for i in 0 to COLUMNS-1 generate
        mem_match_data(i)(CELL_WIDTH-1 downto 0) <= input_m_data_reg_aug_arr(i);
        mem_sf_addr_g : if CELL_HEIGHT_RATIO > 1 generate
            mem_match_data(i)(MEMORY_ADDR_WIDTH-1 downto CELL_WIDTH) <= sf_cnt;
        end generate;
    end generate;

    -- memory match enable
    mem_match_en <= sf_cnt_en;

    -- output match register write enable decoder
    m_aug_reg_we_dec_i : entity work.dec1fn_enable
    generic map (
        ITEMS => CELL_HEIGHT_RATIO
    )
    port map (
        ADDR   => sf_cnt_reg,
        ENABLE => sf_cnt_en_reg,
        DO     => m_aug_reg_we
    );

    -- output match vector register
    match_bits_reg_g : for i in 0 to ROWS-1 generate
        match_words_reg_g : for j in 0 to CELL_HEIGHT_RATIO-1 generate
            m_aug_reg_p : process (CLK)
            begin
                if rising_edge(CLK) then
                    if (m_aug_reg_we(j) = '1') then
                        m_aug_reg(i)(j) <= (others=>'0');
                        m_aug_reg(i)(j)(mem_match_out(i)'range) <= mem_match_out(i);
                    end if;
                end if;
            end process;
        end generate;
    end generate;
    -- array conversion
    m_aug <= slv_array_2d_ser(m_aug_reg);

    -- output length fit
    MATCH_OUT_ADDR <= m_aug(MATCH_OUT_ADDR'range);

    -- match hit
    MATCH_OUT_HIT <= or MATCH_OUT_ADDR;

    -- output match valid register
    match_out_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                MATCH_OUT_VLD <= '0';
            else
                MATCH_OUT_VLD <= sf_cnt_last_reg;
            end if;
        end if;
    end process;

end architecture;
