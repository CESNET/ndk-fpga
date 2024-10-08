-- amm_gen.vhd: Component for creating AMM commands via MI interface
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- MI ADDRESS SPACE --
-- ----------------------------------
-- ctrl         BASE
--              0. in  - memory write    (writes to external memory with rising edge)
--              1. in  - memory read     (reads from external memory with rising edge)
--              2. out - buff valid
--              3. out - amm ready
-- ----------------------------------
-- address      BASE + 0x04
--              address for read/write (indexed by AMM words in burst)
--              also used for burst index when writing / reading to buffer
-- ----------------------------------
-- slice        BASE + 0x08
--              slice address in selected AMM word
--              used when writing / reading to buffer
-- ----------------------------------
-- r/w data     BASE + 0x0C
--              one silce of the AMM word for manual r/w burst
-- ----------------------------------
-- burst cnt    BASE + 0x10
-- ----------------------------------

entity AMM_GEN is
generic (
    -- MI bus --
    MI_DATA_WIDTH           : integer := 32;
    MI_ADDR_WIDTH           : integer := 32;

    -- Avalon bus --
    AMM_DATA_WIDTH          : integer := 512;
    AMM_ADDR_WIDTH          : integer := 26;
    AMM_BURST_COUNT_WIDTH   : integer := 7;

    MAX_BURST_CNT           : integer := 2 ** AMM_BURST_COUNT_WIDTH - 1;
    INIT_BURST_CNT          : integer := 4;

    -- Others --
    MI_ADDR_BASE            : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0) := (others => '0');
    MI_ADDR_USED_BITS       : integer := MI_ADDR_WIDTH;     -- Number of used MI addr LSB bits
    DEVICE                  : string
);
port(
    -- Main --
    CLK                     : in std_logic;
    RST                     : in std_logic;

    -- MI bus master interface --
    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    MI_RD                   : in  std_logic;
    MI_WR                   : in  std_logic;
    MI_ARDY                 : out std_logic;
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_DRDY                 : out std_logic;

    -- Avalon slave interface --
    AMM_READY               : in   std_logic;
    AMM_READ                : out  std_logic;
    AMM_WRITE               : out  std_logic;
    AMM_ADDRESS             : out  std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);
    AMM_READ_DATA           : in   std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_WRITE_DATA          : out  std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);
    AMM_BURST_COUNT         : out  std_logic_vector(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    AMM_READ_DATA_VALID     : in   std_logic
);
end entity;

architecture FULL of AMM_GEN is

    type AMM_STATES_T is (
        INIT,
        WRITE,
        READ,
        READ_WAIT,
        WRITE_DONE,
        READ_DONE
    );

    type MI_STATES_T is (
        MI_READY,

        -- MI WR to buffer
        MI_DEC_SLICE,       -- mi_to_buff_en_delayed
        MI_BUFF_WR,

        -- MI RD from buffer
        MI_BUFF_RD,
        MI_BUFF_RD_REG,     -- DP_BRAM_OUT_REG
        MI_SEL_SLICE,       -- sel_slice_delayed
        MI_SLICE_REG,       -- curr_slice_delayed
        MI_SET_DRDY
    );

    -- Number of MI bus words inside AMM bus word
    constant SLICES_CNT             : integer := AMM_DATA_WIDTH / MI_DATA_WIDTH;

    constant BURST_BITS             : integer := log2(MAX_BURST_CNT);
    constant SLICES_BITS            : integer := max(log2(SLICES_CNT), 1);

    constant MI_ADDR_CUTOFF         : integer := log2(MI_DATA_WIDTH / 8);

    -- in
    constant MEM_WR_BIT             : integer := 0;
    constant MEM_RD_BIT             : integer := 1;
    -- out
    constant BUFF_VLD_BIT           : integer := 2;
    constant AMM_READY_BIT          : integer := 3;

    constant CTRL_LAST_IN_BIT       : integer := MEM_RD_BIT;
    constant CTRL_LAST_OUT_BIT      : integer := AMM_READY_BIT;

    -- AMM pipe
    constant AMM_READ_DELAY         : integer := 1;
    constant AMM_WRITE_DELAY        : integer := 2; -- Because of out reg in DP BRAM

    constant WR_MAX_TICKS           : integer := 2;
    constant RD_MAX_TICKS           : integer := 5;

    constant WORD_FROM_MI_DELAY     : integer := 0;
    constant BUFF_WR_DELAY          : integer := 1;
    constant MI_DRDY_DELAY          : integer := 4;

    pure function id_to_addr_f (addr : integer)
    return std_logic_vector is
        constant mi_addr_base_int   : integer := to_integer(unsigned(MI_ADDR_BASE(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF)));
    begin
        return std_logic_vector(to_unsigned(mi_addr_base_int + addr, MI_ADDR_USED_BITS - MI_ADDR_CUTOFF));
    end function;

    constant CTRL_REG_ADDR          : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF) := id_to_addr_f(0);
    constant ADDR_REG_ADDR          : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF) := id_to_addr_f(1);
    constant SLICE_REG_ADDR         : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF) := id_to_addr_f(2);
    constant DATA_REG_ADDR          : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF) := id_to_addr_f(3);
    constant BURST_REG_ADDR         : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF) := id_to_addr_f(4);

    -- ----------------------------------------------------------------------- --

    -- CONTROL --
    signal curr_amm_state           : AMM_STATES_T;
    signal next_amm_state           : AMM_STATES_T;

    signal curr_mi_state            : MI_STATES_T;
    signal next_mi_state            : MI_STATES_T;

    -- MI BUS --
    -- Selelct signals
    signal mi_addr_sliced           : std_logic_vector(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF);

    -- Slice from MI addr register
    signal sel_burst                : std_logic_vector(BURST_BITS - 1 downto 0);
    signal sel_slice                : std_logic_vector(SLICES_BITS - 1 downto 0);
    signal sel_slice_delayed        : std_logic_vector(SLICES_BITS - 1 downto 0);
    signal curr_word_from_mi        : std_logic;
    signal buff_wr                  : std_logic;

    signal mi_to_buff_en            : std_logic_vector(SLICES_CNT - 1 downto 0);
    signal mi_to_buff_en_delayed    : std_logic_vector(SLICES_CNT - 1 downto 0);
    signal mi_drdy_intern           : std_logic;

    -- '1' when last buffer request was write else read
    signal buff_mi_wr_start         : std_logic;
    signal buff_mi_rd_start         : std_logic;
    signal buff_mi_wr_runing        : std_logic;
    signal buff_mi_rd_runing        : std_logic;
    signal buff_mi_wr_en            : std_logic;
    signal buff_mi_rd_en            : std_logic;
    signal buff_mi_wr_end           : std_logic;
    signal buff_mi_rd_end           : std_logic;
    signal buff_mi_wr_ticks         : integer range 0 to WR_MAX_TICKS - 1;
    signal buff_mi_rd_ticks         : integer range 0 to RD_MAX_TICKS - 1;

    -- Registers
    signal ctrl_reg                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal addr_reg                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal slice_reg                : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal data_reg                 : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);

    signal curr_slice               : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal curr_slice_delayed       : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal word_to_buff             : slv_array_t(0 to SLICES_CNT - 1)(MI_DATA_WIDTH - 1 downto 0);
    signal word_from_buff           : slv_array_t(0 to SLICES_CNT - 1)(MI_DATA_WIDTH - 1 downto 0);
    signal word_from_buff_slv       : std_logic_vector(AMM_DATA_WIDTH - 1 downto 0);

    signal bits_edge_trig           : std_logic_vector(CTRL_LAST_IN_BIT downto 0);
    signal bits_no_trig             : std_logic_vector(CTRL_LAST_IN_BIT downto 0);

    -- AMM BUS --
    signal amm_addr_reg             : std_logic_vector(AMM_ADDR_WIDTH - 1 downto 0);

    signal amm_write_en             : std_logic;
    signal amm_read_en              : std_logic;

    signal amm_write_delayed        : std_logic_vector(AMM_WRITE_DELAY downto 0);
    signal amm_read_delayed         : std_logic_vector(AMM_READ_DELAY downto 0);

    signal target_burst_cnt         : std_logic_vector(BURST_BITS - 1 downto 0);
    signal target_burst_cnt_lim     : std_logic_vector(BURST_BITS - 1 downto 0);    -- Indexed from 0 to match curr_burst
    signal curr_burst_cnt           : std_logic_vector(BURST_BITS - 1 downto 0);
    -- To restore burst cnt when amm_ready occurs
    signal burst_cnt_delayed        : slv_array_t(0 to AMM_WRITE_DELAY - 1)(BURST_BITS - 1 downto 0);
    signal burst_en                 : std_logic;
    signal burst_en_req             : std_logic;
    signal burst_rst                : std_logic;
    signal burst_rst_req            : std_logic;
    signal burst_done               : std_logic;
    signal burst_done_delayed       : std_logic_vector(AMM_WRITE_DELAY downto 0);

    signal wait_for_read_data       : std_logic;
    signal receive_data             : std_logic;

    signal buff_vld                 : std_logic;
    signal buff_set_vld             : std_logic;
    signal buff_clr_vld             : std_logic;

begin
    assert (AMM_DATA_WIDTH mod MI_DATA_WIDTH = 0)
        report "AMM_DATA_WIDTH must be multiple of MI_DATA_WIDTH!"
        severity failure;

    -------------------------
    -- Component instances --
    -------------------------
    edge_trig_g : for i in 0 to CTRL_LAST_IN_BIT generate
        edge_trig_i : entity work.EDGE_DETECT
        port map (
            CLK         => CLK,
            DI          => bits_no_trig(i),
            EDGE        => bits_edge_trig(i)
        );
    end generate;

    buff_i : entity work.DP_BRAM_BEHAV
    generic map (
        DATA_WIDTH      => AMM_DATA_WIDTH,
        ITEMS           => MAX_BURST_CNT,
        OUTPUT_REG      => True        -- Data will be delayed by 1 clk cycle
    )
    port map (
        RST             => RST,
        CLK             => CLK,

        -- Interface A - for AMM
        PIPE_ENA        => '1',
        REA             => not receive_data,
        WEA             => receive_data,
        ADDRA           => curr_burst_cnt,
        DIA             => AMM_READ_DATA,
        DOA             => AMM_WRITE_DATA,

        -- Interface B - for MI
        PIPE_ENB        => '1',
        REB             => not buff_wr,
        WEB             => buff_wr,
        ADDRB           => sel_burst,
        DIB             => slv_array_ser(word_to_buff),
        DOB             => word_from_buff_slv
    );

    ----------------
    -- Wire logic --
    ----------------
    -- MI BUS --
    mi_addr_sliced          <= MI_ADDR(MI_ADDR_USED_BITS - 1 downto MI_ADDR_CUTOFF);

    -- CTRL reg
    ctrl_reg(BUFF_VLD_BIT)  <= buff_vld;
    ctrl_reg(AMM_READY_BIT) <= AMM_READY;
    bits_no_trig            <=
        ctrl_reg(MEM_RD_BIT)    &
        ctrl_reg(MEM_WR_BIT);

    -- Parsing addr reg
    sel_slice               <= slice_reg(SLICES_BITS - 1 downto 0);
    sel_burst               <= addr_reg(BURST_BITS - 1 downto 0);

    word_from_buff          <= slv_array_to_deser(word_from_buff_slv, SLICES_CNT);
    word_to_buff_g : for i in 0 to SLICES_CNT - 1 generate
        word_to_buff(i)     <= data_reg     when (mi_to_buff_en_delayed(i)) else
                               word_from_buff(i);
        mi_to_buff_en(i)    <= '1'          when (curr_word_from_mi = '1' and to_integer(unsigned(sel_slice)) = i) else
                               '0';
    end generate;

    curr_slice              <= word_from_buff(to_integer(unsigned(sel_slice_delayed)));

    buff_mi_wr_start        <= '1' when (mi_addr_sliced = DATA_REG_ADDR and MI_WR = '1') else
                               '0';
    buff_mi_rd_start        <= '1' when (mi_addr_sliced = DATA_REG_ADDR and MI_RD = '1') else
                               '0';
    buff_mi_wr_end          <= '1' when (buff_mi_wr_ticks = WR_MAX_TICKS - 1) else
                               '0';
    buff_mi_rd_end          <= '1' when (buff_mi_rd_ticks = RD_MAX_TICKS - 1) else
                               '0';
    buff_mi_wr_runing        <= buff_mi_wr_en or buff_mi_wr_start;
    buff_mi_rd_runing        <= buff_mi_rd_en or buff_mi_rd_start;

    -- AMM BUS --
    amm_write_delayed(0)    <= amm_write_en and AMM_READY;
    amm_read_delayed(0)     <= amm_read_en;

    AMM_WRITE               <= amm_write_delayed(AMM_WRITE_DELAY) and amm_write_en and AMM_READY;
    AMM_READ                <= amm_read_delayed(AMM_READ_DELAY) and amm_read_en;
    AMM_ADDRESS             <= amm_addr_reg;
    AMM_BURST_COUNT         <= target_burst_cnt;

    receive_data            <= AMM_READ_DATA_VALID and wait_for_read_data;
    burst_en                <= (burst_en_req and AMM_READY) or receive_data;
    burst_rst               <= RST or (burst_en and burst_done) or burst_rst_req;
    burst_done              <= '1' when (curr_burst_cnt = target_burst_cnt_lim and (receive_data = '1' or (wait_for_read_data = '0' and AMM_READY = '1'))) else
                               '0';
    burst_done_delayed(0)   <= burst_done;
    target_burst_cnt_lim    <= std_logic_vector(to_unsigned(to_integer(unsigned(target_burst_cnt)) - 1, target_burst_cnt_lim'length));
    buff_clr_vld            <= buff_wr or bits_edge_trig(MEM_RD_BIT);

    ---------------
    -- Registers --
    ---------------

    -- OUT
    mi_out_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            -- Case can't be used because of warning:
            -- "case choice should be a locally static expression"
            -- (constants are inicialized with function that adds amm_gen base addr)
            if (mi_addr_sliced = CTRL_REG_ADDR)     then
                MI_DRD <= ctrl_reg;
            elsif (mi_addr_sliced = ADDR_REG_ADDR)  then
                MI_DRD <= addr_reg;
            elsif (mi_addr_sliced = SLICE_REG_ADDR)  then
                MI_DRD <= slice_reg;
            elsif (mi_addr_sliced = DATA_REG_ADDR)  then
                MI_DRD <= curr_slice_delayed;
            elsif (mi_addr_sliced = BURST_REG_ADDR) then
                MI_DRD <= (MI_DATA_WIDTH - 1 downto BURST_BITS => '0') & target_burst_cnt;
            else
                MI_DRD <= X"DEADBEEF";
            end if;
        end if;
    end process;

    -- IN
    mi_in_addr_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                ctrl_reg(CTRL_LAST_IN_BIT downto 0)                         <= (others => '0');
                ctrl_reg(MI_DATA_WIDTH - 1 downto CTRL_LAST_OUT_BIT + 1)    <= (others => '0');
                addr_reg                                                    <= (others => '0');
                slice_reg                                                   <= (others => '0');
                data_reg                                                    <= (others => '0');
                target_burst_cnt                                            <= std_logic_vector(to_unsigned(INIT_BURST_CNT, target_burst_cnt'length));
            elsif (MI_WR = '1') then
                if (mi_addr_sliced = CTRL_REG_ADDR)     then
                    ctrl_reg(CTRL_LAST_IN_BIT downto 0)  <= MI_DWR(CTRL_LAST_IN_BIT downto 0);
                elsif (mi_addr_sliced = ADDR_REG_ADDR)  then
                    addr_reg                             <= MI_DWR;
                elsif (mi_addr_sliced = SLICE_REG_ADDR)  then
                    slice_reg                            <= MI_DWR;
                elsif (mi_addr_sliced = DATA_REG_ADDR)  then
                    data_reg                             <= MI_DWR;
                elsif (mi_addr_sliced = BURST_REG_ADDR) then
                    target_burst_cnt                     <= MI_DWR(BURST_BITS - 1 downto 0);
                end if;
            end if;
        end if;
    end process;

    buff_vld_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                buff_vld    <= '0';
            elsif(buff_clr_vld = '1') then
                buff_vld    <= '0';
            elsif(buff_set_vld = '1') then
                buff_vld    <= '1';
            end if;
        end if;
    end process;

    amm_addr_reg_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                amm_addr_reg   <= (others => '0');
            elsif (bits_edge_trig(MEM_WR_BIT) = '1' or bits_edge_trig(MEM_RD_BIT) = '1') then
                -- Save addr from mi bus
                amm_addr_reg   <= addr_reg(AMM_ADDR_WIDTH - 1 downto 0);
            end if;
        end if;
    end process;

    burst_cnt_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (burst_rst = '1') then
                curr_burst_cnt  <= (others => '0');
            elsif (AMM_READY = '0' and curr_amm_state = WRITE) then
                -- To resend words that wouldn't be send due to BRAM 2 clk delay
                curr_burst_cnt <= burst_cnt_delayed(AMM_WRITE_DELAY - 1);
            elsif(burst_en = '1') then
                curr_burst_cnt <= std_logic_vector(unsigned(curr_burst_cnt) + 1);
            end if;
        end if;
    end process;

    burst_cnt_delayed_g : for i in 0 to AMM_WRITE_DELAY - 1 generate
        burst_cnt_delayed_0_g : if (i = 0) generate
            burst_cnt_delayed_p : process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (RST = '1') then
                        burst_cnt_delayed(i) <= (others => '0');
                    else
                        if (AMM_READY = '0') then
                            burst_cnt_delayed(i) <= burst_cnt_delayed(AMM_WRITE_DELAY - 1);
                        else
                            burst_cnt_delayed(i) <= curr_burst_cnt;
                        end if;
                    end if;
                end if;
            end process;
        end generate;

        burst_cnt_delayed_not_0_g : if (i /= 0) generate
            burst_cnt_delayed_p : process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (RST = '1') then
                        burst_cnt_delayed(i) <= (others => '0');
                    else
                        if (AMM_READY = '0') then
                            burst_cnt_delayed(i) <= burst_cnt_delayed(AMM_WRITE_DELAY - 1);
                        else
                            burst_cnt_delayed(i) <= burst_cnt_delayed(i - 1);
                        end if;
                    end if;
                end if;
            end process;
        end generate;
    end generate;

    buff_mi_wr_ticks_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1' or buff_mi_wr_end = '1') then
                buff_mi_wr_ticks  <= 0;
            elsif(buff_mi_wr_runing = '1') then
                buff_mi_wr_ticks  <= buff_mi_wr_ticks + 1;
            end if;
        end if;
    end process;

    buff_mi_rd_ticks_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1' or buff_mi_rd_end = '1') then
                buff_mi_rd_ticks  <= 0;
            elsif(buff_mi_rd_runing = '1') then
                buff_mi_rd_ticks  <= buff_mi_rd_ticks + 1;
            end if;
        end if;
    end process;

    buff_mi_wr_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                buff_mi_wr_en      <= '0';
            elsif (buff_mi_wr_start = '1') then
                buff_mi_wr_en      <= '1';
            elsif (buff_mi_wr_end = '1') then
                buff_mi_wr_en      <= '0';
            end if;
        end if;
    end process;

    buff_mi_rd_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                buff_mi_rd_en      <= '0';
            elsif (buff_mi_rd_start = '1') then
                buff_mi_rd_en      <= '1';
            elsif (buff_mi_rd_end = '1') then
                buff_mi_rd_en      <= '0';
            end if;
        end if;
    end process;

    sel_slice_delayed_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            sel_slice_delayed   <= sel_slice;
        end if;
    end process;

    burst_done_delayed_g : for i in 0 to AMM_WRITE_DELAY - 1 generate
        amm_write_delayed_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (AMM_READY = '0') then
                    burst_done_delayed(i + 1) <= '0';
                else
                    burst_done_delayed(i + 1) <= burst_done_delayed(i);
                end if;
            end if;
        end process;
    end generate;

    -- AMM read / write delayed
    amm_write_delayed_g : for i in 0 to AMM_WRITE_DELAY - 1 generate
        amm_write_delayed_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (AMM_READY = '0') then
                    amm_write_delayed(i + 1) <= '0';
                else
                    amm_write_delayed(i + 1) <= amm_write_delayed(i);
                end if;
            end if;
        end process;
    end generate;

    amm_read_delayed_g : for i in 0 to AMM_READ_DELAY - 1 generate
        amm_read_delayed_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                amm_read_delayed(i + 1) <= amm_read_delayed(i);
            end if;
        end process;
    end generate;

    mi_to_buff_en_delayed_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            mi_to_buff_en_delayed   <= mi_to_buff_en;
        end if;
    end process;

    curr_slice_delayed_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            curr_slice_delayed  <= curr_slice;
        end if;
    end process;

    -----------------------
    -- AMM STATE MACHINE --
    -----------------------

    -- next state logic
    state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                curr_amm_state <= INIT;
            else
                curr_amm_state <= next_amm_state;
            end if;
        end if;
    end process;

    -- output logic
    process (all)
    begin
        amm_write_en        <= '0';
        amm_read_en         <= '0';
        burst_en_req        <= '0';
        wait_for_read_data  <= '0';
        buff_set_vld        <= '0';
        burst_rst_req       <= '0';

        case curr_amm_state is

            when INIT =>
                if (bits_edge_trig(MEM_WR_BIT) = '1') then
                    burst_rst_req           <= '1';
                elsif (bits_edge_trig(MEM_RD_BIT) = '1') then
                    burst_rst_req           <= '1';
                end if;

            when WRITE =>
                amm_write_en            <= '1';
                burst_en_req            <= '1';

            when READ =>
                wait_for_read_data      <= '1';
                if (AMM_READY = '1') then
                    amm_read_en         <= '1';
                end if;

            when READ_WAIT =>
                wait_for_read_data      <= '1';

            when WRITE_DONE =>

            when READ_DONE =>
                buff_set_vld            <= '1';

            when others =>
                null;

        end case;
    end process;

    -- next state logic
    process (all)
    begin
        next_amm_state <= curr_amm_state;

        case curr_amm_state is

            when INIT =>
                if (bits_edge_trig(MEM_WR_BIT) = '1') then
                    next_amm_state      <= WRITE;
                elsif (bits_edge_trig(MEM_RD_BIT) = '1') then
                    next_amm_state      <= READ;
                end if;

            when WRITE =>
                if (burst_done_delayed(AMM_WRITE_DELAY) = '1' and AMM_WRITE = '1') then
                    next_amm_state      <=  WRITE_DONE;
                end if;

            when READ =>
                if (AMM_READY = '1' and AMM_READ = '1') then
                    next_amm_state      <=  READ_WAIT;
                end if;

            when READ_WAIT =>
                if (burst_done = '1')  then
                    next_amm_state      <=  READ_DONE;
                end if;

            when WRITE_DONE =>
                next_amm_state          <= INIT;

            when READ_DONE =>
                next_amm_state          <= INIT;

            when others => null;

        end case;
    end process;

    ----------------------
    -- MI STATE MACHINE --
    ----------------------

    -- next state logic
    mi_state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                curr_mi_state <= MI_READY;
            else
                curr_mi_state <= next_mi_state;
            end if;
        end if;
    end process;

    -- output logic
    process (all)
    begin
        MI_ARDY             <= '0';
        MI_DRDY             <= '0';
        curr_word_from_mi   <= '0';
        buff_wr             <= '0';

        case curr_mi_state is

            when MI_READY       =>
                MI_ARDY             <= '1';

                if (mi_addr_sliced /= DATA_REG_ADDR and MI_RD = '1') then
                    MI_DRDY     <= '1';
                end if;

            when MI_DEC_SLICE   =>
                curr_word_from_mi   <= '1';

            when MI_BUFF_WR     =>
                buff_wr             <= '1';

            when MI_BUFF_RD     =>

            when MI_BUFF_RD_REG =>

            when MI_SEL_SLICE   =>

            when MI_SLICE_REG   =>

            when MI_SET_DRDY    =>
                MI_DRDY             <= '1';

            when others         =>
                null;

        end case;
    end process;

    -- next state logic
    process (all)
    begin
        next_mi_state <= curr_mi_state;

        case curr_mi_state is

            when MI_READY       =>
                if      (mi_addr_sliced = DATA_REG_ADDR and MI_WR = '1') then
                    next_mi_state       <= MI_DEC_SLICE;
                elsif   (mi_addr_sliced = DATA_REG_ADDR and MI_RD = '1') then
                    next_mi_state       <= MI_BUFF_RD;
                end if;

            when MI_DEC_SLICE   =>
                next_mi_state           <= MI_BUFF_WR;

            when MI_BUFF_WR     =>
                next_mi_state           <= MI_READY;

            when MI_BUFF_RD     =>
                next_mi_state           <= MI_BUFF_RD_REG;

            when MI_BUFF_RD_REG =>
                next_mi_state           <= MI_SEL_SLICE;

            when MI_SEL_SLICE   =>
                next_mi_state           <= MI_SLICE_REG;

            when MI_SLICE_REG   =>
                next_mi_state           <= MI_SET_DRDY;

            when MI_SET_DRDY    =>
                next_mi_state           <= MI_READY;

            when others         =>
                null;

        end case;
    end process;


end architecture;
