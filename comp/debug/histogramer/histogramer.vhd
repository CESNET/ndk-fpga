-- histogramer.vhd: Component for creating histograms
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- .. vhdl:autogenerics:: HISTOGRAMER
entity HISTOGRAMER is
generic (
    -- Width of input values
    INPUT_WIDTH             : integer;
    -- Width of one histogram box (number of values in a given range)
    -- Box probably overflowed when its value equals 2**BOX_WIDTH-1
    BOX_WIDTH               : integer;
    -- Number of histogram boxes (defines histogram precision)
    BOX_CNT                 : integer;
    -- Defines if read or write should occur when both happen at the same time
    READ_PRIOR              : boolean := false;
    -- Defines if read should erase box content
    CLEAR_BY_READ           : boolean := true;
    -- Defines if BRAM should be sequentially erased after reset
    CLEAR_BY_RST            : boolean := true
);
port(
    CLK                     : in  std_logic;
    RST                     : in  std_logic;
    RST_DONE                : out std_logic;

    -- =======================================================================
    --  Input interface
    -- =======================================================================

    INPUT_VLD               : in  std_logic;
    INPUT                   : in  std_logic_vector(INPUT_WIDTH - 1 downto 0);

    -- =======================================================================
    --  Read interface
    -- =======================================================================

    -- Request to read box specified by READ_ADDR
    READ_REQ                : in  std_logic;
    -- Box adress
    READ_ADDR               : in  std_logic_vector(log2(BOX_CNT) - 1 downto 0);
    -- The requested box is valid
    READ_BOX_VLD            : out std_logic;
    -- Requested box
    READ_BOX                : out std_logic_vector(BOX_WIDTH - 1 downto 0)
);
end entity;

-- =========================================================================

architecture FULL of HISTOGRAMER is
    ---------------
    -- Constants --
    ---------------

    -- Should equal BRAM latency
    constant PIPELINE_ITEMS     : integer := 2;

    constant ADDR_WIDTH         : integer := log2(BOX_CNT);
    constant ADDR_MAX           : std_logic_vector(ADDR_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(BOX_CNT - 1, ADDR_WIDTH));

    constant MAX_BOX_VAL        : std_logic_vector(BOX_WIDTH - 1 downto 0) := (others => '1');
    constant MAX_BOX_VAL_LONG   : unsigned := unsigned(MAX_BOX_VAL);

    -------------
    -- Signals --
    -------------

    signal input_write          : std_logic;
    signal input_read           : std_logic;

    signal pipeline_box         : slv_array_t(PIPELINE_ITEMS downto 0)(BOX_WIDTH - 1 downto 0);
    signal pipeline_addr        : slv_array_t(PIPELINE_ITEMS downto 0)(ADDR_WIDTH - 1 downto 0);
    signal pipeline_vld         : std_logic_vector(PIPELINE_ITEMS downto 0);
    signal pipeline_read        : std_logic_vector(PIPELINE_ITEMS downto 0);

    signal input_pipeline_box   : std_logic_vector(BOX_WIDTH - 1 downto 0);

    signal last_pipeline_box    : std_logic_vector(BOX_WIDTH - 1 downto 0);
    signal last_pipeline_addr   : std_logic_vector(ADDR_WIDTH - 1 downto 0);
    signal last_pipeline_vld    : std_logic;
    signal last_pipeline_read   : std_logic;

    -- For overflow detection
    signal pipeline_box_incr    : slv_array_t(PIPELINE_ITEMS downto 0)(BOX_WIDTH - 1 downto 0);
    signal pipeline_box_res_tmp : std_logic_vector(BOX_WIDTH - 1 downto 0);
    signal pipeline_box_res     : std_logic_vector(BOX_WIDTH - 1 downto 0);

    signal clear_result         : std_logic;

    signal colision_index       : std_logic_vector(PIPELINE_ITEMS - 1 downto 0);
    signal colision             : std_logic;
    signal colision_last        : std_logic;

    signal feadback_to_first    : std_logic;

    signal bram_read            : std_logic;
    signal bram_read_data_vld   : std_logic;
    signal bram_read_data       : std_logic_vector(BOX_WIDTH - 1 downto 0);
    signal bram_read_addr       : std_logic_vector(ADDR_WIDTH - 1 downto 0);

    signal bram_write           : std_logic;
    signal bram_write_data      : std_logic_vector(BOX_WIDTH - 1 downto 0);
    signal bram_write_addr      : std_logic_vector(ADDR_WIDTH - 1 downto 0);

    signal bram_clear_done      : std_logic;
    signal bram_clear_addr      : std_logic_vector(ADDR_WIDTH - 1 downto 0);

    function add_handle_overflow(a : std_logic_vector ; b : std_logic_vector) return std_logic_vector is
        variable w      : integer := a'length;
        variable tmp    : unsigned(w downto 0);
        variable res    : std_logic_vector(w - 1 downto 0);
    begin
        tmp     := unsigned('0' & a) + unsigned('0' & b);
        res     := std_logic_vector(tmp(BOX_WIDTH - 1 downto 0)) when (tmp(w) = '0') else
                   (others => '1');
        return res;
    end function;

begin
    -------------------------
    -- Component instances --
    -------------------------

    data_i : entity work.DP_BRAM_BEHAV
    generic map (
        DATA_WIDTH  => BOX_WIDTH,
        ITEMS       => BOX_CNT
    )
    port map (
        CLK         => CLK,
        RST         => RST,

        PIPE_ENA    => '1',
        REA         => bram_read,
        WEA         => '0',
        ADDRA       => bram_read_addr,
        DIA         => (others => '0'),
        DOA         => bram_read_data,
        DOA_DV      => bram_read_data_vld,

        PIPE_ENB    => '1',
        REB         => '0',
        WEB         => bram_write,
        ADDRB       => bram_write_addr,
        DIB         => bram_write_data
    );

    -------------------------
    -- Combinational logic --
    -------------------------

    -- Input management --
    ----------------------

    -- Selection between read/write
    read_prior_g : if (READ_PRIOR = true) generate
        input_write     <= INPUT_VLD and not READ_REQ and bram_clear_done;
        input_read      <= READ_REQ and bram_clear_done;
    end generate;
    write_prior_g : if (READ_PRIOR = false) generate
        input_write     <= INPUT_VLD and bram_clear_done;
        input_read      <= READ_REQ and not INPUT_VLD and bram_clear_done;
    end generate;

    -- Command selection
    pipeline_vld(0)     <= (input_write or input_read) and (not colision or feadback_to_first);
    pipeline_read(0)    <= input_read and (not colision or feadback_to_first);
    -- Select histogram box (adress) by cutting value
    pipeline_addr(0)    <= INPUT(INPUT_WIDTH - 1 downto INPUT_WIDTH - ADDR_WIDTH) when (input_write = '1') else
                           READ_ADDR;
    -- Box initial value
    input_pipeline_box  <= std_logic_vector(to_unsigned(1, BOX_WIDTH)) when (input_write = '1') else
                           (others => '0');
    -- Colision between last and the first box => join to the first box
    -- Join to the last box would need adder and ovf detection before bram write port
    -- which would have bad timing
    -- Adding register would need next colision detection and the same problem would occur again
    pipeline_box(0)     <= input_pipeline_box when (feadback_to_first = '0') else
                           add_handle_overflow(input_pipeline_box, last_pipeline_box);

    -- Colision detection --
    ------------------------

    pipeline_colision_g : for i in PIPELINE_ITEMS - 1 downto 0 generate
        colision_index(i) <= '1' when (pipeline_addr(0) = pipeline_addr(i + 1) and pipeline_vld(i + 1) = '1' and (INPUT_VLD = '1' or READ_REQ = '1')) else
                             '0';
    end generate;
    colision_last       <= '1' when (pipeline_addr(0) = last_pipeline_addr and last_pipeline_vld = '1' and (INPUT_VLD = '1' or READ_REQ = '1')) else
                           '0';
    colision            <= (or colision_index); -- or colision_last;

    feadback_to_first   <= colision_last and not clear_result;

    -- BRAM management --
    ---------------------

    bram_read           <= pipeline_vld(0) or pipeline_read(0);
    bram_read_addr      <= pipeline_addr(0);

    bram_write          <= (last_pipeline_vld and not feadback_to_first) when (bram_clear_done = '1') else
                           '1';
    bram_write_addr     <= last_pipeline_addr when (bram_clear_done = '1') else
                           bram_clear_addr;
    bram_write_data     <= (others => '0') when (clear_result = '1' or bram_clear_done = '0') else
                           last_pipeline_box;

    -- Clear by read --
    -------------------

    -- Clear by read detection
    clear_by_read_g : if (CLEAR_BY_READ = true) generate
        clear_result    <= last_pipeline_read or (colision_last and input_read);
    end generate;
    dont_clear_by_read_g : if (CLEAR_BY_READ = false) generate
        clear_result    <= '0';
    end generate;

    -- Pipeline management --
    -------------------------

    -- Increment with overflow detection
    pipeline_incr_g : for i in PIPELINE_ITEMS downto 0 generate
        pipeline_box_incr(i) <= add_handle_overflow(pipeline_box(i), std_logic_vector(to_unsigned(1, pipeline_box(0)'length)));
    end generate;

    -- Result creation (BRAM read data + pipeline box + handle last colision + handle overflow)
    pipeline_box_res_tmp<= pipeline_box(PIPELINE_ITEMS) when (colision_index(PIPELINE_ITEMS - 1) = '0' or input_read = '1') else
                           pipeline_box_incr(PIPELINE_ITEMS);
    pipeline_box_res    <= add_handle_overflow(pipeline_box_res_tmp, bram_read_data);

    -- Output --
    ------------

    READ_BOX            <= last_pipeline_box;
    READ_BOX_VLD        <= ((last_pipeline_read and last_pipeline_vld) or (colision_last and input_read)) and not feadback_to_first;
    RST_DONE            <= bram_clear_done;


    ---------------
    -- Registers --
    ---------------

    -- Pipeline --
    --------------

    pipeline_g : for i in PIPELINE_ITEMS downto 1 generate
        pipeline_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    pipeline_vld(i)     <= '0';
                    pipeline_read(i)    <= '0';
                    pipeline_addr(i)    <= (others => '0');
                else
                    pipeline_vld(i)     <= pipeline_vld(i - 1);
                    pipeline_read(i)    <= pipeline_read(i - 1);
                    pipeline_addr(i)    <= pipeline_addr(i - 1);

                    -- Collision detected
                    if (i > 1 and colision_index(i - 2) = '1') then
                        if (input_read = '1') then
                            pipeline_read(i)    <= '1';
                            pipeline_box(i)     <= pipeline_box(i - 1);
                        else
                            pipeline_box(i)     <= pipeline_box_incr(i - 1);
                        end if;
                    else
                        pipeline_box(i) <= pipeline_box(i - 1);
                    end if;
                end if;
            end if;
        end process;
    end generate;

    last_pipeline_box_data_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            last_pipeline_addr  <= pipeline_addr(PIPELINE_ITEMS);
            last_pipeline_box   <= pipeline_box_res;
            last_pipeline_read  <= pipeline_read(PIPELINE_ITEMS);

            if (colision_index(PIPELINE_ITEMS - 1) = '1' and input_read = '1') then
                last_pipeline_read  <= '1';
            end if;
        end if;
    end process;

    last_pipeline_box_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                last_pipeline_vld   <= '0';
            else
                last_pipeline_vld   <= pipeline_vld(PIPELINE_ITEMS);
            end if;
        end if;
    end process;

    -- Clear by RST --
    ------------------

    clear_addr_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1' or bram_clear_done = '1') then
                bram_clear_addr     <= (others => '0');
            else
                bram_clear_addr     <= std_logic_vector(unsigned(bram_clear_addr) + 1);
            end if;
        end if;
    end process;

    clear_by_rst_g : if (CLEAR_BY_RST = true) generate
        clear_done_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    bram_clear_done     <= '0';
                elsif (bram_clear_addr = ADDR_MAX) then
                    bram_clear_done     <= '1';
                end if;
            end if;
        end process;
    end generate;
    dont_clear_by_rst_g : if (CLEAR_BY_RST = false) generate
        bram_clear_done <= '1';
    end generate;

end architecture;
