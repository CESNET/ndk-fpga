-- data_loggoer.vhd: Component for managing and loging statistics
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


-- MI address space:
-- 0x0000: CTRL REG
--         0: sw rst
--         1: rst done
-- 0x0004: STATS REG
-- 0x0008: INDEX REG
-- 0x000C: SLICE REG
-- 0x0010: HIST REG
-- 0x0014: VALUE REG

-- STATS REG selects statistic
-- (index given by INDEX REG)
-- 0:           CNTER_CNT
-- 1:           VALUE_CNT
-- 2:           MI_DATA_WIDTH
-- 3:           CTRLO_WIDTH
-- 4:           CTRLI_WIDTH
-- 5:           CNTER_WIDTH
-- 6:           VALUE_WIDTH     (i)
-- 7:           VALUE_ENs       (i)
--              0:  min_en
--              1:  max_en
--              2:  sum_en
--              3:  hist_en
-- 8:           SUM_EXTRA_WIDTH (i)
-- 9:           HIST_BOX_CNT    (i)
-- 10:          HIST_BOX_WIDTH  (i)
-- -------------
-- 11:          ctrlo
-- 12:          ctrli
-- 13:          cnter val       (i)
--              (CNTER_CNT + VALUE_CNT counters)
-- 14:          value min       (i)
-- 15:          value max       (i)
-- 16:          value sum       (i)
-- 17:          value hist      (i)

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- .. vhdl:autogenerics:: DATA_LOGGER
entity DATA_LOGGER is
generic (
    MI_DATA_WIDTH           : integer := 32;
    MI_ADDR_WIDTH           : integer := 32;

    CNTER_CNT               : integer := 0;
    VALUE_CNT               : integer := 0;

    CTRLO_WIDTH             : integer := 0;
    CTRLI_WIDTH             : integer := 0;
    CNTER_WIDTH             : integer := MI_DATA_WIDTH;
    VALUE_WIDTH             : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 0);

    MIN_EN                  : b_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => true);
    MAX_EN                  : b_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => true);
    SUM_EN                  : b_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => true);
    HIST_EN                 : b_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => false);

    -- How many bits add to VALUE_WIDTH to form SUM register width
    SUM_EXTRA_WIDTH         : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 16);
    HIST_BOX_CNT            : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 0);
    HIST_BOX_WIDTH          : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 0);
    -- Default value of control output instrface
    CTRLO_DEFAULT           : std_logic_vector(max(CTRLO_WIDTH - 1, 0) downto 0) := (others => '0')
);
port(
    CLK                     : in  std_logic;
    RST                     : in  std_logic;
    RST_DONE                : out std_logic;
    -- SW reset was performed on data_logger
    SW_RST                  : out std_logic;

    -- =======================================================================
    --  CONTROL INTERFACE
    -- =======================================================================

    CTRLO                   : out std_logic_vector(max(CTRLO_WIDTH - 1, 0) downto 0) := (others => '0');
    CTRLI                   : in  std_logic_vector(max(CTRLI_WIDTH - 1, 0) downto 0) := (others => '0');

    -- =======================================================================
    --  COUNTERS INTERFACE
    -- =======================================================================

    CNTERS_INCR             : in  std_logic_vector(max(CNTER_CNT - 1, 0) downto 0) := (others => '0');
    -- Cnt is incremented in the TMP reg and is submited only when SUMBIT = 1
    CNTERS_SUBMIT           : in  std_logic_vector(max(CNTER_CNT - 1, 0) downto 0) := (others => '1');
    CNTERS_DIFF             : in  slv_array_t(max(CNTER_CNT - 1, 0) downto 0)(CNTER_WIDTH - 1 downto 0) := (others => (std_logic_vector(to_unsigned(1, CNTER_WIDTH))));

    -- =======================================================================
    --  VALUE INTERFACE
    -- =======================================================================

    VALUES_VLD              : in  std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');
    VALUES                  : in  std_logic_vector(max(sum(VALUE_WIDTH) - 1, 0) downto 0) := (others => '0');

    -- ==========================
    -- MI bus interface
    -- ==========================

    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    MI_RD                   : in  std_logic;
    MI_WR                   : in  std_logic;
    MI_ARDY                 : out std_logic;
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH - 1 downto 0) := (others => '0');
    MI_DRDY                 : out std_logic
);
end entity;

-- =========================================================================

architecture FULL of DATA_LOGGER is
    ---------------
    -- Funcitons --
    ---------------

    function lsb (index : integer; widths : i_array_t := VALUE_WIDTH) return integer is
        variable l    : integer := 0;
    begin
        if (index > 0) then
            for i in 0 to index - 1 loop
                l := l + widths(i);
            end loop;
        end if;

        return l;
    end function;

    function msb (index : integer; widths : i_array_t := VALUE_WIDTH) return integer is
    begin
        return lsb(index, widths) + widths(index) - 1;
    end function;

    function slice_lsb (index : integer; w : integer := MI_DATA_WIDTH) return integer is
    begin
        return index * w;
    end function;

    function slice_msb (index : integer; w : integer := MI_DATA_WIDTH) return integer is
        variable l    : integer := slice_lsb(index, w);
    begin
        return l + w - 1;
    end function;

    impure function log2_arr (arr : i_array_t) return i_array_t is
        variable logs  : i_array_t(arr'high downto arr'low) := arr;
    begin
        if (arr'length > 0) then
            for i in arr'low to arr'high loop
                logs(i) := log2(logs(i));
            end loop;
        end if;

        return logs;
    end function;

    function add_arr (arr_0 : i_array_t; arr_1 : i_array_t) return i_array_t is
        variable tmp  : i_array_t(arr_0'high downto arr_0'low) := arr_0;
    begin
        if (arr_0'length > 0) then
            for i in arr_0'low to arr_0'high loop
                tmp(i) := arr_0(i) + arr_1(i);
            end loop;
        end if;

        return tmp;
    end function;

    function bool_to_logic(x : boolean) return std_logic is
    begin
        if x then
            return('1');
        else
            return('0');
        end if;
    end function;


    ---------------
    -- Constants --
    ---------------

    -- Each value has its own cnter
    constant ALL_CNTER_CNT      : integer := CNTER_CNT + VALUE_CNT;

    constant CNTER_MAX          : std_logic_vector(CNTER_WIDTH - 1 downto 0) := (others => '1');
    constant MIN_INIT           : std_logic_vector(max(sum(VALUE_WIDTH) - 1, 0) downto 0) := (others => '1');
    constant MAX_INIT           : std_logic_vector(max(sum(VALUE_WIDTH) - 1, 0) downto 0) := (others => '0');

    constant SUM_WIDTH          : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := add_arr(VALUE_WIDTH, SUM_EXTRA_WIDTH);
    constant HIST_ADDR_WIDTH    : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := log2_arr(HIST_BOX_CNT);

    constant MI_ADDR_CUTOFF     : integer := 5;
    constant MI_CTRL_ADDR       : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0) := std_logic_vector(to_unsigned(0,  MI_ADDR_CUTOFF));
    constant MI_STATS_ADDR      : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0) := std_logic_vector(to_unsigned(4,  MI_ADDR_CUTOFF));
    constant MI_INDEX_ADDR      : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0) := std_logic_vector(to_unsigned(8,  MI_ADDR_CUTOFF));
    constant MI_SLICE_ADDR      : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0) := std_logic_vector(to_unsigned(12, MI_ADDR_CUTOFF));
    constant MI_HIST_ADDR       : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0) := std_logic_vector(to_unsigned(16, MI_ADDR_CUTOFF));
    constant MI_VALUE_ADDR      : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0) := std_logic_vector(to_unsigned(20, MI_ADDR_CUTOFF));

    constant CTRL_RST_BIT       : integer := 0;
    constant CTRL_RST_DONE_BIT  : integer := 1;

    constant STAT_CNT           : integer := 18;
    constant MI_READ_DELAY      : integer := 2;

    constant MAX_DATA_WIDTH_RAW : integer :=
        max(CTRLI_WIDTH,
        max(CTRLO_WIDTH,
        max(CNTER_WIDTH,
        max(max(VALUE_WIDTH),
        max(max(SUM_WIDTH), max(HIST_BOX_WIDTH))
    ))));
    constant MAX_DATA_WIDTH     : integer := div_roundup(MAX_DATA_WIDTH_RAW, MI_DATA_WIDTH) * MI_DATA_WIDTH;
    constant MI_SLICES          : integer := div_roundup(MAX_DATA_WIDTH, MI_DATA_WIDTH);

    constant MI_STAT_MAX        : std_logic_vector(MI_DATA_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(STAT_CNT,        MI_DATA_WIDTH));
    constant MI_CNTER_INDEX_MAX : std_logic_vector(MI_DATA_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(ALL_CNTER_CNT,   MI_DATA_WIDTH));
    constant MI_VALUE_INDEX_MAX : std_logic_vector(MI_DATA_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(VALUE_CNT,       MI_DATA_WIDTH));
    constant MI_SLICE_MAX       : std_logic_vector(MI_DATA_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(MI_SLICES,       MI_DATA_WIDTH));

    constant CTRLO_SLICE_CNT    : integer := div_roundup(CTRLO_WIDTH, MI_DATA_WIDTH);

    -------------
    -- Signals --
    -------------

    signal rst_intern           : std_logic;
    signal rst_done_intern      : std_logic;
    signal rst_done_vec         : std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');

    signal cnter_new            : slv_array_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(CNTER_WIDTH downto 0) := (others => (others => '0'));
    signal cnter_diff_intern    : slv_array_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(CNTER_WIDTH - 1 downto 0) := (others => (std_logic_vector(to_unsigned(1, CNTER_WIDTH))));

    signal ctrli_reg            : std_logic_vector(max(CTRLI_WIDTH - 1, 0) downto 0) := (others => '0');
    signal cnter_reg            : slv_array_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(CNTER_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal cnter_reg_tmp        : slv_array_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(CNTER_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal value_min_reg        : std_logic_vector(max(sum(VALUE_WIDTH) - 1, 0) downto 0) := (others => '0');
    signal value_max_reg        : std_logic_vector(max(sum(VALUE_WIDTH) - 1, 0) downto 0) := (others => '0');
    signal value_sum_reg        : std_logic_vector(max(sum(SUM_WIDTH) - 1, 0) downto 0) := (others => '0');
    signal value_sum_new        : std_logic_vector(max(sum(SUM_WIDTH) - 1, 0) downto 0) := (others => '0');

    signal hist_read_raw        : std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');
    signal hist_read            : std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');
    signal hist_read_vld        : std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');
    signal hist_read_vld_reg    : std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');
    signal hist_read_box        : std_logic_vector(max(sum(HIST_BOX_WIDTH) - 1, 0) downto 0) := (others => '0');
    signal hist_read_box_reg    : std_logic_vector(max(sum(HIST_BOX_WIDTH) - 1, 0) downto 0) := (others => '0');
    signal hist_read_addr       : std_logic_vector(max(sum(HIST_ADDR_WIDTH) - 1, 0) downto 0) := (others => '0');

    signal mi_ctrl_reg          : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_stats_reg         : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_index_reg         : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_slice_reg         : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_hist_reg          : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_stats_reg_i       : integer range 0 to MAX(STAT_CNT  - 1, 0);
    signal mi_cnter_index_reg_i : integer range 0 to MAX(ALL_CNTER_CNT - 1, 0);
    signal mi_value_index_reg_i : integer range 0 to MAX(VALUE_CNT - 1, 0);
    signal mi_slice_reg_i       : integer range 0 to MAX(MI_SLICES - 1, 0);

    signal value_width_slices   : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal value_ens_slices     : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal sum_extra_slices     : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal box_cnt_slices       : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal box_width_slices     : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));

    signal ctrlo_enlarge        : std_logic_vector(MAX_DATA_WIDTH - 1 downto 0) := (others => '0');
    signal ctrli_enlarge        : std_logic_vector(MAX_DATA_WIDTH - 1 downto 0) := (others => '0');
    signal ctrlo_slices         : slv_array_t(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal ctrli_slices         : slv_array_t(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));

    signal cnter_enlarge        : slv_array_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(MAX_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal cnter_slices         : slv_array_2d_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal cnter_slices_reg     : slv_array_2d_t(max(ALL_CNTER_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));

    signal value_min_enlarge    : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MAX_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal value_max_enlarge    : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MAX_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal value_sum_enlarge    : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MAX_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));
    signal value_hist_enlarge   : slv_array_t(max(VALUE_CNT - 1, 0) downto 0)(MAX_DATA_WIDTH - 1 downto 0) := (others => (others => '0'));

    signal value_min_slices     : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal value_max_slices     : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal value_sum_slices     : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal value_hist_slices    : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));

    signal value_min_slices_reg : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal value_max_slices_reg : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal value_sum_slices_reg : slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));
    signal value_hist_slices_reg: slv_array_2d_t(max(VALUE_CNT - 1, 0) downto 0)(MI_SLICES - 1 downto 0)(MI_DATA_WIDTH - 1 downto 0) := (others => (others => (others => '0')));

    signal sel_value_width_slice: std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_value_ens_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_sum_extra_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_box_cnt_slice    : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_box_width_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_ctrlo_slice      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_ctrli_slice      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_cnter_slice      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_value_min_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_value_max_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_value_sum_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_value_hist_slice : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);

    signal sel_reg_value_width_slice: std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_value_ens_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_sum_extra_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_box_cnt_slice    : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_box_width_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_ctrlo_slice      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_ctrli_slice      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_cnter_slice      : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_value_min_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_value_max_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_value_sum_slice  : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal sel_reg_value_hist_slice : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);

    signal mi_reading           : std_logic;

    signal mi_sel_stat          : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_sel_stat_vld      : std_logic;
    signal mi_read_delayed      : std_logic_vector(MI_READ_DELAY downto 0);
    signal hist_read_delayed    : std_logic_vector(MI_READ_DELAY downto 0);

    signal ctrlo_enlarge_reg    : std_logic_vector(max(CTRLO_SLICE_CNT * MI_DATA_WIDTH - 1, 0) downto 0);
    signal ctrlo_enlarge_default: std_logic_vector(max(CTRLO_SLICE_CNT * MI_DATA_WIDTH - 1, 0) downto 0);

    signal mi_addr_intern       : std_logic_vector(MI_ADDR_CUTOFF - 1 downto 0);

begin
    -------------------------
    -- Component instances --
    -------------------------

    hist_g : for i in 0 to VALUE_CNT - 1 generate
        hist_if_g : if (HIST_EN(i) = true) generate
            hist_i : entity work.HISTOGRAMER
            generic map(
                INPUT_WIDTH             => VALUE_WIDTH(i),
                BOX_WIDTH               => HIST_BOX_WIDTH(i),
                BOX_CNT                 => HIST_BOX_CNT(i)
                --READ_PRIOR              => READ_PRIOR
            )
            port map(
                CLK                     => CLK,
                RST                     => rst_intern,
                RST_DONE                => rst_done_vec(i),

                INPUT                   => VALUES(msb(i) downto lsb(i)),
                INPUT_VLD               => VALUES_VLD(i),

                READ_REQ                => hist_read(i),
                READ_ADDR               => hist_read_addr(msb(i, HIST_ADDR_WIDTH) downto lsb(i, HIST_ADDR_WIDTH)),
                READ_BOX_VLD            => hist_read_vld(i),
                READ_BOX                => hist_read_box(msb(i, HIST_BOX_WIDTH) downto lsb(i, HIST_BOX_WIDTH))
            );
        end generate;
        no_hist_g : if (HIST_EN(i) = false) generate
            rst_done_vec(i)     <= '1';
            hist_read_vld(i)    <= '1';
        end generate;
    end generate;

    -------------------------
    -- Combinational logic --
    -------------------------

    -- RST management --
    --------------------

    rst_intern  <= RST or mi_ctrl_reg(CTRL_RST_BIT);
    SW_RST      <= mi_ctrl_reg(CTRL_RST_BIT);

    rst_done_g : if (VALUE_CNT > 0) generate
        rst_done_intern <= and rst_done_vec;
    end generate;
    rst_done2_g : if (VALUE_CNT = 0) generate
        rst_done_intern <= '1';
    end generate;

    -- CTRLI/O management --
    ------------------------

    CTRLO   <= ctrlo_enlarge_reg(max(CTRLO_WIDTH - 1, 0) downto 0);
    ctrlo_enlarge_default(max(CTRLO_WIDTH - 1, 0) downto 0) <= CTRLO_DEFAULT;

    -- CNTER management --
    ----------------------

    cnter_diff_intern_g : if (CNTER_CNT > 0) generate
        cnter_diff_intern(CNTER_CNT - 1 downto 0) <= CNTERS_DIFF;
    end generate;

    value_cnter_g : if (VALUE_CNT > 0) generate
        cnter_reg_tmp(ALL_CNTER_CNT - 1 downto CNTER_CNT) <= cnter_reg(ALL_CNTER_CNT - 1 downto CNTER_CNT);
    end generate;

    -- New counter value (has one more bit to detect overflow)
    cnter_incr_g : for i in 0 to ALL_CNTER_CNT - 1 generate
        cnter_new(i)    <= std_logic_vector(
            unsigned('0' & cnter_reg_tmp(i)) +
            unsigned('0' & cnter_diff_intern(i))
        );
    end generate;

    -- VALUE maangement --
    ----------------------

    -- Calculate sum + overflow
    value_sum_new_g : for i in 0 to VALUE_CNT - 1 generate
        value_sum_new_if_g : if (SUM_EN(i) = true) generate
            value_sum_new(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH)) <=
                -- TODO overflow
                --(others => '1')
                --when (
                --    std_logic_vector(
                --        ('1' & unsigned(value_sum_reg(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH)))) +
                --        ('1' & unsigned(VALUES(msb(i) downto lsb(i))))
                --        ) > std_logic_vector(to_unsigned(max(2 ** SUM_WIDTH(i) - 1, 0), SUM_WIDTH(i) + 1))
                --) else
                std_logic_vector(unsigned(value_sum_reg(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH))) +
                    unsigned(VALUES(msb(i) downto lsb(i)))
                );
        end generate;
    end generate;

    -- MI bus --
    ------------

    MI_ARDY         <= RST_DONE and not mi_reading;
    mi_addr_intern  <= MI_ADDR(MI_ADDR_CUTOFF - 1 downto 0);

    mi_stats_reg_i          <= to_integer(unsigned(mi_stats_reg)) when (mi_stats_reg < MI_STAT_MAX) else
                               0;
    mi_cnter_index_reg_i    <= to_integer(unsigned(mi_index_reg)) when (mi_index_reg < MI_CNTER_INDEX_MAX) else
                               0;
    mi_value_index_reg_i    <= to_integer(unsigned(mi_index_reg)) when (mi_index_reg < MI_VALUE_INDEX_MAX) else
                               0;
    mi_slice_reg_i          <= to_integer(unsigned(mi_slice_reg)) when (mi_slice_reg < MI_SLICE_MAX) else
                               0;

    mi_sel_stat   <=
        std_logic_vector(to_unsigned(CNTER_CNT,     MI_DATA_WIDTH)) when (mi_stats_reg_i = 0 ) else
        std_logic_vector(to_unsigned(VALUE_CNT,     MI_DATA_WIDTH)) when (mi_stats_reg_i = 1 ) else
        std_logic_vector(to_unsigned(MI_DATA_WIDTH, MI_DATA_WIDTH)) when (mi_stats_reg_i = 2 ) else
        std_logic_vector(to_unsigned(CTRLO_WIDTH,   MI_DATA_WIDTH)) when (mi_stats_reg_i = 3 ) else
        std_logic_vector(to_unsigned(CTRLI_WIDTH,   MI_DATA_WIDTH)) when (mi_stats_reg_i = 4 ) else
        std_logic_vector(to_unsigned(CNTER_WIDTH,   MI_DATA_WIDTH)) when (mi_stats_reg_i = 5 ) else
        std_logic_vector(to_unsigned(CNTER_WIDTH,   MI_DATA_WIDTH)) when (mi_stats_reg_i = 5 ) else
        sel_reg_value_width_slice                                   when (mi_stats_reg_i = 6 ) else
        sel_reg_value_ens_slice                                     when (mi_stats_reg_i = 7 ) else
        sel_reg_sum_extra_slice                                     when (mi_stats_reg_i = 8 ) else
        sel_reg_box_cnt_slice                                       when (mi_stats_reg_i = 9 ) else
        sel_reg_box_width_slice                                     when (mi_stats_reg_i = 10) else
        sel_reg_ctrlo_slice                                         when (mi_stats_reg_i = 11) else
        sel_reg_ctrli_slice                                         when (mi_stats_reg_i = 12) else
        sel_reg_cnter_slice                                         when (mi_stats_reg_i = 13) else
        sel_reg_value_min_slice                                     when (mi_stats_reg_i = 14) else
        sel_reg_value_max_slice                                     when (mi_stats_reg_i = 15) else
        sel_reg_value_sum_slice                                     when (mi_stats_reg_i = 16) else
        sel_reg_value_hist_slice                                    when (mi_stats_reg_i = 17) else
        X"DEAD_BEAF";

    mi_sel_stat_vld  <=
        '1'                     when (mi_stats_reg_i = 0 ) else
        '1'                     when (mi_stats_reg_i = 1 ) else
        '1'                     when (mi_stats_reg_i = 2 ) else
        '1'                     when (mi_stats_reg_i = 3 ) else
        '1'                     when (mi_stats_reg_i = 4 ) else
        '1'                     when (mi_stats_reg_i = 5 ) else
        '1'                     when (mi_stats_reg_i = 5 ) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 6 ) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 7 ) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 8 ) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 9 ) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 10) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 11) else
        mi_read_delayed(1)      when (mi_stats_reg_i = 12) else
        mi_read_delayed(2)      when (mi_stats_reg_i = 13) else
        mi_read_delayed(2)      when (mi_stats_reg_i = 14) else
        mi_read_delayed(2)      when (mi_stats_reg_i = 15) else
        mi_read_delayed(2)      when (mi_stats_reg_i = 16) else
        hist_read_delayed(2)    when (mi_stats_reg_i = 17) else
        '1';

    mi_read_delayed(0)      <= MI_ARDY and MI_RD;
    hist_read_delayed(0)    <= hist_read_vld_reg(mi_value_index_reg_i) and not MI_ARDY;

    -- MI slices --
    ---------------

    -- Ctrl to MI slices
    ctrlo_enlarge(max(CTRLO_WIDTH - 1, 0) downto 0) <= CTRLO;
    ctrli_enlarge(max(CTRLI_WIDTH - 1, 0) downto 0) <= ctrli_reg;
    ctrl_slices_g : for i in 0 to MI_SLICES - 1 generate
        ctrlo_slices(i)     <= ctrlo_enlarge(slice_msb(i) downto slice_lsb(i));
        ctrli_slices(i)     <= ctrli_enlarge(slice_msb(i) downto slice_lsb(i));
    end generate;

    -- Cnter to slices
    cnter_slices_g : for i in 0 to ALL_CNTER_CNT - 1 generate
        cnter_enlarge(i)(CNTER_WIDTH - 1 downto 0)  <= cnter_reg(i);
        cnter_slices_2_g : for j in 0 to MI_SLICES - 1 generate
            cnter_slices(i)(j) <= cnter_enlarge(i)(slice_msb(j) downto slice_lsb(j));
        end generate;
    end generate;

    -- Values to slices
    value_slices_g : for i in 0 to VALUE_CNT - 1 generate
        value_width_slices(i)                               <= std_logic_vector(to_unsigned(VALUE_WIDTH(i),     MI_DATA_WIDTH));
        value_ens_slices(i)(4 - 1 downto 0)                 <=
            bool_to_logic(HIST_EN(i)) &
            bool_to_logic(SUM_EN(i))  &
            bool_to_logic(MAX_EN(i))  &
            bool_to_logic(MIN_EN(i));
        sum_extra_slices(i)                                 <= std_logic_vector(to_unsigned(SUM_EXTRA_WIDTH(i), MI_DATA_WIDTH));
        box_cnt_slices(i)                                   <= std_logic_vector(to_unsigned(HIST_BOX_CNT(i),    MI_DATA_WIDTH));
        box_width_slices(i)                                 <= std_logic_vector(to_unsigned(HIST_BOX_WIDTH(i),  MI_DATA_WIDTH));

        value_min_enlarge (i)(VALUE_WIDTH(i) - 1 downto 0)   <= value_min_reg(msb(i) downto lsb(i));
        value_max_enlarge (i)(VALUE_WIDTH(i) - 1 downto 0)   <= value_max_reg(msb(i) downto lsb(i));
        value_sum_enlarge (i)(SUM_WIDTH(i) - 1 downto 0)     <= value_sum_reg(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH));
        value_hist_enlarge(i)(HIST_BOX_WIDTH(i) - 1 downto 0)<= hist_read_box_reg(msb(i, HIST_BOX_WIDTH) downto lsb(i, HIST_BOX_WIDTH));

        valie_slices_2_g : for j in 0 to MI_SLICES - 1 generate
            value_min_slices(i)(j)  <= value_min_enlarge(i)(slice_msb(j) downto slice_lsb(j));
            value_max_slices(i)(j)  <= value_max_enlarge(i)(slice_msb(j) downto slice_lsb(j));
            value_sum_slices(i)(j)  <= value_sum_enlarge(i)(slice_msb(j) downto slice_lsb(j));
            value_hist_slices(i)(j) <= value_hist_enlarge(i)(slice_msb(j) downto slice_lsb(j));
        end generate;
    end generate;

    -- MI slice selection --
    ------------------------

    sel_value_width_slice   <= value_width_slices   (mi_value_index_reg_i);
    sel_value_ens_slice     <= value_ens_slices     (mi_value_index_reg_i);
    sel_sum_extra_slice     <= sum_extra_slices     (mi_value_index_reg_i);
    sel_box_cnt_slice       <= box_cnt_slices       (mi_value_index_reg_i);
    sel_box_width_slice     <= box_width_slices     (mi_value_index_reg_i);
    sel_ctrlo_slice         <= ctrlo_slices                         (mi_slice_reg_i);
    sel_ctrli_slice         <= ctrli_slices                         (mi_slice_reg_i);
    sel_cnter_slice         <= cnter_slices_reg     (mi_cnter_index_reg_i)(mi_slice_reg_i);
    sel_value_min_slice     <= value_min_slices_reg (mi_value_index_reg_i)(mi_slice_reg_i);
    sel_value_max_slice     <= value_max_slices_reg (mi_value_index_reg_i)(mi_slice_reg_i);
    sel_value_sum_slice     <= value_sum_slices_reg (mi_value_index_reg_i)(mi_slice_reg_i);
    sel_value_hist_slice    <= value_hist_slices_reg(mi_value_index_reg_i)(mi_slice_reg_i);

    -- Hist management --
    ---------------------

    hist_read_g : for i in 0 to VALUE_CNT - 1 generate
        hist_read_raw(i) <= '1' when (mi_value_index_reg_i = i and mi_addr_intern = MI_HIST_ADDR and MI_WR = '1' and MI_ARDY = '1') else
                            '0';
        hist_read_addr(msb(i, HIST_ADDR_WIDTH) downto lsb(i, HIST_ADDR_WIDTH))  <= mi_hist_reg(HIST_ADDR_WIDTH(i) - 1 downto 0);
    end generate;

    ---------------
    -- Registers --
    ---------------

    rst_done_reg_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            RST_DONE    <= rst_done_intern;
        end if;
    end process;

    ctrli_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            ctrli_reg   <= CTRLI;
        end if;
    end process;

    ctrlo_g : for i in 0 to CTRLO_SLICE_CNT - 1 generate
        ctrlo_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (rst_intern = '1') then
                    ctrlo_enlarge_reg(slice_msb(i) downto slice_lsb(i)) <= ctrlo_enlarge_default(slice_msb(i) downto slice_lsb(i));
                elsif (mi_addr_intern = MI_VALUE_ADDR and mi_stats_reg_i = 11 and mi_slice_reg_i = i and MI_WR = '1' and MI_ARDY = '1') then
                    ctrlo_enlarge_reg(slice_msb(i) downto slice_lsb(i)) <= MI_DWR;
                end if;
            end if;
        end process;
    end generate;

    cnter_g : for i in 0 to CNTER_CNT - 1 generate
        cnter_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (rst_intern = '1') then
                    cnter_reg_tmp(i)        <= (others => '0');
                    cnter_reg(i)            <= (others => '0');
                elsif (CNTERS_INCR(i) = '1') then
                    if (cnter_new(i)(CNTER_WIDTH) = '1') then   -- Counter overflow
                        cnter_reg_tmp(i)    <= CNTER_MAX;
                        if (CNTERS_SUBMIT(i) = '1') then
                            cnter_reg(i)    <= CNTER_MAX;
                        end if;
                    else
                        cnter_reg_tmp(i)    <= cnter_new(i)(CNTER_WIDTH - 1 downto 0);
                        if (CNTERS_SUBMIT(i) = '1') then
                            cnter_reg(i)    <= cnter_new(i)(CNTER_WIDTH - 1 downto 0);
                        end if;
                    end if;
                elsif (CNTERS_SUBMIT(i) = '1') then
                    cnter_reg(i)    <= cnter_reg_tmp(i);
                end if;
            end if;
        end process;
    end generate;

    value_cnter_reg_g : for i in CNTER_CNT to CNTER_CNT + VALUE_CNT - 1 generate
        value_cnter_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (rst_intern = '1') then
                    cnter_reg(i)        <= (others => '0');
                elsif (VALUES_VLD(i - CNTER_CNT) = '1') then
                    if (cnter_new(i)(CNTER_WIDTH) = '1') then -- Counter overflow
                        cnter_reg(i)    <= CNTER_MAX;
                    else
                        cnter_reg(i)    <= cnter_new(i)(CNTER_WIDTH - 1 downto 0);
                    end if;
                end if;
            end if;
        end process;
    end generate;

    value_min_g : for i in 0 to VALUE_CNT - 1 generate
        value_min_if_g : if (MIN_EN(i) = true) generate
            value_min_p : process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (rst_intern = '1') then
                        value_min_reg(msb(i) downto lsb(i)) <= MIN_INIT(msb(i) downto lsb(i));
                    elsif (VALUES_VLD(i) = '1' and VALUES(msb(i) downto lsb(i)) < value_min_reg(msb(i) downto lsb(i))) then
                        value_min_reg(msb(i) downto lsb(i)) <= VALUES(msb(i) downto lsb(i));
                    end if;
                end if;
            end process;
        end generate;
    end generate;

    value_max_g : for i in 0 to VALUE_CNT - 1 generate
        value_max_if_g : if (MAX_EN(i) = true) generate
            value_max_p : process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (rst_intern = '1') then
                        value_max_reg(msb(i) downto lsb(i)) <= MAX_INIT(msb(i) downto lsb(i));
                    elsif (VALUES_VLD(i) = '1' and VALUES(msb(i) downto lsb(i)) > value_max_reg(msb(i) downto lsb(i))) then
                        value_max_reg(msb(i) downto lsb(i)) <= VALUES(msb(i) downto lsb(i));
                    end if;
                end if;
            end process;
        end generate;
    end generate;

    value_sum_g : for i in 0 to VALUE_CNT - 1 generate
        value_sum_if_g : if (SUM_EN(i) = true) generate
            value_sum_p : process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (rst_intern = '1') then
                        value_sum_reg(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH)) <= (others => '0');
                    elsif (VALUES_VLD(i) = '1') then
                        value_sum_reg(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH)) <= value_sum_new(msb(i, SUM_WIDTH) downto lsb(i, SUM_WIDTH));
                    end if;
                end if;
            end process;
        end generate;
    end generate;

    slices_reg_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            cnter_slices_reg            <= cnter_slices;
            value_min_slices_reg        <= value_min_slices;
            value_max_slices_reg        <= value_max_slices;
            value_sum_slices_reg        <= value_sum_slices;
            value_hist_slices_reg       <= value_hist_slices;

            sel_reg_value_width_slice   <= sel_value_width_slice;
            sel_reg_value_ens_slice     <= sel_value_ens_slice;
            sel_reg_sum_extra_slice     <= sel_sum_extra_slice;
            sel_reg_box_cnt_slice       <= sel_box_cnt_slice;
            sel_reg_box_width_slice     <= sel_box_width_slice;
            sel_reg_ctrlo_slice         <= sel_ctrlo_slice;
            sel_reg_ctrli_slice         <= sel_ctrli_slice;
            sel_reg_cnter_slice         <= sel_cnter_slice;
            sel_reg_value_min_slice     <= sel_value_min_slice;
            sel_reg_value_max_slice     <= sel_value_max_slice;
            sel_reg_value_sum_slice     <= sel_value_sum_slice;
            sel_reg_value_hist_slice    <= sel_value_hist_slice;
        end if;
    end process;

    hist_read_delay_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            hist_read       <= hist_read_raw;
        end if;
    end process;

    hist_box_reg_g : for i in 0 to VALUE_CNT - 1 generate
        hist_box_reg_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (rst_intern = '1') then
                    hist_read_box_reg(msb(i, HIST_BOX_WIDTH) downto lsb(i, HIST_BOX_WIDTH))   <= (others => '0');
                elsif (hist_read_vld(i) = '1') then
                    hist_read_box_reg(msb(i, HIST_BOX_WIDTH) downto lsb(i, HIST_BOX_WIDTH))
                        <= hist_read_box(msb(i, HIST_BOX_WIDTH) downto lsb(i, HIST_BOX_WIDTH));
                end if;
            end if;
        end process;
    end generate;

    hist_box_vld_reg_g : for i in 0 to VALUE_CNT - 1 generate
        hist_box_vld_reg_p : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (rst_intern = '1' or hist_read_raw(i) = '1') then
                    hist_read_vld_reg(i)    <= '0';
                elsif (hist_read_vld(i) = '1') then
                    hist_read_vld_reg(i)    <= '1';
                end if;
            end if;
        end process;
    end generate;

    -- MI --

    mi_ctrl_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1') then
                mi_ctrl_reg    <= (others => '0');
            else
                mi_ctrl_reg(CTRL_RST_DONE_BIT)  <= RST_DONE;
                if (mi_addr_intern = MI_CTRL_ADDR and MI_WR = '1') then
                    mi_ctrl_reg(CTRL_RST_BIT)   <= MI_DWR(CTRL_RST_BIT);
                end if;
            end if;
        end if;
    end process;

    mi_stats_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1') then
                mi_stats_reg    <= (others => '0');
            elsif (mi_addr_intern = MI_STATS_ADDR and MI_WR = '1') then
                mi_stats_reg    <= MI_DWR;
            end if;
        end if;
    end process;

    mi_index_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1') then
                mi_index_reg    <= (others => '0');
            elsif (mi_addr_intern = MI_INDEX_ADDR and MI_WR = '1') then
                mi_index_reg    <= MI_DWR;
            end if;
        end if;
    end process;

    mi_slice_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1') then
                mi_slice_reg    <= (others => '0');
            elsif (mi_addr_intern = MI_SLICE_ADDR and MI_WR = '1') then
                mi_slice_reg    <= MI_DWR;
            end if;
        end if;
    end process;

    mi_hist_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1') then
                mi_hist_reg    <= (others => '0');
            elsif (mi_addr_intern = MI_HIST_ADDR and MI_WR = '1') then
                mi_hist_reg    <= MI_DWR;
            end if;
        end if;
    end process;

    mi_drd_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (mi_reading = '1') then
                MI_DRD  <= mi_sel_stat;
                MI_DRDY <= mi_sel_stat_vld;
            elsif (MI_RD = '1' and MI_ARDY = '1') then
                if (mi_addr_intern = MI_CTRL_ADDR) then
                    MI_DRD  <= mi_ctrl_reg;
                    MI_DRDY <= '1';
                elsif (mi_addr_intern = MI_STATS_ADDR) then
                    MI_DRD  <= mi_stats_reg;
                    MI_DRDY <= '1';
                elsif (mi_addr_intern = MI_INDEX_ADDR) then
                    MI_DRD  <= mi_index_reg;
                    MI_DRDY <= '1';
                elsif (mi_addr_intern = MI_SLICE_ADDR) then
                    MI_DRD  <= mi_slice_reg;
                    MI_DRDY <= '1';
                elsif (mi_addr_intern = MI_HIST_ADDR) then
                    MI_DRD  <= mi_hist_reg;
                    MI_DRDY <= '1';
                elsif (mi_addr_intern = MI_VALUE_ADDR) then
                    MI_DRD  <= mi_sel_stat;
                    MI_DRDY <= mi_sel_stat_vld;
                else
                    MI_DRD  <= X"DEAD_BEEF";
                    MI_DRDY <= '1';
                end if;
            else
                MI_DRDY     <= '0';
                MI_DRD      <= X"DEAD_BEAF";
            end if;
        end if;
    end process;

    mi_reading_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (rst_intern = '1' or mi_sel_stat_vld = '1') then
                mi_reading  <= '0';
            elsif (MI_RD = '1' and MI_ARDY = '1' and mi_addr_intern = MI_VALUE_ADDR) then
                mi_reading  <= '1';
            end if;
        end if;
    end process;

    mi_read_delay_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            mi_read_delayed(MI_READ_DELAY downto 1)     <= mi_read_delayed(MI_READ_DELAY - 1 downto 0);
            hist_read_delayed(MI_READ_DELAY downto 1)   <= hist_read_delayed(MI_READ_DELAY - 1 downto 0);
        end if;
    end process;

end architecture;
