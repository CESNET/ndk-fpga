-- mux.vhd: Generic multiplexer
-- Copyright (C) 2019 CESNET
-- Author(s): Jan Kubalek  <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                                Description
-- ----------------------------------------------------------------------------
-- This is a universal component for behavioral Multiplexer with optional
-- pipelining and output register.
-- Pipelining is enabled by setting the MUX_LATENCY generic to a non-zero
-- (positive) value. This way the multiplexing is optimally distributed into
-- multiple levels to improve timing.
-- The total latency is additionally increased by 1 if the OUTPUT_REG
-- generic is set to true.
--
-- OPTIMALIZATION_1:
--    Multiplexers 2:1 are now only used when MUX_WIDTH==2.
--    When MUX_WIDTH>2, only multiplexers 4:1 and bigger are used.
--    This should save resources on any architecture, where a LUT has
--    at least 6 input ports.
--
-- OPTIMALIZATION_2:
--    If the generated pipeline contains levels with no multiplexers at all (MUX 1:1),
--    these levels are put at the pipeline's end, where the data width
--    is just 1*DATA_WIDTH.
--
-- Examples:
--    ----------------
--    MUX_WIDTH   = 100
--    MUX_LATENCY = 2
--    OUTPUT_REG  = false
--
--    resulting pipeline --> ( 32 x MUX 4:1 | 32 x REG | 8 x MUX 4:1 | 8 x REG | 1 x MUX 8:1 )
--    ----------------
--    MUX_WIDTH   = 100
--    MUX_LATENCY = 2
--    OUTPUT_REG  = true
--
--    resulting pipeline --> ( 32 x MUX 4:1 | 32 x REG | 8 x MUX 4:1 | 8 x REG | 1 x MUX 8:1 | 1 x REG )
--    ----------------
--    MUX_WIDTH   = 5
--    MUX_LATENCY = 1
--    OUTPUT_REG  = false
--
--    resulting pipeline (without OPTIMALIZATIONs)                    --> ( 4 x MUX 2:1 | 4 x REG | 1 x MUX 4:1 ) -- uses MUX 2:1, which is not effective
--    resulting pipeline (with OPTIMALIZATION_1)                      --> ( 8 x MUX 1:1 | 8 x REG | 1 x MUX 8:1 ) -- uses up too much REGs
--    resulting pipeline (with OPTIMALIZATION_1 and OPTIMALIZATION_2) --> ( 1 x MUX 8:1 | 1 x REG | 1 x MUX 1:1 ) -- best option
--    ----------------
--    MUX_WIDTH   = 5
--    MUX_LATENCY = 0
--    OUTPUT_REG  = false
--
--    resulting pipeline --> ( 1 x MUX 8:1 )
--    ----------------
--
-- By setting the MUX_LATENCY to 0 and OUTPUT_REG to false the component is reduced
-- to one simple GEN_MUX.

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity GEN_MUX_PIPED is
generic(
    -- Width of multiplexed data blocks
    DATA_WIDTH     : integer := 64;
    -- Number of input data blocks
    MUX_WIDTH      : integer := 15;
    -- Latency of the multiplexer pipeline
    MUX_LATENCY    : integer := 0;
    -- Input register enable (adds additional 1 CLK latency)
    INPUT_REG      : boolean := false;
    -- Output register enable (adds additional 1 CLK latency)
    OUTPUT_REG     : boolean := false;

    -- Metadata can be useful when you want to send additional info to the TX side
    -- along with the multiplexed value. (for example the value of the RX_SEL signal)
    METADATA_WIDTH : integer := 0
);
port(
    CLK         : in  std_logic := '0'; -- unused when MUX_LATENCY==0 and OUTPUT_REG==INPUT_REG==false
    RESET       : in  std_logic := '0'; -- unused when MUX_LATENCY==0 and OUTPUT_REG==INPUT_REG==false

    RX_DATA     : in  std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
    RX_SEL      : in  std_logic_vector(log2(MUX_WIDTH)-1 downto 0);
    RX_METADATA : in  std_logic_vector(METADATA_WIDTH-1 downto 0) := (others => '0');
    RX_SRC_RDY  : in  std_logic := '1';
    RX_DST_RDY  : out std_logic;

    TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
    TX_METADATA : out std_logic_vector(METADATA_WIDTH-1 downto 0);
    TX_SRC_RDY  : out std_logic;
    TX_DST_RDY  : in  std_logic := '1'
);
end entity GEN_MUX_PIPED;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of GEN_MUX_PIPED is
    constant MUX_WIDTH_EXT : integer := 2**log2(MUX_WIDTH);

    -- optimalizations can be turned off for experimantation
    constant OPTIMALIZATION_1 : boolean := true;
    constant OPTIMALIZATION_2 : boolean := true;

    -- function for computing widths of multiplexers in different levels when latency is not 0
    function getMuxWidthsLog(width, latency : integer) return i_array_t is
        variable mux_widths_log     : i_array_t(latency+1-1 downto 0);
        variable tmp                : integer;
        variable muxes              : integer := latency+1; -- number of multiplexer levels
        variable mux_widths_log_tmp : i_array_t(latency+1-1 downto 0);
        variable non_zeros_index    : integer;
    begin
        mux_widths_log := (others => 0); -- set all multiplexers to minimum width

        ----
        -- OPTIMALIZATION 1 (see unit Description)
        if (OPTIMALIZATION_1) then
            if (width=2) then
                mux_widths_log(0) := 1;
                return mux_widths_log;
            end if;
        end if;
        ----

        tmp := 1;
        for l in 0 to width*2-1 loop -- should actually always break by the return inside (this is just a safer "while true")
            for i in muxes-1 downto 0 loop -- start widening multiplexers from the last level to the first
                 if (tmp=width) then -- check reaching the final width
                     ----
                     -- OPTIMALIZATION 2 (see unit Description)
                     if (OPTIMALIZATION_2) then
                         non_zeros_index := 0;
                         for e in 0 to muxes-1 loop
                             exit when (mux_widths_log(e)/=0);
                             non_zeros_index := non_zeros_index+1;
                         end loop;

                         -- put all zero-sized multiplexers to the end of the pipeline
                         mux_widths_log := mux_widths_log(non_zeros_index-1 downto 0) & mux_widths_log(muxes-1 downto non_zeros_index);
                         ----
                     end if;

                     return mux_widths_log;
                 end if;

                 -- else enlarge the multiplexer to double

                 ----
                 -- OPTIMALIZATION 1 (see unit Description)
                 if (OPTIMALIZATION_1) then
                    if (mux_widths_log(i)=0) then
                        -- don't create MUX 2:1
                        -- jump right to MUX 4:1
                        mux_widths_log(i) := mux_widths_log(i)+2;
                        tmp := tmp*4;
                        if (tmp>width) then -- if this is too much
                            -- start enlarging back from the begining
                            mux_widths_log(i) := mux_widths_log(i)-2;
                            tmp := tmp/4;
                            exit;
                        end if;
                    else
                        -- double the size of this mux
                        mux_widths_log(i) := mux_widths_log(i)+1;
                        tmp := tmp*2;
                    end if;
                ----
                else
                    -- double the size of this mux
                    mux_widths_log(i) := mux_widths_log(i)+1;
                    tmp := tmp*2;
                end if;
            end loop;
        end loop;
        return mux_widths_log;
    end function;

    function getMuxWidths(mux_widths_log : i_array_t; latency : integer) return i_array_t is
        variable mux_widths : i_array_t(latency+1-1 downto 0);
        variable muxes      : integer := latency+1; -- number of multiplexer levels
    begin
        for i in 0 to muxes-1 loop
            mux_widths(i) := 2**mux_widths_log(i);
        end loop;
        return mux_widths;
    end function;

    function getMuxSelHighs(mux_widths_log : i_array_t; width, latency : integer) return i_array_t is
        variable mux_sel_highs : i_array_t(latency+1-1 downto 0);
        variable muxes         : integer := latency+1; -- number of multiplexer levels
    begin
        mux_sel_highs(0) := log2(width)-1;
        for i in 1 to muxes-1 loop
            mux_sel_highs(i) := mux_sel_highs(i-1)-mux_widths_log(i-1);
        end loop;
        return mux_sel_highs;
    end function;

    function getMuxCnts(mux_widths_log : i_array_t; width, latency : integer) return i_array_t is
        variable mux_cnts : i_array_t(latency+1-1 downto 0);
        variable muxes    : integer := latency+1; -- number of multiplexer levels
    begin
        mux_cnts(0) := width/(2**mux_widths_log(0));
        for i in 1 to muxes-1 loop
            mux_cnts(i) := mux_cnts(i-1)/(2**mux_widths_log(i));
        end loop;
        return mux_cnts;
    end function;

    function getOutRegInt(out_reg : boolean) return integer is
    begin
        if (out_reg) then
            return 1;
        else
            return 0;
        end if;
    end function;

    constant MUX_WIDTHS_LOG : i_array_t(MUX_LATENCY+1-1 downto 0) := getMuxWidthsLog(MUX_WIDTH_EXT,MUX_LATENCY);
    constant MUX_WIDTHS     : i_array_t(MUX_LATENCY+1-1 downto 0) := getMuxWIdths(MUX_WIDTHS_LOG,MUX_LATENCY);
    constant MUX_SEL_HIGHS  : i_array_t(MUX_LATENCY+1-1 downto 0) := getMuxSelHighs(MUX_WIDTHS_LOG,MUX_WIDTH_EXT,MUX_LATENCY);
    constant MUX_CNTS       : i_array_t(MUX_LATENCY+1-1 downto 0) := getMuxCnts(MUX_WIDTHS_LOG,MUX_WIDTH_EXT,MUX_LATENCY);

    constant OUTPUT_REG_INT : integer := getOutRegInt(OUTPUT_REG);

    -- input register
    signal in_reg_rx_data     : std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
    signal in_reg_rx_sel      : std_logic_vector(log2(MUX_WIDTH)-1 downto 0);
    signal in_reg_rx_metadata : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal in_reg_rx_src_rdy  : std_logic;
    signal in_reg_rx_dst_rdy  : std_logic;

    -- per mux level signals
    signal data_in_arr       : slv_array_2d_t  (MUX_LATENCY+1+1-1 downto 0)(MUX_WIDTH_EXT-1 downto 0)(DATA_WIDTH-1 downto 0) := (others => (others => (others => 'X'))); -- registers (the last one is unused (possible output reg))
    signal data_in_reord_arr : slv_array_2d_t  (MUX_LATENCY+1+1-1 downto 0)(MUX_WIDTH_EXT-1 downto 0)(MUX_WIDTH_EXT*DATA_WIDTH-1 downto 0) := (others => (others => (others => 'X')));
    signal src_rdy_in        : std_logic_vector(MUX_LATENCY+1+1-1 downto 0);
    signal dst_rdy_in        : std_logic_vector(MUX_LATENCY+1+1+1-1 downto 0);
    signal sel_in            : slv_array_t     (MUX_LATENCY+1+1-1 downto 0)(log2(MUX_WIDTH)-1 downto 0);
    signal metadata_in       : slv_array_t     (MUX_LATENCY+1+1-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal data_out          : slv_array_2d_t  (MUX_LATENCY+1+1-1 downto 0)(MUX_WIDTH_EXT-1 downto 0)(DATA_WIDTH-1 downto 0) := (others => (others => (others => 'X')));

begin

    in_reg_yes_gen : if (INPUT_REG) generate
        in_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RX_DST_RDY='1') then
                    in_reg_rx_data     <= RX_DATA;
                    in_reg_rx_sel      <= RX_SEL;
                    in_reg_rx_metadata <= RX_METADATA;
                    in_reg_rx_src_rdy  <= RX_SRC_RDY;
                end if;

                if (RESET='1') then
                    in_reg_rx_src_rdy <= '0';
                end if;
            end if;
        end process;
        RX_DST_RDY <= '1' when in_reg_rx_dst_rdy='1' or in_reg_rx_src_rdy='0' else '0';
    else generate
        in_reg_rx_data     <= RX_DATA;
        in_reg_rx_sel      <= RX_SEL;
        in_reg_rx_metadata <= RX_METADATA;
        in_reg_rx_src_rdy  <= RX_SRC_RDY;
        RX_DST_RDY <= in_reg_rx_dst_rdy;
    end generate;

    data_in_arr(0)(MUX_WIDTH-1 downto 0) <= slv_array_downto_deser(in_reg_rx_data, MUX_WIDTH, DATA_WIDTH);
    sel_in(0)         <= in_reg_rx_sel;
    metadata_in(0)    <= in_reg_rx_metadata;
    src_rdy_in(0)     <= in_reg_rx_src_rdy;
    in_reg_rx_dst_rdy <= dst_rdy_in(0);
    dst_rdy_in(0)     <= dst_rdy_in(1);

    mux_levels_gen : for i in 0 to MUX_LATENCY+1-1 generate

        mux_level_gen : for e in 0 to MUX_CNTS(i)-1 generate
            signal sel : std_logic_vector(max(1,MUX_WIDTHS_LOG(i))-1 downto 0) := (others => '0');
        begin

            mux_input_reordering_item_gen : for g in 0 to MUX_WIDTHS(i)-1 generate
                data_in_reord_arr(i)(e)((g+1)*DATA_WIDTH-1 downto g*DATA_WIDTH) <= data_in_arr(i)(g*MUX_CNTS(i)+e);
            end generate;

            -- this is written like this to fix the stupid max(1,log(WIDTHS)) thing in the GEN_MUX interface
            sel(MUX_WIDTHS_LOG(i)-1 downto 0) <= sel_in(i)(MUX_SEL_HIGHS(i) downto MUX_SEL_HIGHS(i)+1-MUX_WIDTHS_LOG(i));

            gen_mux_gen : entity work.GEN_MUX
            generic map (
                DATA_WIDTH => DATA_WIDTH,
                MUX_WIDTH  => MUX_WIDTHS(i)
            )
            port map (
                DATA_IN  => data_in_reord_arr(i)(e)(MUX_WIDTHS(i)*DATA_WIDTH-1 downto 0),
                SEL      => sel,
                DATA_OUT => data_out(i)(e)
            );

        end generate;

        next_level_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (dst_rdy_in(i+1)='1') then
                    data_in_arr(i+1) <= data_out(i);
                    sel_in(i+1)      <= sel_in(i);
                    metadata_in(i+1) <= metadata_in(i);
                    src_rdy_in(i+1)  <= src_rdy_in(i);
                end if;

                if (RESET='1') then
                    src_rdy_in(i+1)  <= '0';
                end if;
            end if;
        end process;

    end generate;

    dst_rdy_gen : for i in 1 to MUX_LATENCY+OUTPUT_REG_INT+1-1 generate
        dst_rdy_in(i) <= '1' when dst_rdy_in(i+1)='1' or src_rdy_in(i)='0' else '0';
    end generate;

    dst_rdy_in(MUX_LATENCY+OUTPUT_REG_INT+1+1-1) <= TX_DST_RDY;
    TX_SRC_RDY                      <= src_rdy_in(MUX_LATENCY+OUTPUT_REG_INT+1-1);
    TX_DATA                         <= data_out(MUX_LATENCY+1-1)(0) when OUTPUT_REG=false else data_in_arr(MUX_LATENCY+OUTPUT_REG_INT+1-1)(0);
    TX_METADATA                     <= metadata_in(MUX_LATENCY+OUTPUT_REG_INT+1-1);

end architecture full;
