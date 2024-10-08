-- mfb2axi.vhd: MFB to AXI bridge
-- Copyright (C) 2024 BrnoLogic, Ltd.
-- Author(s): Radek Hajek <hajek@brnologic.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- -------------------------------------------------------------------------
--                             Description
-- -------------------------------------------------------------------------

-- This component implements AXI stream to MFB bridge
--
-- The purpose of this IP is to translate MFB to AXI4 Stream with minimal stalls possible
-- The AXi stream communication is always aligned and the data is continuous (TKEEP is 1
-- from first to last byte). The stalls shall be generated ideally only in case where AXI
-- Stream is not capable to transmit 2 transactions in the some time while MFB is providing
-- all the data necessary to do it.
--
-- Architecture of this IP is:
-- 1. input stage (optional PIPE)
-- 2. pre-processor stage (used only for REGIONS > 1) with output registers
-- 3. combinatorial bridge stage (main logic translating MFB to AXI)
-- 4. output state (optional PIPE)
--
-- The minimal latency is in range from 0 clock cycles, i.e. combinatorial (MFB(1,x,y,z)
-- without input and output PIPEs) to 3 clock cycles (MFB(2+,x,y,z) with input and output
-- PIPES). Note that PIPE component does not have fixed latency in case of stalls, therefore
-- only the minimal latency is listed assuming the case where destination is always ready.
--

entity MFB2AXI is
    generic(
        -- =========================================================================
        -- input/output reg. config
        -- =========================================================================
        -- enables input register stage
        USE_IN_PIPE          : boolean := true;
        -- enables output register stage
        USE_OUT_PIPE         : boolean := true;

        -- =========================================================================
        -- MFB parameters
        --
        -- Frame size restrictions:
        -- regions: 1
        -- regison_size & block_size: power of 2
        -- item_width: 8
        -- =========================================================================

        -- any possitive value
        REGIONS             : natural := 1;
        -- any possitive value
        REGION_SIZE         : natural := 8;
        -- any possitive value
        BLOCK_SIZE          : natural := 32;
        ITEM_WIDTH          : natural := 8;

        -- =========================================================================
        -- AXI STREAM parameters
        --
        -- restrictions:
        -- size of AXI stream data needs to match MFB data size
        -- =========================================================================
        -- AXI stream data width
        AXI_DATA_WIDTH          : natural := 2048;

        -- =============================
        -- Others (PIPE config)
        -- =============================
        -- "SHREG" or "REG"
        PIPE_TYPE      : string  := "SHREG";
        DEVICE         : string  := "7SERIES"
   );
   port(
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================

        CLK              : in  std_logic;
        RST              : in  std_logic;

        -- =========================================================================
        -- RX MFB INTERFACE
        -- =========================================================================

        RX_MFB_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SRC_RDY  : in  std_logic;
        RX_MFB_DST_RDY  : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================

        TX_AXI_TDATA     : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
   );
end MFB2AXI;

architecture behavioral of MFB2AXI is

    constant REG_SOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE));
    constant REG_EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant MFB_DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant MFB_SOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE));
    constant MFB_EOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant REP_CNT           : natural := ITEM_WIDTH / 8;
    constant GLOBAL_EOF_POS_WIDTH  : natural := max(1, log2(REGIONS*REGION_SIZE*BLOCK_SIZE));
    constant GLOBAL_SOF_POS_WIDTH  : natural := max(1, log2(REGIONS*REGION_SIZE));
    constant REG_PTR_WIDTH     : natural := max(1, log2(REGIONS));
    constant PP_CNT_WIDTH      : natural := work.math_pack.min(2, log2(REGIONS)+1);

    subtype  SOF2EOF_POS_RANGE  is natural range GLOBAL_EOF_POS_WIDTH-1 downto GLOBAL_EOF_POS_WIDTH - GLOBAL_SOF_POS_WIDTH;

    -- functions
    -- checks if number if power of 2
    function is_powerof2 (n : natural) return boolean is
    begin
        return (2 ** log2(n)) = n;
    end is_powerof2;

    -- find LSB one index
    function lsb_one(slv : std_logic_vector) return natural is
        variable res : natural := 0;
    begin
        for i in 0 to slv'LENGTH - 1 loop
            if slv(i) = '1' then
                res := i;
                exit;
            end if;
        end loop;
        return res;
    end;

    -- find MSB one index
    function msb_one(slv : std_logic_vector) return natural is
        variable res : natural := 0;
    begin
        for i in slv'LENGTH - 1 downto 0 loop
            if slv(i) = '1' then
                res := i;
                exit;
            end if;
        end loop;
        return res;
    end;

    -- array for SOF to global SOF conversion
    type global_sof_array_t is array (0 to REGIONS -1) of unsigned (GLOBAL_SOF_POS_WIDTH-1 downto 0);
    signal global_sof_array : global_sof_array_t;

    -- array for EOF to global EOF conversion
    type global_eof_array_t is array (0 to REGIONS -1) of unsigned (GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal global_eof_array : global_eof_array_t;

    -- signals
    signal tkeep_item : std_logic_vector((AXI_DATA_WIDTH/ITEM_WIDTH)-1 downto 0);

    -- input stage
    signal mfb_data_in    : std_logic_vector(RX_MFB_DATA'RANGE);
    signal mfb_sof_pos_in : std_logic_vector(RX_MFB_SOF_POS'RANGE);
    signal mfb_eof_pos_in : std_logic_vector(RX_MFB_EOF_POS'RANGE);
    signal mfb_sof_in     : std_logic_vector(RX_MFB_SOF'RANGE);
    signal mfb_eof_in     : std_logic_vector(RX_MFB_EOF'RANGE);
    signal src_rdy_in     : std_logic;
    signal dst_rdy_in     : std_logic;

    -- output stage
    signal axi_tlast_out : std_logic;
    signal axi_tdata_out : std_logic_vector(TX_AXI_TDATA'RANGE);
    signal axi_tkeep_out : std_logic_vector(TX_AXI_TKEEP'RANGE);
    signal tvalid_out    : std_logic;
    signal tready_out    : std_logic;

    -- PRE-PROCESSOR FSM
    type t_state_preproc is (st_PP_DONE, st_PP_WAIT_EOF, st_PP_ONG);
    signal pp_curr_state : t_state_preproc;
    signal pp_next_state : t_state_preproc;

    -- pre-processor logic
    signal sof_reg_mask  : std_logic_vector(REGIONS-1 downto 0);
    signal eof_reg_mask  : std_logic_vector(REGIONS-1 downto 0);
    signal sof_masked    : std_logic_vector(REGIONS-1 downto 0);
    signal eof_masked    : std_logic_vector(REGIONS-1 downto 0);
    signal sof_reg_ptr_d : unsigned(REG_PTR_WIDTH-1 downto 0);
    signal sof_reg_ptr_q : unsigned(REG_PTR_WIDTH-1 downto 0);
    signal eof_reg_ptr_d : unsigned(REG_PTR_WIDTH-1 downto 0);
    signal eof_reg_ptr_q : unsigned(REG_PTR_WIDTH-1 downto 0);
    signal sof_cnt       : unsigned(REG_PTR_WIDTH downto 0);
    signal eof_cnt       : unsigned(REG_PTR_WIDTH downto 0);
    signal sof_first     : unsigned(REG_PTR_WIDTH-1 downto 0);
    signal eof_first     : unsigned(REG_PTR_WIDTH-1 downto 0);
    signal sof_last      : unsigned(REG_PTR_WIDTH-1 downto 0);

    signal sof_pos_first : unsigned(GLOBAL_SOF_POS_WIDTH-1 downto 0);
    signal sof_pos_last  : unsigned(GLOBAL_SOF_POS_WIDTH-1 downto 0);
    signal eof_pos_first : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal pp_valid      : std_logic;
    signal pp_sof_cnt    : unsigned(PP_CNT_WIDTH-1 downto 0);
    signal pp_eof_cnt    : unsigned(PP_CNT_WIDTH-1 downto 0);

    -- pre-processor output regs
    signal pp_sof_cnt_q       : unsigned(PP_CNT_WIDTH-1 downto 0);
    signal pp_eof_cnt_q       : unsigned(PP_CNT_WIDTH-1 downto 0);
    signal pp_sof_pos_first_q : unsigned(GLOBAL_SOF_POS_WIDTH-1 downto 0);
    signal pp_sof_pos_last_q  : unsigned(GLOBAL_SOF_POS_WIDTH-1 downto 0);
    signal pp_eof_pos_first_q : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal pp_mfb_data_q      : std_logic_vector(RX_MFB_DATA'RANGE);
    signal pp_valid_q         : std_logic;

    -- bridge FSM
    type t_state_bridge is (st_BR_DONE, st_BR_ONG_ALIGN, st_BR_ONG_UNALIGN, st_BR_STALL_UNALIGN, st_BR_ONG_UNALIGN_EOF);
    signal br_curr_state : t_state_bridge;
    signal br_next_state : t_state_bridge;

    -- bridge logic
    signal br_data_ptr_q    : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_data_ptr_d    : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_data_buffer_q : std_logic_vector(RX_MFB_DATA'RANGE);
    signal br_data_update   : std_logic;
    signal br_eof_data_len_off : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_eof_data_len_h: unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_eof_data_len_l: unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_eof_data_len  : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_shift_cnt     : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_eof_pos_q     : unsigned(GLOBAL_EOF_POS_WIDTH-1 downto 0);
    signal br_data_ext      : std_logic_vector(2*MFB_DATA_WIDTH - 1 downto 0);
    signal br_data_shift    : std_logic_vector(2*MFB_DATA_WIDTH - 1 downto 0);
    signal br_rdy           : std_logic;

begin
    -----------------------------------------------------------------------------
    -- valid parameters checks
    -----------------------------------------------------------------------------
    -- 1. MFB ITEM needs to be *byte - AXI stream use TKEEP by byte
    assert (ITEM_WIDTH mod 8 = 0)   report "ITEM_WIDTH/8 != 0"   severity FAILURE;

    -- 2. MFB REGIONS_SIZE is expected to be 2^n
    assert (is_powerof2(REGION_SIZE))   report "REGION_SIZE is not power of 2"   severity FAILURE;

    -- 3. MFB BLOCK_SIZE is expected to be 2^n
    assert (is_powerof2(BLOCK_SIZE))   report "BLOCK_SIZE is not power of 2"   severity FAILURE;

    -- 4. MFB and AXI stream data width needs to be equal
    assert (MFB_DATA_WIDTH = AXI_DATA_WIDTH)   report "MFB and AXIs data width is not matching"   severity FAILURE;

    -----------------------------------------------------------------------------
    -- input stage
    -----------------------------------------------------------------------------
    input_pipe_i :  entity  work.MFB_PIPE
        generic map(
            REGIONS       => REGIONS,
            REGION_SIZE   => REGION_SIZE,
            BLOCK_SIZE    => BLOCK_SIZE,
            ITEM_WIDTH    => ITEM_WIDTH,
            META_WIDTH    => 0,

            FAKE_PIPE     => not USE_IN_PIPE,
            USE_DST_RDY   => true,
            PIPE_TYPE     => PIPE_TYPE,
            DEVICE        => DEVICE
        )
        port map(
            CLK           => CLK,
            RESET         => RST,

            RX_DATA       => RX_MFB_DATA,
            RX_META       => (others => '0'),
            RX_SOF_POS    => RX_MFB_SOF_POS,
            RX_EOF_POS    => RX_MFB_EOF_POS,
            RX_SOF        => RX_MFB_SOF,
            RX_EOF        => RX_MFB_EOF,
            RX_SRC_RDY    => RX_MFB_SRC_RDY,
            RX_DST_RDY    => RX_MFB_DST_RDY,

            TX_DATA       => mfb_data_in,
            TX_META       => open,
            TX_SOF_POS    => mfb_sof_pos_in,
            TX_EOF_POS    => mfb_eof_pos_in,
            TX_SOF        => mfb_sof_in,
            TX_EOF        => mfb_eof_in,
            TX_SRC_RDY    => src_rdy_in,
            TX_DST_RDY    => dst_rdy_in
        );

    -----------------------------------------------------------------------------
    -- bridge logic
    -----------------------------------------------------------------------------
    mfb_config_g: if (REGIONS = 1 and REGION_SIZE = 1) generate
        -----------------------------------------------------------------------------
        -- direct connection AXI stream <=> MFB
        -----------------------------------------------------------------------------
        axi_tdata_out <= mfb_data_in;
        tvalid_out    <= src_rdy_in;
        dst_rdy_in    <= tready_out;

        -----------------------------------------------------------------------------
        -- output comb. logic
        -----------------------------------------------------------------------------
        -- TLAST is OR of MFB_EOF bits
        axi_tlast_out <= mfb_eof_in(0);

        -- TKEEP = LSbits 1 till last index
        axis_keep_p : process (all)
        begin
            tkeep_item <= (others => '0');

            for i in 0 to (AXI_DATA_WIDTH/ITEM_WIDTH)-1 loop
                tkeep_item(i) <= '1';
                exit when (i = to_integer(unsigned(mfb_eof_pos_in)));
            end loop;
        end process;

    else generate

        -----------------------------------------------------------------------------
        -- pre-processing stage
        -----------------------------------------------------------------------------
        -- purpose of this stage is to split transactions to following types of transactions:
        --   SOF, SOF + EOF, SOF + EOF + SOF or EOF, EOF + SOF

        mfb_preproc_g: if (REGIONS = 1) generate
            -- for REGIONS = 1 the pre-processor stage is not needed and is fully bypassed
            pp_sof_cnt_q       <= unsigned(mfb_sof_in);
            pp_eof_cnt_q       <= unsigned(mfb_eof_in);
            pp_sof_pos_first_q <= unsigned(mfb_sof_pos_in);
            pp_sof_pos_last_q  <= unsigned(mfb_sof_pos_in);
            pp_eof_pos_first_q <= unsigned(mfb_eof_pos_in);
            pp_mfb_data_q      <= mfb_data_in;
            pp_valid_q         <= src_rdy_in;
            dst_rdy_in         <= br_rdy;
        else generate
            -- decoding the incomming MFB transaction
            -- mask already processed regions
            sof_reg_mask <= (REGIONS-1 downto 0 => '1') sll to_integer(sof_reg_ptr_q);
            eof_reg_mask <= (REGIONS-1 downto 0 => '1') sll to_integer(eof_reg_ptr_q);
            sof_masked <= mfb_sof_in and sof_reg_mask;
            eof_masked <= mfb_eof_in and eof_reg_mask;

            -- count number of SOFs and EOFs in transaction
            sof_cnt <= to_unsigned(count_ones(sof_masked), sof_cnt'LENGTH);
            eof_cnt <= to_unsigned(count_ones(eof_masked), eof_cnt'LENGTH);

            -- find index of spefic SOFs and EOF
            sof_first <= to_unsigned(lsb_one(sof_masked), sof_first'LENGTH);
            sof_last  <= to_unsigned(msb_one(sof_masked), sof_last'LENGTH);
            eof_first <= to_unsigned(lsb_one(eof_masked), eof_first'LENGTH);

            -- create global position arrays
            global_pos_array_p: process(all)
            begin
                for i in 0 to REGIONS -1 loop
                    -- EOF
                    global_eof_array(i)(REG_EOF_POS_WIDTH-1 downto 0) <= unsigned(mfb_eof_pos_in((i + 1) * REG_EOF_POS_WIDTH - 1 downto i * REG_EOF_POS_WIDTH));
                    global_eof_array(i)(GLOBAL_EOF_POS_WIDTH-1 downto REG_EOF_POS_WIDTH) <= to_unsigned(i, GLOBAL_EOF_POS_WIDTH - REG_EOF_POS_WIDTH);

                    -- SOF
                    global_sof_array(i)(REG_SOF_POS_WIDTH-1 downto 0) <= unsigned(mfb_sof_pos_in((i + 1) * REG_SOF_POS_WIDTH - 1 downto i * REG_SOF_POS_WIDTH));
                    global_sof_array(i)(GLOBAL_SOF_POS_WIDTH-1 downto REG_SOF_POS_WIDTH) <= to_unsigned(i, GLOBAL_SOF_POS_WIDTH - REG_SOF_POS_WIDTH);
                end loop;
            end process;

            -- adapt POSs so it is pointing in complete data
            sof_pos_first <= global_sof_array(to_integer(sof_first));
            sof_pos_last  <= global_sof_array(to_integer(sof_last));
            eof_pos_first <= global_eof_array(to_integer(eof_first));

            -- pre-process seq. logic
            pp_seq_p: process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (RST = '1') then
                        pp_curr_state <= st_PP_DONE;
                        sof_reg_ptr_q <= (others => '0');
                        eof_reg_ptr_q <= (others => '0');
                    else
                        pp_curr_state <= pp_next_state;
                        sof_reg_ptr_q <= sof_reg_ptr_d;
                        eof_reg_ptr_q <= eof_reg_ptr_d;
                    end if;
                end if;
            end process;

            -- pre-processor next state logic
            pp_next_state_logic_p: process(all)
            begin
                -- default assignment
                pp_next_state <= pp_curr_state;

                if (src_rdy_in = '1' and br_rdy = '1') then
                    case pp_curr_state is
                        when st_PP_DONE =>
                            if (sof_cnt > 2 or sof_cnt = eof_cnt) then
                                -- 2*(SOF + EOF) + <...> / N*(SOF + EOF)
                                pp_next_state <= st_PP_DONE;
                            else
                                -- <SOF + EOF> + SOF
                                pp_next_state <= st_PP_WAIT_EOF;
                            end if;

                        when st_PP_WAIT_EOF =>
                            if (sof_cnt = 0 and eof_cnt = 1) then
                                -- EOF
                                pp_next_state <= st_PP_DONE;
                            elsif (sof_cnt = 1 and eof_cnt = 1) then
                                -- EOF + SOF
                                pp_next_state <= st_PP_WAIT_EOF;
                            elsif (eof_cnt > 1) then
                                -- EOF + SOF + EOF + <...>
                                -- only EOF will be send this cycle, PP_ONG is SOF aligned again
                                pp_next_state <= st_PP_ONG;
                            else
                                -- none
                                pp_next_state <= st_PP_WAIT_EOF;
                            end if;

                        when st_PP_ONG =>
                            if (sof_cnt = 1 and eof_cnt = 1) then
                                -- SOF + EOF
                                pp_next_state <= st_PP_DONE;
                            elsif (sof_cnt = 2 and eof_cnt = 1) then
                                -- SOF + EOF + SOF
                                pp_next_state <= st_PP_WAIT_EOF;
                            else
                                -- N*(SOF + EOF) + SOF
                                pp_next_state <= st_PP_ONG;
                            end if;

                        when others =>
                            pp_next_state <= st_PP_DONE;

                    end case;
                end if;
            end process;

            -- pre-processor comb. logic
            pp_comb_logic_p: process(all)
            begin
                -- default assignment
                pp_valid      <= '0';
                dst_rdy_in    <= '0';
                sof_reg_ptr_d <= sof_reg_ptr_q;
                eof_reg_ptr_d <= eof_reg_ptr_q;
                pp_sof_cnt    <= sof_cnt(PP_CNT_WIDTH-1 downto 0);
                pp_eof_cnt    <= eof_cnt(PP_CNT_WIDTH-1 downto 0);

                if (src_rdy_in = '1' and br_rdy = '1') then
                    pp_valid      <= '1';
                    sof_reg_ptr_d <= sof_first + 1;
                    eof_reg_ptr_d <= eof_first + 1;

                    case pp_curr_state is
                        when st_PP_DONE =>
                            if (eof_cnt = 1 or sof_cnt = 1) then
                                -- last SOF + <EOF> or <SOF> + EOF
                                dst_rdy_in    <= '1';
                                sof_reg_ptr_d <= (others => '0');
                                eof_reg_ptr_d <= (others => '0');
                            end if;

                            if (sof_cnt > 2 or sof_cnt = eof_cnt) then
                                -- 2*(SOF + EOF) + <...> / N*(SOF + EOF)
                                -- will send only first SOF + EOF frame
                                pp_sof_cnt    <= to_unsigned(1, pp_sof_cnt'LENGTH);
                                pp_eof_cnt    <= to_unsigned(1, pp_eof_cnt'LENGTH);
                            else
                                -- <SOF + EOF> + SOF
                                -- send as is (default)
                            end if;

                        when st_PP_WAIT_EOF =>
                            if (eof_cnt = 1 or (sof_cnt = 0 and eof_cnt = 0)) then
                                -- last EOF or none symbol
                                dst_rdy_in    <= '1';
                                sof_reg_ptr_d <= (others => '0');
                                eof_reg_ptr_d <= (others => '0');
                            end if;

                            if (sof_cnt = 0 and eof_cnt = 1) then
                                -- EOF
                                -- send as is (default)
                            elsif (sof_cnt = 1 and eof_cnt = 1) then
                                -- EOF + SOF
                                -- send as is (default)
                            elsif (eof_cnt > 1) then
                                -- EOF + SOF + EOF + <...>
                                -- only EOF will be send this cycle, SOF ptr not updated as not used
                                pp_sof_cnt    <= to_unsigned(0, pp_sof_cnt'LENGTH);
                                sof_reg_ptr_d <= sof_reg_ptr_q; -- SOF is not used here
                                pp_eof_cnt    <= to_unsigned(1, pp_eof_cnt'LENGTH);
                            else
                                -- none
                                -- send as is (default)
                            end if;

                        when st_PP_ONG =>
                            if (eof_cnt = 1) then
                                -- last EOF
                                dst_rdy_in    <= '1';
                                sof_reg_ptr_d <= (others => '0');
                                eof_reg_ptr_d <= (others => '0');
                            end if;


                            if (sof_cnt = 1 and eof_cnt = 1) then
                                -- SOF + EOF
                                -- send as is (default)
                            elsif (sof_cnt = 2 and eof_cnt = 1) then
                                -- SOF + EOF + SOF
                                -- send as is (default)
                            else
                                -- N*(SOF + EOF) + SOF
                                -- will send only first SOF + EOF frame
                                pp_sof_cnt    <= to_unsigned(1, pp_sof_cnt'LENGTH);
                                pp_eof_cnt    <= to_unsigned(1, pp_eof_cnt'LENGTH);
                            end if;

                        when others =>
                            -- default

                    end case;
                end if;
            end process;

            -- pre-process output register logic
            pp_out_reg_p: process(CLK)
            begin
                if (rising_edge(CLK)) then
                    -- FF with reset
                    if (RST = '1') then
                        pp_valid_q         <= '0';
                    else
                        if (pp_valid = '1') then
                            pp_valid_q         <= '1';
                        elsif (br_rdy = '1') then
                            -- clear pp_valid flaf in case it was accepted and new is not available yet
                            pp_valid_q         <= '0';
                        end if;
                    end if;
                    -- FF witout reset
                    if (pp_valid = '1') then
                        pp_sof_cnt_q       <= pp_sof_cnt;
                        pp_eof_cnt_q       <= pp_eof_cnt;
                        pp_sof_pos_first_q <= sof_pos_first;
                        pp_sof_pos_last_q  <= sof_pos_last;
                        pp_eof_pos_first_q <= eof_pos_first;
                        pp_mfb_data_q      <= mfb_data_in;
                    end if;
                end if;
            end process;
        end generate;

        -----------------------------------------------------------------------------
        -- bridge logic
        -----------------------------------------------------------------------------
        -- translates pre-processed MFB to AXI

        -- bridge seq. logic
        br_fsm_seq_p: process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    br_curr_state <= st_BR_DONE;
                    br_data_ptr_q <= (others => '0');
                else
                    br_curr_state <= br_next_state;
                    if (br_data_update = '1') then
                        -- low bits are always 0, synthesis should optimize it
                        br_data_ptr_q(SOF2EOF_POS_RANGE) <= br_data_ptr_d(SOF2EOF_POS_RANGE);
                        br_data_buffer_q <= pp_mfb_data_q;
                        br_eof_pos_q <= pp_eof_pos_first_q;
                    end if;
                end if;
            end if;
        end process;

        -- bridge next state logic
        br_next_state_logic_p: process(all)
        begin
            -- default assignment
            br_next_state <= br_curr_state;

            case br_curr_state is
                when st_BR_DONE =>
                    if (pp_valid_q = '1') then
                        -- pre-processor stage valid
                        if (pp_sof_cnt_q = 1 and pp_eof_cnt_q = 1 and tready_out = '1') then
                            -- SOF + EOF + output stage ready (need to send)
                            br_next_state <= st_BR_DONE;
                        elsif (pp_sof_cnt_q = 2 and tready_out = '1') then
                            -- SOF + EOF + SOF + output stage ready (need to send)
                            br_next_state <= st_BR_ONG_UNALIGN;
                        elsif (pp_sof_cnt_q = 1 and pp_eof_cnt_q = 0) then
                            -- SOF
                            if (pp_sof_pos_first_q = 0 and tready_out = '1') then
                                -- SOF is aligned => check output stage ready (need to send)
                                br_next_state <= st_BR_ONG_ALIGN;
                            elsif (pp_sof_pos_first_q /= 0) then
                                -- SOF is NOT aligned => cannot send, output stage does not have to be ready in this cycle
                                br_next_state <= st_BR_ONG_UNALIGN;
                            end if;
                        end if;
                    end if;

                when st_BR_ONG_ALIGN =>
                    if (pp_valid_q = '1'  and tready_out = '1') then
                        -- pre-processor stage valid + output stage ready (need to send)
                        if (pp_eof_cnt_q = 1 and pp_sof_cnt_q = 0) then
                            -- EOF
                            br_next_state <= st_BR_DONE;
                        elsif (pp_eof_cnt_q = 1 and pp_sof_cnt_q = 1) then
                            -- EOF + SOF
                            br_next_state <= st_BR_ONG_UNALIGN;
                        else
                            -- none
                            br_next_state <= st_BR_ONG_ALIGN;
                        end if;
                    end if;

                when st_BR_ONG_UNALIGN =>
                    if (pp_valid_q = '1'  and tready_out = '1') then
                        -- pre-processor stage valid + output stage ready (need to send)
                        if (pp_eof_cnt_q = 1 and br_data_ptr_q > pp_eof_pos_first_q) then
                            -- EOF + all data available
                            if (pp_sof_cnt_q = 0) then
                                -- not SOF
                                br_next_state <= st_BR_DONE;
                            else
                                -- another SOF (always unaligned)
                                br_next_state <= st_BR_ONG_UNALIGN;
                            end if;
                        elsif (pp_eof_cnt_q = 1  and br_data_ptr_q <= pp_eof_pos_first_q) then
                            -- EOF + all data not available
                            if (pp_sof_cnt_q = 0) then
                                -- not SOF => stall may not be necassary (next cycle the frame will be finished)
                                br_next_state <= st_BR_ONG_UNALIGN_EOF;
                            else
                                -- another SOF => need to stall the bus finish last frame next clock cycle
                                br_next_state <= st_BR_STALL_UNALIGN;
                            end if;
                        else
                            -- none
                            br_next_state <= st_BR_ONG_UNALIGN;
                        end if;
                    end if;

                when st_BR_STALL_UNALIGN =>
                    if (tready_out = '1') then
                        -- output stage ready (need to send)
                        -- finish ongoing frame
                        br_next_state <= st_BR_ONG_UNALIGN;
                    end if;

                when st_BR_ONG_UNALIGN_EOF =>
                    if (tready_out = '1') then
                        -- output stage ready (need to send)
                        -- finish ongoing frame
                        if (pp_valid_q = '1'and pp_eof_cnt_q = 0 and pp_sof_cnt_q = 1 and pp_sof_pos_first_q /= 0) then
                            -- SOF which is not aligned
                            br_next_state <= st_BR_ONG_UNALIGN;
                        else
                            -- not valid transaction / SOF + EOF + <...> / SOF aligned
                            br_next_state <= st_BR_DONE;
                        end if;
                    end if;

                when others =>
                    br_next_state <= st_BR_DONE;

            end case;
        end process;

        -- bridge output. logic
        br_output_logic_p: process(all)
        begin
            -- default assignment
            br_data_update <= '0';
            br_data_ptr_d  <= br_data_ptr_q;
            axi_tlast_out  <= '0';
            tvalid_out     <= pp_valid_q;
            br_rdy         <= tready_out;
            br_eof_data_len_off <= (others => '0');
            br_eof_data_len_h <= (others => '0');
            br_eof_data_len_l <= (others => '0');
            br_shift_cnt      <= br_data_ptr_q;

            -- current state decoding
            case br_curr_state is
                when st_BR_DONE =>
                    -- data_len = 0 + EOF_POS - SOF_POS
                    br_eof_data_len_off <= (others => '0');
                    br_eof_data_len_h   <= pp_eof_pos_first_q;
                    br_eof_data_len_l(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;

                    -- data shift
                    br_shift_cnt(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;

                    if (pp_valid_q = '1') then
                        -- pre-processor stage valid
                        if (pp_sof_cnt_q = 1 and pp_eof_cnt_q = 1 and tready_out = '1') then
                            -- SOF + EOF + output stage ready (need to send)
                            -- frame finished
                            -- => st_BR_DONE
                            axi_tlast_out <= '1';
                        elsif (pp_sof_cnt_q = 2 and tready_out = '1') then
                            -- SOF + EOF + SOF + output stage ready (need to send)
                            -- frame finished, another started
                            -- => st_BR_ONG_UNALIGN
                            axi_tlast_out <= '1';
                            br_data_update <= '1';
                            br_data_ptr_d(SOF2EOF_POS_RANGE) <= pp_sof_pos_last_q;
                        elsif (pp_sof_cnt_q = 1 and pp_eof_cnt_q = 0) then
                            -- SOF
                            br_data_update <= '1';
                            br_data_ptr_d(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;

                            if (pp_sof_pos_first_q = 0 and tready_out = '1') then
                                -- SOF is aligned => check output stage ready (need to send)
                                -- => st_BR_ONG_ALIGN
                                -- default
                            elsif (pp_sof_pos_first_q /= 0) then
                                -- SOF is NOT aligned => cannot send, output stage does not have to be ready in this cycle
                                -- => st_BR_ONG_UNALIGN
                                tvalid_out <= '0';
                                br_rdy     <= '1';
                            end if;
                        end if;
                    end if;

                when st_BR_ONG_ALIGN =>
                    -- data_len = 0 + EOF_POS - 0
                    br_eof_data_len_off <= (others => '0');
                    br_eof_data_len_h   <= pp_eof_pos_first_q;
                    br_eof_data_len_l   <= (others => '0');

                    if (pp_valid_q = '1'  and tready_out = '1') then
                        -- pre-processor stage valid + output stage ready (need to send)
                        br_data_update <= '1';

                        if (pp_eof_cnt_q = 1 and pp_sof_cnt_q = 0) then
                            -- EOF
                            -- frame finished
                            -- => st_BR_DONE
                            axi_tlast_out <= '1';
                        elsif (pp_eof_cnt_q = 1 and pp_sof_cnt_q = 1) then
                            -- EOF + SOF
                            -- frame finished, another started
                            -- => st_BR_ONG_UNALIGN
                            axi_tlast_out <= '1';
                            br_data_ptr_d(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;
                        else
                            -- none
                            -- => st_BR_ONG_ALIGN
                            -- default
                        end if;
                    end if;

                when st_BR_ONG_UNALIGN =>
                    -- data_len = CONST + EOF_POS - DATA_PTR (EOF < PTR)
                    br_eof_data_len_off <= to_unsigned(REGIONS*REGION_SIZE*BLOCK_SIZE, br_eof_data_len_off'LENGTH);
                    br_eof_data_len_h <= pp_eof_pos_first_q;
                    br_eof_data_len_l <= br_data_ptr_q;

                    if (pp_valid_q = '1'  and tready_out = '1') then
                        -- pre-processor stage valid + output stage ready (need to send)
                        br_data_update <= '1';

                        if (pp_eof_cnt_q = 1 and br_data_ptr_q > pp_eof_pos_first_q) then
                            -- EOF + all data available
                            -- frame finished
                            axi_tlast_out <= '1';
                            if (pp_sof_cnt_q = 0) then
                                -- not SOF
                                -- => st_BR_DONE
                            else
                                -- another SOF (always unaligned)
                                -- => st_BR_ONG_UNALIGN
                                br_data_ptr_d(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;
                            end if;
                        elsif (pp_eof_cnt_q = 1 and br_data_ptr_q <= pp_eof_pos_first_q) then
                            -- EOF + all data not available
                            if (pp_sof_cnt_q = 0) then
                                -- not SOF => stall may not be necassary (next cycle the frame will be finished)
                                -- => st_BR_ONG_UNALIGN_EOF
                                -- default
                            else
                                -- another SOF => need to stall the bus finish last frame next clock cycle
                                -- => st_BR_STALL_UNALIGN
                                br_rdy <= '0';
                            end if;
                        else
                            -- none
                            -- => st_BR_ONG_UNALIGN
                            -- default
                        end if;
                    end if;


                when st_BR_STALL_UNALIGN =>
                    -- data_len = 0 + EOF_POS - DATA_PTR ... (EOF > PTR)
                    br_eof_data_len_off <= (others => '0');
                    br_eof_data_len_h <= pp_eof_pos_first_q;
                    br_eof_data_len_l <= br_data_ptr_q;

                    -- axi control
                    -- frame finished
                    axi_tlast_out <= '1';
                    tvalid_out   <= '1';

                    if (tready_out = '1') then
                        -- output stage ready (need to send)
                        -- finish ongoing frame
                        -- => st_BR_ONG_UNALIGN
                        br_data_update <= '1';
                        br_data_ptr_d(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;
                    end if;

                when st_BR_ONG_UNALIGN_EOF =>
                    -- data_len = 0 + EOF_POS (register) - DATA_PTR  ... (EOF > PTR)
                    br_eof_data_len_off <= (others => '0');
                    br_eof_data_len_h <= br_eof_pos_q;
                    br_eof_data_len_l <= br_data_ptr_q;

                    -- axi control
                    -- frame finished
                    axi_tlast_out <= '1';
                    tvalid_out   <= '1';

                    if (tready_out = '1') then
                        -- output stage ready (need to send)
                        -- finish ongoing frame
                        if (pp_valid_q = '1' and pp_eof_cnt_q = 0 and pp_sof_cnt_q = 1 and pp_sof_pos_first_q /= 0) then
                            -- SOF which is not aligned
                            -- => st_BR_ONG_UNALIGN
                            br_data_update <= '1';
                            br_data_ptr_d(SOF2EOF_POS_RANGE) <= pp_sof_pos_first_q;
                        else
                            -- not valid transaction / SOF + EOF + <...> / SOF aligned
                            -- => st_BR_DONE
                            br_rdy <= '0';
                        end if;
                    end if;

                when others =>
                    tvalid_out   <= '0';
                    br_rdy  <= '0';
                    br_data_update <= '1';
                    br_data_ptr_d  <= (others => '0');

            end case;
        end process;

        -- compute the data length
        br_eof_data_len <= resize(('0' & br_eof_data_len_off) + ('0' & br_eof_data_len_h) - ('0' & br_eof_data_len_l), br_eof_data_len);

        -- concatenate input data with buffer if needed
        br_data_ext <= pp_mfb_data_q & pp_mfb_data_q when (br_curr_state = st_BR_DONE or br_curr_state = st_BR_ONG_ALIGN) else
                       pp_mfb_data_q & br_data_buffer_q;

        -- shift the transmited data to LSB
        br_data_shift <= std_logic_vector(unsigned(br_data_ext) srl (to_integer(br_shift_cnt) * ITEM_WIDTH));

        -- low data taken
        axi_tdata_out <= br_data_shift(axi_tdata_out'RANGE);

        -- TKEEP = LSbits 1 till last index
        axis_keep_p : process (all)
        begin
            tkeep_item <= (others => '0');

            for i in 0 to (AXI_DATA_WIDTH/ITEM_WIDTH)-1 loop
                tkeep_item(i) <= '1';
                exit when (i = to_integer(unsigned(br_eof_data_len)));
            end loop;
        end process;

    end generate;

    -- tkeep_item is distributed to TKEEP, MSB bit is useless
    -- in case ITEM_WIDTH is multiple bytes, it needs to be replicated to multiple bit
    tkeep_ext_p : process (all)
    begin
        if (axi_tlast_out = '1') then
            -- EOF => generate appropriete TKEEP
            iterate_vector_l : for i in 0 to tkeep_item'LEFT loop
                axi_tkeep_out((i + 1) * REP_CNT - 1 downto i * REP_CNT) <= (others => tkeep_item(i));
            end loop;
        else
            -- otherwise keep TKEEP all 1s
            axi_tkeep_out <= (others => '1');
        end if;
    end process;

    -----------------------------------------------------------------------------
    -- output stage
    -----------------------------------------------------------------------------
    output_pipe_i :  entity  work.AXI_PIPE
        generic map(
            AXI_DATA_WIDTH  => AXI_DATA_WIDTH,
            FAKE_PIPE       => not USE_OUT_PIPE,
            USE_DST_RDY     => true,
            PIPE_TYPE       => PIPE_TYPE,
            DEVICE          => DEVICE
        )
        port map(
            CLK           => CLK,
            RESET         => RST,

            RX_AXI_TDATA   => axi_tdata_out,
            RX_AXI_TKEEP   => axi_tkeep_out,
            RX_AXI_TLAST   => axi_tlast_out,
            RX_AXI_TVALID  => tvalid_out,
            RX_AXI_TREADY  => tready_out,

            TX_AXI_TDATA   => TX_AXI_TDATA,
            TX_AXI_TKEEP   => TX_AXI_TKEEP,
            TX_AXI_TLAST   => TX_AXI_TLAST,
            TX_AXI_TVALID  => TX_AXI_TVALID,
            TX_AXI_TREADY  => TX_AXI_TREADY
        );

end architecture;
