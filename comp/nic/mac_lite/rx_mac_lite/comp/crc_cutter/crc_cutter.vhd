-- crc_cutter.vhd: CRC cutter
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_CRC_CUTTER is
    generic(
        REGIONS     : natural := 4; -- any possitive value
        REGION_SIZE : natural := 8; -- any possitive value
        BLOCK_SIZE  : natural := 8; -- must be >= 4 and power of two
        ITEM_WIDTH  : natural := 8; -- must be 8
        OUTPUT_REG  : boolean := True
    );
    port(
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK            : in  std_logic;
        RESET          : in  std_logic;
        -- =======================================================================
        -- INPUT MFB LIKE INTERFACE (don't support gaps inside frame!):
        -- =======================================================================
        RX_DATA        : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_SOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS     : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF         : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY     : in  std_logic;
        RX_ADAPTER_ERR : in  std_logic_vector(REGIONS-1 downto 0);
        -- =======================================================================
        -- OUTPUT MFB LIKE INTERFACE
        -- =======================================================================
        TX_DATA        : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_SOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS     : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF         : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY     : out std_logic;
        TX_ADAPTER_ERR : out std_logic_vector(REGIONS-1 downto 0);
        TX_CRC_CUT_ERR : out std_logic_vector(REGIONS-1 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_CRC_CUTTER is

    constant DATA_WIDTH       : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant SOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));

    signal s_err_mca          : std_logic_vector(REGIONS downto 0);
    signal s_sof_mca          : std_logic_vector(REGIONS downto 0);
    signal s_eof_mca          : std_logic_vector(REGIONS downto 0);
    signal s_sof_pos_mca      : slv_array_t(REGIONS downto 0)(SOF_POS_SIZE-1 downto 0);
    signal s_eof_pos_mca      : slv_array_t(REGIONS downto 0)(EOF_POS_SIZE-1 downto 0);

    signal s_reg1_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal s_reg1_sof_pos     : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
    signal s_reg1_eof_pos     : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
    signal s_reg1_sof_pos_arr : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
    signal s_reg1_eof_pos_arr : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
    signal s_reg1_sof         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg1_eof         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg1_adapter_err : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg1_src_rdy     : std_logic;

    signal s_sof_eof_one_blk  : std_logic_vector(REGIONS downto 0);
    signal s_one_blk_frame    : std_logic_vector(REGIONS downto 0);
    signal s_small_eof_pos    : std_logic_vector(REGIONS downto 0);
    signal s_overflow_eof     : std_logic_vector(REGIONS downto 0);
    signal s_need_move_eof    : std_logic_vector(REGIONS downto 0);
    signal s_move_eof_allowed : std_logic_vector(REGIONS downto 0);
    signal s_crc_cut_error    : std_logic_vector(REGIONS-1 downto 0);

    signal s_new_eof          : std_logic_vector(REGIONS-1 downto 0);
    signal s_new_eof_pos_arr  : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
    signal s_new_eof_pos      : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
    signal s_new_err          : std_logic_vector(REGIONS-1 downto 0);

    signal s_inc_frame        : std_logic_vector(REGIONS downto 0);
    signal s_valid_region     : std_logic_vector(REGIONS-1 downto 0);
    signal s_valid_word       : std_logic;

    signal s_reg2_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal s_reg2_sof_pos     : std_logic_vector(REGIONS*SOF_POS_SIZE-1 downto 0);
    signal s_reg2_eof_pos     : std_logic_vector(REGIONS*EOF_POS_SIZE-1 downto 0);
    signal s_reg2_sof         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg2_eof         : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg2_adapter_err : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg2_crc_cut_err : std_logic_vector(REGIONS-1 downto 0);
    signal s_reg2_src_rdy     : std_logic;

begin

    assert (ITEM_WIDTH = 8)
        report "RX_MAC_LITE_CRC_CUTTER: ITEM_WIDTH must be 8, other values are not supported!!!"
        severity failure;

    assert (BLOCK_SIZE >= 4)
        report "RX_MAC_LITE_CRC_CUTTER: BLOCK_SIZE must be >= 4 and power of two!!!"
        severity failure;

    -- =========================================================================
    --  1. LOGIC STAGE
    -- =========================================================================

    -- create first part of multi-cycle arrays
    s_err_mca(REGIONS)     <= RX_ADAPTER_ERR(0);
    s_sof_mca(REGIONS)     <= RX_SOF(0) and RX_SRC_RDY;
    s_eof_mca(REGIONS)     <= RX_EOF(0) and RX_SRC_RDY;
    s_eof_pos_mca(REGIONS) <= RX_EOF_POS(EOF_POS_SIZE-1 downto 0);
    s_sof_pos_mca(REGIONS) <= RX_SOF_POS(SOF_POS_SIZE-1 downto 0);

    -- =========================================================================
    --  1. REGISTER STAGE
    -- =========================================================================

    reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_reg1_data        <= RX_DATA;
            s_reg1_sof_pos     <= RX_SOF_POS;
            s_reg1_eof_pos     <= RX_EOF_POS;
            s_reg1_sof         <= RX_SOF;
            s_reg1_eof         <= RX_EOF;
            s_reg1_adapter_err <= RX_ADAPTER_ERR;
        end if;
    end process;

    reg1_vld_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg1_src_rdy <= '0';
            else
                s_reg1_src_rdy <= RX_SRC_RDY;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  2. LOGIC STAGE
    -- =========================================================================

    s_reg1_sof_pos_arr <= slv_array_deser(s_reg1_sof_pos,REGIONS,SOF_POS_SIZE);
    s_reg1_eof_pos_arr <= slv_array_deser(s_reg1_eof_pos,REGIONS,EOF_POS_SIZE);

    -- create second part of multi-cycle arrays
    eof_mca_g : for r in 0 to REGIONS-1 generate
        s_err_mca(r)     <= s_reg1_adapter_err(r);
        s_sof_mca(r)     <= s_reg1_sof(r) and s_reg1_src_rdy;
        s_eof_mca(r)     <= s_reg1_eof(r) and s_reg1_src_rdy;
        s_sof_pos_mca(r) <= s_reg1_sof_pos_arr(r);
        s_eof_pos_mca(r) <= s_reg1_eof_pos_arr(r);
    end generate;

    -- detect very small frames (size <= 1 block)
    one_blk_frame_g : for r in 0 to REGIONS generate
        s_sof_eof_one_blk(r) <= '1' when (unsigned(s_sof_pos_mca(r)) = unsigned(s_eof_pos_mca(r)(EOF_POS_SIZE-1 downto EOF_POS_SIZE-SOF_POS_SIZE))) else '0';
        s_one_blk_frame(r)   <= s_sof_eof_one_blk(r) and s_eof_mca(r) and s_sof_mca(r);
    end generate;

    -- detect state, when EOF_POS is too small and new EOF will be in previous region
    overflow_eof_g : for r in 0 to REGIONS generate
        s_small_eof_pos(r) <= '1' when (unsigned(s_eof_pos_mca(r)) < 4) else '0';
        s_overflow_eof(r)  <= s_small_eof_pos(r) and s_eof_mca(r);
        s_need_move_eof(r) <= s_overflow_eof(r) and not s_one_blk_frame(r);
    end generate;

    overflow_eof_ok_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_move_eof_allowed(0) <= '0';
            elsif (s_reg1_src_rdy = '1') then
                s_move_eof_allowed(0) <= s_move_eof_allowed(REGIONS);
            end if;
        end if;
    end process;

    new_eof_eof_pos_g : for r in 0 to REGIONS-1 generate
        -- generate overflow EOF OK flag
        s_move_eof_allowed(r+1) <= s_need_move_eof(r+1) and not s_eof_mca(r);
        -- cut CRC error
        s_crc_cut_error(r) <= (s_need_move_eof(r) and not s_move_eof_allowed(r)) or s_one_blk_frame(r);

        -- generate new EOF for cut CRC
        new_eof_p : process (s_move_eof_allowed,s_eof_mca)
        begin
            if (s_move_eof_allowed(r+1) = '1') then -- move EOF allowed, created new EOF
                s_new_eof(r) <= '1';
            elsif (s_move_eof_allowed(r) = '1') then -- removed old EOF
                s_new_eof(r) <= '0';
            else
                s_new_eof(r) <= s_eof_mca(r);
            end if;
        end process;

        -- generate new Adapter ERROR for cut CRC
        new_err_p : process (s_move_eof_allowed,s_err_mca)
        begin
            if (s_move_eof_allowed(r+1) = '1') then -- move EOF allowed
                s_new_err(r) <= s_err_mca(r+1);
            else
                s_new_err(r) <= s_err_mca(r);
            end if;
        end process;

        -- generate new EOF_POS for cut CRC
        new_eof_pos_arr_p : process (all)
        begin
            if (s_move_eof_allowed(r+1) = '1') then -- move EOF allowed
                s_new_eof_pos_arr(r) <= std_logic_vector(unsigned(s_eof_pos_mca(r+1)) - 4);
            elsif ((s_need_move_eof(r) = '1' and s_move_eof_allowed(r) = '0') or (s_one_blk_frame(r) = '1')) then -- move EOF NOT allowed or CRC cut is disabled due to one block frame
                s_new_eof_pos_arr(r) <= s_eof_pos_mca(r);
            else -- simple cuting - only changed EOF_POS
                s_new_eof_pos_arr(r) <= std_logic_vector(unsigned(s_eof_pos_mca(r)) - 4);
            end if;
        end process;
    end generate;

    s_new_eof_pos <= slv_array_ser(s_new_eof_pos_arr,REGIONS,EOF_POS_SIZE);

    -- -------------------------------------------------------------------------
    --  FRAME STATE LOGIC
    -- -------------------------------------------------------------------------

    inc_frame2_g : for r in 0 to REGIONS-1 generate
        s_inc_frame(r+1) <= (s_reg1_sof(r) and not s_new_eof(r) and not s_inc_frame(r)) or
                            (s_reg1_sof(r) and s_new_eof(r) and s_inc_frame(r)) or
                            (not s_reg1_sof(r) and not s_new_eof(r) and s_inc_frame(r));
    end generate;

    inc_frame_last_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_inc_frame(0) <= '0';
            elsif (s_reg1_src_rdy = '1') then
                s_inc_frame(0) <= s_inc_frame(REGIONS);
            end if;
        end if;
    end process;

    valid_region_g : for r in 0 to REGIONS-1 generate
        s_valid_region(r) <= s_reg1_sof(r) or s_new_eof(r) or s_inc_frame(r);
    end generate;
    s_valid_word <= (or s_valid_region) and s_reg1_src_rdy;

    -- =========================================================================
    --  2. REGISTER STAGE
    -- =========================================================================

    out_reg_g : if OUTPUT_REG generate
        reg2_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                s_reg2_data        <= s_reg1_data;
                s_reg2_sof_pos     <= s_reg1_sof_pos;
                s_reg2_eof_pos     <= s_new_eof_pos;
                s_reg2_sof         <= s_reg1_sof;
                s_reg2_eof         <= s_new_eof;
                s_reg2_adapter_err <= s_new_err;
                s_reg2_crc_cut_err <= s_crc_cut_error;
            end if;
        end process;

        reg2_vld_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                s_reg2_src_rdy <= '0';
                else
                s_reg2_src_rdy <= s_valid_word;
                end if;
            end if;
        end process;
    end generate;

    no_out_reg_g : if not OUTPUT_REG generate
        s_reg2_data        <= s_reg1_data;
        s_reg2_sof_pos     <= s_reg1_sof_pos;
        s_reg2_eof_pos     <= s_new_eof_pos;
        s_reg2_sof         <= s_reg1_sof;
        s_reg2_eof         <= s_new_eof;
        s_reg2_adapter_err <= s_new_err;
        s_reg2_crc_cut_err <= s_crc_cut_error;
        s_reg2_src_rdy     <= s_valid_word;
    end generate;

    -- output ports
    TX_DATA        <= s_reg2_data;
    TX_SOF_POS     <= s_reg2_sof_pos;
    TX_EOF_POS     <= s_reg2_eof_pos;
    TX_SOF         <= s_reg2_sof;
    TX_EOF         <= s_reg2_eof;
    TX_ADAPTER_ERR <= s_reg2_adapter_err;
    TX_CRC_CUT_ERR <= s_reg2_crc_cut_err;
    TX_SRC_RDY     <= s_reg2_src_rdy;

end architecture;
