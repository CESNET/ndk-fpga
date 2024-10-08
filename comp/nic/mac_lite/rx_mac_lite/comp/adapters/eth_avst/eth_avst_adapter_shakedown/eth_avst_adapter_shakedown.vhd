-- eth_avst_adapter_shakedown.vhd: Shakedown for ETH_AVST_ADAPTER
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

-- .. Note::
-- Allowed MFB configurations
--   - Input:  1,1,M,8, M=DATA_WIDTH/8 (-> SOF is aligned to BLOCK(0)),
--   - Output: 1,N,8,8, N=DATA_WIDTH/64.

-- .. Warning::
-- DATA_WIDTH other than 512 b is not expected!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity ETH_AVST_ADAPTER_SHAKEDOWN is
    generic(
        DATA_WIDTH     : natural := 512;
        TX_REGION_SIZE : natural := DATA_WIDTH/64
    );
    port(
        -- CLOCK AND RESET
        CLK               : in  std_logic;
        RESET             : in  std_logic;
        -- INPUT MFB INTERFACE
        IN_MFB_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
        IN_MFB_SOF        : in std_logic;
        IN_MFB_EOF        : in std_logic;
        IN_MFB_EOF_POS    : in std_logic_vector(max(1,log2(TX_REGION_SIZE*8))-1 downto 0);
        IN_MFB_ERROR      : in std_logic_vector(1-1 downto 0) := (others => '0'); -- aligned to EOF
        IN_MFB_UNDERSIZED : in std_logic; -- aligned to EOF
        IN_MFB_SRC_RDY    : in std_logic;
        -- OUTPUT MFB INTERFACE
        OUT_MFB_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        OUT_MFB_SOF       : out std_logic_vector(1-1 downto 0);
        OUT_MFB_SOF_POS   : out std_logic_vector(max(1,log2(TX_REGION_SIZE))-1 downto 0);
        OUT_MFB_EOF       : out std_logic_vector(1-1 downto 0);
        OUT_MFB_EOF_POS   : out std_logic_vector(max(1,log2(TX_REGION_SIZE*8))-1 downto 0);
        OUT_MFB_ERROR     : out std_logic_vector(1-1 downto 0); -- aligned to EOF
        OUT_MFB_SRC_RDY   : out std_logic
    );
end entity;

architecture FULL of ETH_AVST_ADAPTER_SHAKEDOWN is

    -- ========================================================================
    --                              Constants
    -- ========================================================================
    constant DATA_BYTES       : natural := DATA_WIDTH/8;
    -- COMPR_ITEMS indicates how closely can packets be placed after each other (= granularity of compression)
    -- options: TX_REGION_SIZE (-> maximum -> worst timing), TX_REGION_SIZE/2, TX_REGION_SIZE/4
    constant COMPR_ITEMS      : natural := TX_REGION_SIZE;
    constant SOF_POS_LIMIT    : natural := log2(TX_REGION_SIZE) - log2(COMPR_ITEMS);
    constant INT_BLOCK_WIDTH  : natural := DATA_WIDTH/COMPR_ITEMS; -- internal BLOCK_WIDTH
    constant INT_BLOCK_SIZE   : natural := DATA_BYTES/COMPR_ITEMS; -- internal BLOCK_SIZE
    --                                     data            + sof + eof + eof_pos              + error
    constant COMPR_ITEM_WIDTH : natural := INT_BLOCK_WIDTH + 1   + 1   + log2(INT_BLOCK_SIZE) + 1;

    -- ========================================================================
    --                              Signals
    -- ========================================================================
    signal IN_MFB_DATA_arr               : slv_array_t     (COMPR_ITEMS-1 downto 0)(INT_BLOCK_WIDTH-1 downto 0);
    signal last_valid_block              : unsigned        (max(1,log2(COMPR_ITEMS))-1 downto 0);
    signal last_valid_item               : unsigned        (max(1,log2(INT_BLOCK_SIZE))-1 downto 0);
    signal IN_MFB_SOF_arr                : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal IN_MFB_EOF_arr                : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal IN_MFB_ERROR_arr              : std_logic_vector(COMPR_ITEMS-1 downto 0);

    signal compr_in_data_arr             : slv_array_t     (COMPR_ITEMS-1 downto 0)(COMPR_ITEM_WIDTH-1 downto 0);
    signal compr_in_data                 : std_logic_vector(COMPR_ITEMS*            COMPR_ITEM_WIDTH-1 downto 0);
    signal compr_in_data_reg0            : std_logic_vector(COMPR_ITEMS*            COMPR_ITEM_WIDTH-1 downto 0);
    signal compr_in_data_reg1            : std_logic_vector(COMPR_ITEMS*            COMPR_ITEM_WIDTH-1 downto 0);
    signal compr_in_last_reg0            : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal compr_in_valid_per_block      : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal compr_in_valid_per_block_reg0 : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal compr_in_valid_per_block_reg1 : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal compr_in_full_reg1            : std_logic;

    signal compr_out_data                : std_logic_vector(COMPR_ITEMS*            COMPR_ITEM_WIDTH-1 downto 0);
    signal compr_out_data_arr            : slv_array_t     (COMPR_ITEMS-1 downto 0)(COMPR_ITEM_WIDTH-1 downto 0);
    signal compr_out_item_vld            : std_logic_vector(COMPR_ITEMS-1 downto 0);

    signal mfb_data_arr                  : slv_array_t     (COMPR_ITEMS-1 downto 0)(INT_BLOCK_WIDTH-1 downto 0);
    signal mfb_data_arr_reg2             : slv_array_t     (COMPR_ITEMS-1 downto 0)(INT_BLOCK_WIDTH-1 downto 0);
    signal mfb_data_arr_reg3             : slv_array_t     (COMPR_ITEMS-1 downto 0)(INT_BLOCK_WIDTH-1 downto 0);
    signal mfb_sof_arr                   : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_sof_arr_reg2              : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_sof_arr_reg3              : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_eof_arr                   : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_eof_arr_reg2              : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_eof_arr_reg3              : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_eof_pos_item_arr          : slv_array_t     (COMPR_ITEMS-1 downto 0)(log2(INT_BLOCK_SIZE)-1 downto 0); -- only the lowest 3 bits of eof_pos (indicates item in each block)
    signal mfb_eof_pos_item_arr_reg2     : slv_array_t     (COMPR_ITEMS-1 downto 0)(log2(INT_BLOCK_SIZE)-1 downto 0);
    signal mfb_eof_pos_item_arr_reg3     : slv_array_t     (COMPR_ITEMS-1 downto 0)(log2(INT_BLOCK_SIZE)-1 downto 0);
    signal mfb_error_arr                 : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_error_arr_reg2            : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_error_arr_reg3            : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_vld_reg2                  : std_logic_vector(COMPR_ITEMS-1 downto 0);
    signal mfb_src_rdy_reg2              : std_logic;
    signal mfb_src_rdy_reg3              : std_logic;

    signal mfb_data                      : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mfb_sof                       : std_logic_vector(1-1 downto 0);
    signal mfb_sof_pos                   : std_logic_vector(max(1,log2(TX_REGION_SIZE))-1 downto 0);
    signal mfb_eof                       : std_logic_vector(1-1 downto 0);
    signal mfb_eof_pos                   : std_logic_vector(max(1,log2(TX_REGION_SIZE*8))-1 downto 0);
    signal mfb_error                     : std_logic_vector(1-1 downto 0);
    signal mfb_src_rdy                   : std_logic;

begin

    -- ========================================================================
    --  Input logic
    -- ========================================================================
    IN_MFB_DATA_arr <= slv_array_deser(IN_MFB_DATA, COMPR_ITEMS);

    last_valid_block_item_p : process(all)
    begin
        last_valid_block <= resize_right(unsigned(IN_MFB_EOF_POS), log2(COMPR_ITEMS)); -- first few bits of EOF_POS indicate BLOCK
        last_valid_item  <= resize_left (unsigned(IN_MFB_EOF_POS), log2(INT_BLOCK_SIZE)); -- last few bits of EOF_POS indicate ITEM
        if ((IN_MFB_UNDERSIZED = '1') and (IN_MFB_EOF = '1')) then
            last_valid_block <= to_unsigned(COMPR_ITEMS-1, max(1,log2(COMPR_ITEMS)));
            last_valid_item  <= (others => '0');
        end if;
    end process;

    in_sof_eof_p: process(all)
    begin
        -- assign sof only to the first BLOCK -> serves to identify sof_pos at shakedown's output
        IN_MFB_SOF_arr    <= (others => '0');
        IN_MFB_SOF_arr(0) <= IN_MFB_SOF and IN_MFB_SRC_RDY;
        -- assign eof only to the last BLOCK -> serves as first 2 bits of eof_pos (indicates BLOCK)
        IN_MFB_EOF_arr                               <= (others => '0');
        IN_MFB_EOF_arr(to_integer(last_valid_block)) <= IN_MFB_EOF and IN_MFB_SRC_RDY;
        -- error is only valid with EOF
        IN_MFB_ERROR_arr <= (others => (IN_MFB_ERROR(0) and IN_MFB_EOF));
    end process;

    -- ========================================================================
    --  Shake packets down (compressor)
    -- ========================================================================
    compr_in_data_g : for i in COMPR_ITEMS-1 downto 0 generate
        --                       data               & sof               & eof               & last 4 bits of EOF_POS            & error
        compr_in_data_arr(i) <= IN_MFB_DATA_arr(i) & IN_MFB_SOF_arr(i) & IN_MFB_EOF_arr(i) & std_logic_vector(last_valid_item) & IN_MFB_ERROR_arr(i);
    end generate;
    compr_in_data <= slv_array_ser(compr_in_data_arr);

    -- valid for each item (BLOCK) of shakedown's data
    compr_in_valid_per_block(0) <= IN_MFB_SRC_RDY;
    avst_valid_g : for i in COMPR_ITEMS-1 downto 1 generate
        compr_in_valid_per_block(i) <= IN_MFB_SRC_RDY when ((IN_MFB_EOF = '0') or (last_valid_block >= i)) else '0';
    end generate;

    -- Input regs -------------------------------------------------------------
    shakedown_in_regs: process(CLK)
    begin
        if rising_edge(CLK) then
            compr_in_data_reg0            <= compr_in_data;
            compr_in_last_reg0            <= IN_MFB_EOF_arr;
            compr_in_valid_per_block_reg0 <= compr_in_valid_per_block;

            if (RESET = '1') then
                compr_in_last_reg0 <= (others => '0');
                compr_in_valid_per_block_reg0 <= (others => '0');
                compr_in_valid_per_block_reg1 <= (others => '0');
            end if;
        end if;
    end process;

    compress_i : entity work.EASA_COMPRESSOR_LITE
    generic map(
        ITEMS      => COMPR_ITEMS,
        ITEM_WIDTH => COMPR_ITEM_WIDTH
    )
    port map(
        CLK     => CLK,
        RESET   => RESET,
        RX_DATA => compr_in_data_reg0,
        RX_LAST => compr_in_last_reg0,
        RX_VLD  => compr_in_valid_per_block_reg0,
        TX_DATA => compr_out_data,
        TX_VLD  => compr_out_item_vld
    );

    compr_out_data_arr <= slv_array_deser(compr_out_data, COMPR_ITEMS);
    shakedown_out_data_g : for i in COMPR_ITEMS-1 downto 0 generate
        mfb_data_arr        (i) <= compr_out_data_arr(i)(COMPR_ITEM_WIDTH-1 downto COMPR_ITEM_WIDTH-INT_BLOCK_WIDTH);
        mfb_sof_arr         (i) <= compr_out_data_arr(i)(COMPR_ITEM_WIDTH-INT_BLOCK_WIDTH-1);
        mfb_eof_arr         (i) <= compr_out_data_arr(i)(COMPR_ITEM_WIDTH-INT_BLOCK_WIDTH-1-1);
        mfb_eof_pos_item_arr(i) <= compr_out_data_arr(i)(COMPR_ITEM_WIDTH-INT_BLOCK_WIDTH-1-1-1 downto 1);
        mfb_error_arr       (i) <= compr_out_data_arr(i)(0);
    end generate;

    -- Output regs ------------------------------------------------------------
    shakedown_out_regs : process(CLK)
    begin
        if rising_edge(CLK) then
            mfb_data_arr_reg2         <= mfb_data_arr;
            mfb_sof_arr_reg2          <= mfb_sof_arr;
            mfb_eof_arr_reg2          <= mfb_eof_arr;
            mfb_eof_pos_item_arr_reg2 <= mfb_eof_pos_item_arr;
            mfb_error_arr_reg2        <= mfb_error_arr;
            mfb_vld_reg2              <= compr_out_item_vld;
            mfb_src_rdy_reg2          <= compr_out_item_vld(0);

            mfb_data_arr_reg3         <= mfb_data_arr_reg2;
            mfb_sof_arr_reg3          <= mfb_sof_arr_reg2 and mfb_vld_reg2;
            mfb_eof_arr_reg3          <= mfb_eof_arr_reg2 and mfb_vld_reg2;
            mfb_eof_pos_item_arr_reg3 <= mfb_eof_pos_item_arr_reg2;
            mfb_error_arr_reg3        <= mfb_error_arr_reg2;
            mfb_src_rdy_reg3          <= mfb_src_rdy_reg2;

            if (RESET = '1') then
                mfb_src_rdy_reg2 <= '0';
                mfb_src_rdy_reg3 <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    --  Output logic
    -- ========================================================================
    mfb_data <= slv_array_ser(mfb_data_arr_reg3);

    mfb_sof(0) <= or (mfb_sof_arr_reg3);

    out_sof_pos_p : process(all)
    begin
        mfb_sof_pos <= (others => '0');
        for i in COMPR_ITEMS-1 downto 0 loop
            if (mfb_sof_arr_reg3(i) = '1') then
                -- convert to standard BLOCK_WIDTH=8 (resize to log2(8))
                mfb_sof_pos(log2(TX_REGION_SIZE)-1 downto SOF_POS_LIMIT) <= std_logic_vector(to_unsigned(i, max(1, log2(COMPR_ITEMS))));
            end if;
        end loop;
    end process;

    mfb_eof(0) <= or (mfb_eof_arr_reg3);

    out_eof_pos_p : process(all)
    begin
        mfb_eof_pos <= (others => '0');
        mfb_error   <= (others => '0');
        for i in COMPR_ITEMS-1 downto 0 loop
            if (mfb_eof_arr_reg3(i) = '1') then
                --              upper bits indicate BLOCK                                   & lower bits indicate ITEM
                mfb_eof_pos  <= std_logic_vector(to_unsigned(i, max(1, log2(COMPR_ITEMS)))) & mfb_eof_pos_item_arr_reg3(i);
                mfb_error(0) <= mfb_error_arr_reg3(i);
            end if;
        end loop;
    end process;

    mfb_src_rdy <= mfb_src_rdy_reg3;

    -- ========================================================================
    --  Output register
    -- ========================================================================
    out_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            OUT_MFB_DATA    <= mfb_data;
            OUT_MFB_SOF     <= mfb_sof;
            OUT_MFB_SOF_POS <= mfb_sof_pos;
            OUT_MFB_EOF     <= mfb_eof;
            OUT_MFB_EOF_POS <= mfb_eof_pos;
            OUT_MFB_ERROR   <= mfb_error;
            OUT_MFB_SRC_RDY <= mfb_src_rdy;
            if (RESET = '1') then
                OUT_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
