-- compressor_lite.vhd
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity EASA_COMPRESSOR_LITE is
    generic(
        -- ====================================================================
        -- BUS CONFIGURATION:
        -- ====================================================================
        ITEMS      : natural := 2;
        ITEM_WIDTH : natural := 512
    );
    port(
        -- ====================================================================
        -- CLOCK AND RESET
        -- ====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;
        -- ====================================================================
        -- INPUT INTERFACE
        -- ====================================================================
        RX_DATA    : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- Identifies the last item in a burst of inseparable items.
        RX_LAST    : in  std_logic_vector(ITEMS-1 downto 0);
        -- Valids of items, minimum size of item burst is ITEMS.
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        -- ====================================================================
        -- OUTPUT INTERFACES
        -- ====================================================================
        TX_DATA    : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD     : out std_logic_vector(ITEMS-1 downto 0)
    );
end entity;

architecture FULL of EASA_COMPRESSOR_LITE is

    constant BS_BLOCK_WIDTH : natural := ITEM_WIDTH+2;

    signal s_rx_data_arr         : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_rx_vld_sum          : std_logic_vector(log2(ITEMS+1)-1 downto 0);

    signal s_rx_data_arr_reg     : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_rx_vld_sum_reg      : unsigned(log2(ITEMS+1)-1 downto 0);
    signal s_rx_last_reg         : std_logic_vector(ITEMS-1 downto 0);
    signal s_rx_vld_reg          : std_logic_vector(ITEMS-1 downto 0);

    signal s_bs_data_in_arr      : slv_array_t(ITEMS-1 downto 0)(BS_BLOCK_WIDTH-1 downto 0);
    signal s_bs_data_out         : std_logic_vector(ITEMS*BS_BLOCK_WIDTH-1 downto 0);
    signal s_bs_data_out_arr     : slv_array_t(ITEMS-1 downto 0)(BS_BLOCK_WIDTH-1 downto 0);
    signal s_bs_sel              : std_logic_vector(log2(ITEMS)-1 downto 0);

    signal s_bs_out_vld          : std_logic_vector(ITEMS-1 downto 0);
    signal s_bs_out_last         : std_logic_vector(ITEMS-1 downto 0);
    signal s_bs_out_data_arr     : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);

    signal s_reg_vld_count       : unsigned(log2(ITEMS)-1 downto 0);
    signal s_reg_vld_count_next  : unsigned(log2(ITEMS)-1 downto 0);
    signal s_reg_vld_vector      : std_logic_vector(ITEMS-1 downto 0);
    signal s_reg_vld_vector_next : std_logic_vector(ITEMS-1 downto 0);

    signal s_reg_data            : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_reg_last            : std_logic_vector(ITEMS-1 downto 0);
    signal s_timeout_cnt         : unsigned(5-1 downto 0);
    signal s_last_of_burst       : std_logic;
    signal s_force_push          : std_logic;

    signal s_out_en              : std_logic;
    signal s_data_out_arr        : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_vld_out_arr         : std_logic_vector(ITEMS-1 downto 0);
    signal s_vld_out_sum         : unsigned(log2(ITEMS+1)-1 downto 0);

begin

    s_rx_data_arr <= slv_array_downto_deser(RX_DATA,ITEMS,ITEM_WIDTH);

    rx_vld_sum_i : entity work.SUM_ONE
    generic map(
        INPUT_WIDTH => ITEMS,
        OUTPUT_REG  => False
    )
    port map(
        CLK      => CLK,
        RESET    => RESET,
        DIN      => RX_VLD,
        DIN_MASK => (others => '1'),
        DIN_VLD  => '1',
        DOUT     => s_rx_vld_sum,
        DOUT_VLD => open
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_rx_data_arr_reg <= s_rx_data_arr;
            s_rx_vld_sum_reg  <= unsigned(s_rx_vld_sum);
            s_rx_last_reg     <= RX_LAST;
            s_rx_vld_reg      <= RX_VLD;
            if (RESET = '1') then
                s_rx_vld_reg     <= (others => '0');
                s_rx_vld_sum_reg <= (others => '0');
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------
    -- BARREL SHIFTER
    ---------------------------------------------------------------------------

    bs_data_in_arr_g : for i in 0 to ITEMS-1 generate
        s_bs_data_in_arr(i)(0) <= s_rx_vld_reg(i);
        s_bs_data_in_arr(i)(1) <= s_rx_last_reg(i);
        s_bs_data_in_arr(i)(2+ITEM_WIDTH-1 downto 2) <= s_rx_data_arr_reg(i);
    end generate;

    bs_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => ITEMS,
        BLOCK_SIZE => BS_BLOCK_WIDTH,
        SHIFT_LEFT => true
    )
    port map (
        DATA_IN  => slv_array_ser(s_bs_data_in_arr,ITEMS,BS_BLOCK_WIDTH),
        DATA_OUT => s_bs_data_out,
        SEL      => s_bs_sel
    );

    s_bs_data_out_arr <= slv_array_deser(s_bs_data_out,ITEMS,BS_BLOCK_WIDTH);

    bs_data_out_arr_g : for i in 0 to ITEMS-1 generate
        s_bs_out_vld(i)      <= s_bs_data_out_arr(i)(0);
        s_bs_out_last(i)     <= s_bs_data_out_arr(i)(1);
        s_bs_out_data_arr(i) <= s_bs_data_out_arr(i)(2+ITEM_WIDTH-1 downto 2);
    end generate;

    ---------------------------------------------------------------------------
    -- REGISTERS & LOGIC
    ---------------------------------------------------------------------------

    -- calculate number of valid items in the output register next clock cycle
    --                              number of stored valid items + number of incoming valid items - number of sent items
    s_reg_vld_count_next <= resize((s_reg_vld_count              + s_rx_vld_sum_reg               - s_vld_out_sum),log2(ITEMS));

    -- make vector of valid items
    process (all)
    begin
        s_reg_vld_vector_next <= (others => '0');
        for i in 0 to ITEMS-1 loop
            if (s_reg_vld_count_next > i) then
                s_reg_vld_vector_next(i) <= '1';
            end if;
        end loop;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_reg_vld_count  <= (others => '0');
                s_reg_vld_vector <= (others => '0');
            else
                s_reg_vld_count  <= s_reg_vld_count_next;
                s_reg_vld_vector <= s_reg_vld_vector_next;
            end if;
        end if;
    end process;

    -- shift by the number of valid items in the output register
    s_bs_sel <= std_logic_vector(s_reg_vld_count);

    regs_g : for i in 0 to ITEMS-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_bs_out_vld(i) = '1') then
                s_reg_last(i) <= s_bs_out_last(i);
                s_reg_data(i) <= s_bs_out_data_arr(i);
                end if;
            end if;
        end process;
    end generate;

    out_arr_g : for i in 0 to ITEMS-1 generate
        --                   valid data from output register                or   barel shifter output data
        s_data_out_arr(i) <= s_reg_data(i) when (s_reg_vld_vector(i) = '1') else s_bs_out_data_arr(i);
        s_vld_out_arr(i)  <= s_reg_vld_vector(i) or s_bs_out_vld(i);
    end generate;

    -- number of valid output items
    process (all)
    begin
        s_vld_out_sum <= (others => '0');
        if (s_out_en = '1') then
            if (s_vld_out_arr(ITEMS-1) = '1') then
                s_vld_out_sum <= to_unsigned(ITEMS,s_vld_out_sum'length);
            else
                s_vld_out_sum <= resize(s_reg_vld_count,s_vld_out_sum'length);
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------
    -- FORCE WORD PUSH
    ---------------------------------------------------------------------------

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_timeout_cnt <= s_timeout_cnt + 1;
            if (RESET = '1' or TX_VLD(0) = '1') then
                s_timeout_cnt <= (others => '0');
            end if;
        end if;
    end process;

    process (all)
    begin
        s_last_of_burst <= '0';
        for i in 0 to ITEMS-1 loop
            if (s_reg_vld_vector(i) = '1') then
                s_last_of_burst <= s_reg_last(i);
            end if;
        end loop;
    end process;

    -- send incomplete word when time ran out and the word ends with EOF
    s_force_push <= s_timeout_cnt(4) and s_last_of_burst;

    ---------------------------------------------------------------------------
    -- OUTPUT
    ---------------------------------------------------------------------------
    -- enable output when all items are valid or time ran out

    s_out_en <= s_vld_out_arr(ITEMS-1) or s_force_push;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            TX_DATA <= slv_array_ser(s_data_out_arr,ITEMS,ITEM_WIDTH);
            TX_VLD  <= s_vld_out_arr and s_out_en;
            if (RESET = '1') then
                TX_VLD <= (others => '0');
            end if;
        end if;
    end process;

end architecture;
