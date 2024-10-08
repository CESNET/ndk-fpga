-- fp_merger.vhd: Simplified merger for FramePacker
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FP_MERGER is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;
        MFB_META_WIDTH      : natural := 0;

        -- Should be power of 2
        MERGER_INPUTS       : natural := 2;
        USR_RX_PKT_SIZE_MAX : natural := 2**10;
        DEVICE              : string  := "ULTRASCALE"
    );
    port(
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK : in std_logic;
        RST : in std_logic;

        -- =====================================================================
        -- Multiple input RX MFB interfaces
        -- =====================================================================
        RX_MFB_DATA    : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS -1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS -1 downto 0);

        -- =====================================================================
        -- Single output TX interface
        -- =====================================================================
        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of FP_MERGER is
    ------------------------------------------------------------
    --                    TYPE DECLARATION                    --
    ------------------------------------------------------------
    type fp_merger_fsm is (
        st_SKIP,    -- Skip current port
        st_PASS     -- Pass current port
    );

    ------------------------------------------------------------
    --                   SIGNAL DECLARATION                   --
    ------------------------------------------------------------
    signal state, next_state: fp_merger_fsm := st_SKIP;

    signal input_select             : unsigned(max(1, log2(MERGER_INPUTS)) - 1 downto 0);
    signal input_skip               : std_logic;
    signal input_valid              : unsigned(max(1, log2(MERGER_INPUTS)) - 1 downto 0);

    -- One-Hot
    signal input_select_oh          : std_logic_vector(MERGER_INPUTS - 1 downto 0);
    -- After one
    signal input_select_ao          : std_logic_vector(MERGER_INPUTS - 1 downto 0);

    -- Round up
    signal pipe_rx_eof_pos_arr      : slv_array_t(MFB_REGIONS - 1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal pipe_rx_eof_pos_round_up : slv_array_t(MFB_REGIONS - 1 downto 0)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);

    -- MFB interface
    signal pipe_rx_data             : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal pipe_rx_meta             : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal pipe_rx_sof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pipe_rx_eof              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal pipe_rx_sof_pos          : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    signal pipe_rx_eof_pos          : std_logic_vector(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
    signal pipe_rx_src_rdy          : std_logic;
    signal pipe_rx_dst_rdy          : std_logic;
begin

    -- Pointer select valid input
    pointer_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                input_select   <= (others => '0');
            elsif input_skip = '1' then
                input_select   <= input_valid;
            end if;
        end if;
    end process;

    process(all)
        variable input_select_oh_v  : std_logic_vector(MERGER_INPUTS - 1 downto 0);
    begin
        input_select_oh_v                           := (others => '0');
        input_select_oh_v(to_integer(input_select)) := '1';

        input_select_oh <= input_select_oh_v;
    end process;

    after_one_i : entity work.AFTER_ONE
    generic map(
        DATA_WIDTH  => MERGER_INPUTS
    )
    port map(
        DI  => input_select_oh,
        DO  => input_select_ao
    );

    -- Select next valid pointer
    pointer_sel_p: process(all)
        variable input_valid_v  : unsigned(max(1, log2(MERGER_INPUTS)) - 1 downto 0);
    begin
        input_valid_v := (others => '0');
        for i in 0 to MERGER_INPUTS - 1 loop
            if (RX_MFB_SRC_RDY(i) = '1') and (input_select_ao(i) = '1') then
                input_valid_v   := to_unsigned(i, input_valid_v'length);
                exit;
            end if;
        end loop;

        input_valid <= input_valid_v;
    end process;

    fp_merger_reg_p: process(CLK)
    begin
        if (rising_edge(CLK)) then
            if RST = '1' then
                state   <= st_SKIP;
            else
                state   <= next_state;
            end if;
        end if;
    end process;

    fp_merger_log_p: process(all)
        variable eof_std_v  : std_logic;
    begin
        next_state  <= state;
        input_skip  <= '0';

        eof_std_v   := or (RX_MFB_EOF(to_integer(input_select)));

        case(state) is
            when st_SKIP    =>
                if RX_MFB_SRC_RDY(to_integer(input_select)) = '1' then
                    next_state  <= st_PASS;
                    -- Small Packet
                    if (eof_std_v = '1') and (pipe_rx_dst_rdy = '1') then
                        next_state  <= st_SKIP;
                        input_skip  <= '1';
                    end if;
                else
                    input_skip  <= '1';
                end if;

            when st_PASS    =>
                if (eof_std_v = '1') and (pipe_rx_dst_rdy = '1') then
                    next_state  <= st_SKIP;
                    input_skip  <= '1';
                end if;

        end case;
    end process;

    -- Data MUX
    data_mux_i: entity work.GEN_MUX
    generic map(
        DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,
        MUX_WIDTH   => MERGER_INPUTS
    )
    port map(
        DATA_IN     => slv_array_ser(RX_MFB_DATA),
        SEL         => std_logic_vector(input_select),
        DATA_OUT    => pipe_rx_data
    );

    -- META MUX
    meta_mux_i: entity work.GEN_MUX
    generic map(
        DATA_WIDTH  => MFB_REGIONS*MFB_META_WIDTH,
        MUX_WIDTH   => MERGER_INPUTS
    )
    port map(
        DATA_IN     => slv_array_ser(RX_MFB_META),
        SEL         => std_logic_vector(input_select),
        DATA_OUT    => pipe_rx_meta
    );

    -- SOF MUX
    sof_mux_i: entity work.GEN_MUX
    generic map(
        DATA_WIDTH  => MFB_REGIONS,
        MUX_WIDTH   => MERGER_INPUTS
    )
    port map(
        DATA_IN     => slv_array_ser(RX_MFB_SOF),
        SEL         => std_logic_vector(input_select),
        DATA_OUT    => pipe_rx_sof
    );

    -- EOF MUX
    eof_mux_i: entity work.GEN_MUX
    generic map(
        DATA_WIDTH  => MFB_REGIONS,
        MUX_WIDTH   => MERGER_INPUTS
    )
    port map(
        DATA_IN     => slv_array_ser(RX_MFB_EOF),
        SEL         => std_logic_vector(input_select),
        DATA_OUT    => pipe_rx_eof
    );

    -- SOF_POS MUX
    sof_pos_mux_i: entity work.GEN_MUX
    generic map(
        DATA_WIDTH  => MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)),
        MUX_WIDTH   => MERGER_INPUTS
    )
    port map(
        DATA_IN     => slv_array_ser(RX_MFB_SOF_POS),
        SEL         => std_logic_vector(input_select),
        DATA_OUT    => pipe_rx_sof_pos
    );

    -- EOF_POS MUX
    eof_pos_mux_i: entity work.GEN_MUX
    generic map(
        DATA_WIDTH  => MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE),
        MUX_WIDTH   => MERGER_INPUTS
    )
    port map(
        DATA_IN     => slv_array_ser(RX_MFB_EOF_POS),
        SEL         => std_logic_vector(input_select),
        DATA_OUT    => pipe_rx_eof_pos
    );

    -- SRC_RDY MUX
    pipe_rx_src_rdy  <= RX_MFB_SRC_RDY(to_integer(input_select));

    -- DST_RDY DEMUX
    dst_rdy_demux_p: process(all)
        variable dst_rdy_v : std_logic_vector(MERGER_INPUTS -1 downto 0);
    begin
        dst_rdy_v                             := (others => '0');
        dst_rdy_v(to_integer(input_select))   := pipe_rx_dst_rdy;

        RX_MFB_DST_RDY  <= dst_rdy_v;
    end process;

    -- Packet round up
    pipe_rx_eof_pos_arr <= slv_array_deser(pipe_rx_eof_pos, MFB_REGIONS);
    round_up_g: for i in 0 to MFB_REGIONS - 1  generate
        pipe_rx_eof_pos_round_up(i) <= pipe_rx_eof_pos_arr(i)(log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE) - 1 downto log2(MFB_REGION_SIZE)) & "111";
    end generate;
    -- Output register
    out_reg_i: entity work.MFB_PIPE
    generic map(
        REGIONS        => MFB_REGIONS,
        REGION_SIZE    => MFB_REGION_SIZE,
        BLOCK_SIZE     => MFB_BLOCK_SIZE,
        ITEM_WIDTH     => MFB_ITEM_WIDTH,
        META_WIDTH     => MFB_META_WIDTH,

        PIPE_TYPE      => "SHREG",
        DEVICE         => DEVICE
    )
    port map(

        CLK    => CLK,
        RESET  => RST,

        RX_DATA       => pipe_rx_data,
        RX_META       => pipe_rx_meta,
        RX_SOF        => pipe_rx_sof,
        RX_EOF        => pipe_rx_eof,
        RX_SOF_POS    => pipe_rx_sof_pos,
        RX_EOF_POS    => slv_array_ser(pipe_rx_eof_pos_round_up),
        RX_SRC_RDY    => pipe_rx_src_rdy,
        RX_DST_RDY    => pipe_rx_dst_rdy,

        TX_DATA       => TX_MFB_DATA,
        TX_META       => TX_MFB_META,
        TX_SOF        => TX_MFB_SOF,
        TX_EOF        => TX_MFB_EOF,
        TX_SOF_POS    => TX_MFB_SOF_POS,
        TX_EOF_POS    => TX_MFB_EOF_POS,
        TX_SRC_RDY    => TX_MFB_SRC_RDY,
        TX_DST_RDY    => TX_MFB_DST_RDY
    );

end architecture;
