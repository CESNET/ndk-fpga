-- elastic_fifo.vhd: Elastic FIFO used to synchronize simmillar clock domains by
-- omitting or generating blocks, which are marked with log. '1' in MASK (idle blocks)
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity ELASTIC_FIFO is
    generic (

        -- Number of items in FIFO. The capacity should be raised with amount of clock cycles,
        -- when no idle blocks can be omitted or generated (no rate compensation can be done)
        FIFO_ITEMS          : natural := 16;

        -- FIFO RAM type - see asfifox.vhd for possible values
        FIFO_RAM_TYPE       : string := "LUT";

        DEVICE              : string := "ULTRASCALE";

        -- Determines how few data words must be left free
        -- for WR_AFULL to be triggered.
        ALMOST_FULL_OFFSET  : natural := FIFO_ITEMS/2;

        -- Determines how few data words must be stored for
        -- RD_AEMPTY to be triggered.
        ALMOST_EMPTY_OFFSET : natural := FIFO_ITEMS/2;

        -- FIFO enabled output registers allow better timing for a few flip-flops.
        FIFO_OUTPUT_REG     : boolean := True;

        -- Block width in bits, must be n-th power of 2, where n =  3, 4, 5, ...
        -- Elementary unit with which this component works
        BLOCK_WIDTH         : natural := 64;

        -- Number of blocks in data
        BLOCK_COUNT         : natural := 8;

        -- Generates output registers on output
        OUTPUT_REGISTERS    : boolean := false

    );
    port (
        -- Clock for data input
        WR_CLK              : in std_logic;
        -- Clock enable for data input
        WR_CE               : in std_logic;

        -- Clock for data output
        RD_CLK              : in std_logic;
        -- Clock enable for data output
        RD_CE               : in std_logic;

        -- Asynchronous reset
        AS_RST              : in std_logic;

        -- Data input, containing blocks
        DIN                 : in std_logic_vector(BLOCK_WIDTH * BLOCK_COUNT - 1 downto 0);

        -- Auxiliary data input, they are not considered as blocks, but are associated
        -- with them by position (block at 63th to 0th bit <=> aux_data at 7th to 0th bit)
        AUX_IN              : in std_logic_vector((BLOCK_WIDTH * BLOCK_COUNT / 8) - 1 downto 0);

        -- Tells which blocks don't have to be put into FIFO to compensate for
        -- faster input clock (log. "1" means, that block on that position can be omittted)
        MASK_IN             : in std_logic_vector(BLOCK_COUNT - 1 downto 0);

        -- Data output, containing blocks
        DOUT                : out std_logic_vector(BLOCK_WIDTH * BLOCK_COUNT - 1 downto 0);
        -- Auxiliary data output in association with DOUT - same association as AUX_IN
        AUX_OUT             : out std_logic_vector((BLOCK_WIDTH * BLOCK_COUNT / 8) - 1 downto 0)
    );
end entity;

architecture FULL of ELASTIC_FIFO is

    constant WR_RST_REPLICAS            : natural := 2;
    constant RD_RST_REPLICAS            : natural := 2;

    -- Data input width
    constant DIN_WIDTH                  : natural := BLOCK_WIDTH * BLOCK_COUNT;

    -- Auxiliary data width in relation with blocks, every bit belongs to a byte in blocks
    constant AUX_DATA_WIDTH             : natural := DIN_WIDTH / 8;

    -- FIFO data word width in bits
    constant FIFO_DATA_WIDTH            : natural := BLOCK_COUNT + DIN_WIDTH + AUX_DATA_WIDTH;

    signal wr_rst           : std_logic_vector(WR_RST_REPLICAS - 1 downto 0);
    signal rd_rst           : std_logic_vector(RD_RST_REPLICAS - 1 downto 0);

    -- Registers storing 1 clock cycle old data input
    signal wr_din_buff      : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal wr_aux_in_buff   : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);
    signal wr_mask_in_buff  : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    -- Registers storing actual data input
    signal wr_din_prebuff      : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal wr_aux_in_prebuff   : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);
    signal wr_mask_in_prebuff  : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    -- FIFO write interface
    signal fifo_wr_data     : std_logic_vector(FIFO_DATA_WIDTH - 1 downto 0);
    signal fifo_wr_en       : std_logic := '0';
    signal fifo_wr_full     : std_logic := '0';
    signal fifo_wr_afull    : std_logic := '0';
    signal fifo_wr_status   : std_logic_vector(max(log2(FIFO_ITEMS), 1) downto 0);

    -- FIFO read interface
    signal fifo_rd_data     : std_logic_vector(FIFO_DATA_WIDTH - 1 downto 0);
    signal fifo_rd_en       : std_logic := '0';
    signal fifo_rd_empty    : std_logic := '0';
    signal fifo_rd_aempty   : std_logic := '0';
    signal fifo_rd_status   : std_logic_vector(max(log2(FIFO_ITEMS), 1) downto 0);

    -- MUX select signal, for every block is one MUX which selects from (DIN & din_buff)
    signal mux_sel_i        : std_logic_vector(BLOCK_COUNT - 1 downto 0);
    signal mux_dout_i       : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal mux_auxo_i       : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);
    signal mux_mask_i       : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    -- MASK_IN & mask_in_buff, to check for more then 1 block long idle sequence,
    -- which can be ommited
    signal wr_mask_string   : std_logic_vector(BLOCK_COUNT * 2 - 1 downto 0);

    -- Relevant part of mask
    signal wr_mux_mask_out: std_logic_vector(BLOCK_COUNT downto 0);

    -- Vector where log. "1" at index i mean that there are log. "1" in wr_mask_string
    -- at i and i - 1
    signal wr_mask_idle_seq : std_logic_vector(BLOCK_COUNT downto 0);

    -- First log. "1" in wr_mask_idle_seq
    signal wr_mask_first_seq: std_logic_vector(BLOCK_COUNT downto 0);

    signal wr_data_mux_offset_neg   : std_logic_vector(BLOCK_COUNT downto 0);

    -- Contains log. "1" for every data MUX, which should be offseted
    signal wr_data_mux_offset_set   : std_logic_vector(BLOCK_COUNT downto 0);

    signal wr_data_string   : std_logic_vector(DIN_WIDTH * 2 - 1 downto 0);
    signal wr_auxin_string  : std_logic_vector(AUX_DATA_WIDTH * 2 - 1 downto 0);

    -- Output data buffer for storing unread data
    signal rd_dout_buff         : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal rd_auxo_buff         : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);
    signal rd_mask_buff         : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    -- Output buffer
    signal rd_dout_string       : std_logic_vector(DIN_WIDTH * 2 - 1 downto 0);
    signal rd_auxo_string       : std_logic_vector(AUX_DATA_WIDTH * 2 - 1 downto 0);
    signal rd_mask_string       : std_logic_vector(BLOCK_COUNT * 2 - 1 downto 0);

    -- Data which are going to go through insertion of idle block
    signal rd_data_mux_out_i    : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal rd_auxo_mux_out_i    : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);
    signal rd_mask_mux_out_i    : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    -- Idle block which can be inserted
    signal idle_block           : std_logic_vector(BLOCK_WIDTH - 1 downto 0);
    signal idle_aux_data        : std_logic_vector(BLOCK_WIDTH / 8 - 1 downto 0);

    -- Select for MUX which selects IDLE or data block
    signal rd_mux_idle_sel      : std_logic_vector(BLOCK_COUNT - 1 downto 0);
    -- Vector of accordingly shifted data
    signal rd_mux_idle_din      : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal rd_mux_idle_auxin    : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);

    -- Counter for number of inserted blocks
    signal rd_insert_cnt        : unsigned(log2(BLOCK_COUNT + 1) - 1 downto 0);
    -- Marks first idle in relevant data
    signal rd_first_idle        : std_logic_vector(BLOCK_COUNT - 1 downto 0);
    signal rd_first_idle_addr   : std_logic_vector(max(log2(BLOCK_COUNT), 1) - 1 downto 0);

    -- If MSB of this vector is 1, add 1 to rd_insert_cnt
    signal rd_shift_check           : std_logic_vector(BLOCK_COUNT - 1 downto 0);
     -- Tells which blocks are meant to be shifted by one block
    signal rd_blocks_to_shift       : std_logic_vector(BLOCK_COUNT - 1 downto 0);
    signal rd_shift_data_demux_out_i: std_logic_vector((BLOCK_COUNT - 1) * 2 * BLOCK_WIDTH - 1 downto 0);
    signal rd_shift_auxo_demux_out_i: std_logic_vector((BLOCK_COUNT - 1) * 2 * BLOCK_WIDTH / 8 - 1 downto 0);

    -- Tells where the first shifted block
    signal rd_first_shifted         : std_logic_vector(BLOCK_COUNT - 1 downto 0);

    -- Vectors with inserted data, put on OUT if desired by logic
    signal rd_inserted_dout         : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal rd_inserted_auxo         : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);

    signal data_out_signal          : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal aux_out_signal           : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);

    signal dout_reg                 : std_logic_vector(DIN_WIDTH - 1 downto 0);
    signal aux_out_reg              : std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);

    -- This signal tells if data are going to be shifted
    signal wr_shift                 : std_logic;

    signal wr_fsm_curr_state        : unsigned(max(log2(BLOCK_COUNT + 1), 1) - 1 downto 0);
    signal wr_fsm_next_state        : unsigned(max(log2(BLOCK_COUNT + 1), 1) - 1 downto 0);

    -- Tells how many blocks were shifted and its used to select relevant data
    signal wr_mux_base_offset       : unsigned(max(log2(BLOCK_COUNT + 1), 1) - 1 downto 0);
    -- This is FSM driven signal which tells when to write or skip current writing into FIFO
    signal wr_fsm_fifo_wr_en        : std_logic;

    signal rd_fsm_curr_state        : unsigned(max(log2(BLOCK_COUNT + 2), 1) - 1 downto 0);
    signal rd_fsm_next_state        : unsigned(max(log2(BLOCK_COUNT + 2), 1) - 1 downto 0);

    ---------------
    -- Functions --
    ---------------

    -- Reverses block order in data
    function reverse_data(to_reverse: in std_logic_vector(DIN_WIDTH - 1 downto 0)) return std_logic_vector is
        variable result: std_logic_vector(DIN_WIDTH - 1 downto 0);
    begin
        for i in 0 to BLOCK_COUNT - 1 loop
            result((BLOCK_COUNT - i) * BLOCK_WIDTH - 1 downto (BLOCK_COUNT - i - 1) * BLOCK_WIDTH) :=
            to_reverse((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH);
        end loop;
        return result;
    end;

    function reverse_aux_data(to_reverse: in std_logic_vector(AUX_DATA_WIDTH - 1 downto 0)) return std_logic_vector is
        variable result: std_logic_vector(AUX_DATA_WIDTH - 1 downto 0);
    begin
        for i in 0 to BLOCK_COUNT - 1 loop
            result((BLOCK_COUNT - i) * BLOCK_WIDTH / 8 - 1 downto (BLOCK_COUNT - i - 1) * BLOCK_WIDTH / 8) :=
            to_reverse((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8);
        end loop;
        return result;
    end;

    function reverse_mask(to_reverse: in std_logic_vector(BLOCK_COUNT - 1 downto 0)) return std_logic_vector is
        variable result: std_logic_vector(BLOCK_COUNT - 1 downto 0);
    begin
        for i in 0 to BLOCK_COUNT - 1 loop
            result((BLOCK_COUNT - i) - 1 downto BLOCK_COUNT - i - 1) :=
            to_reverse((i + 1) - 1 downto i);
        end loop;
        return result;
    end;

begin
    ----------------
    -- READ LOGIC --
    ----------------

    rd_dout_string <= fifo_rd_data(DIN_WIDTH - 1 downto 0) & rd_dout_buff;
    rd_auxo_string <= fifo_rd_data(FIFO_DATA_WIDTH - BLOCK_COUNT - 1 downto DIN_WIDTH) & rd_auxo_buff;
    rd_mask_string <= fifo_rd_data(FIFO_DATA_WIDTH - 1 downto FIFO_DATA_WIDTH - BLOCK_COUNT) & rd_mask_buff;

    rd_fsm_state_p : process(RD_CLK, RD_CE, rd_rst)
    begin
        if rising_edge(RD_CLK) then
            if rd_rst(1) then
                rd_fsm_curr_state <= (others => '0');
            elsif RD_CE = '1' then
                rd_fsm_curr_state <= rd_fsm_next_state;
            end if;
        end if;
    end process;

    -- Read FSN Next State + Mealy logic
    rd_fsm_next_state_p : process(all)
    begin
        if fifo_rd_aempty = '1' then
            if rd_fsm_curr_state = BLOCK_COUNT + 1 then
                if rd_shift_check(rd_shift_check'high) = '1' then
                    rd_fsm_next_state <= to_unsigned(1, rd_fsm_next_state'length);
                else
                    rd_fsm_next_state <= to_unsigned(0, rd_fsm_next_state'length);
                end if;
            elsif rd_fsm_curr_state = BLOCK_COUNT then
                rd_fsm_next_state <= rd_fsm_curr_state + 1;
            else
                if rd_shift_check(rd_shift_check'high) = '1' then
                    rd_fsm_next_state <= rd_fsm_curr_state + 1;
                else
                rd_fsm_next_state <= rd_fsm_curr_state;
                end if;
            end if;
        else
            rd_fsm_next_state <= rd_fsm_curr_state;
        end if;
    end process;

    -- Read FSM Moore logic
    rd_fsm_out_logic_p : process(all)
    begin
        fifo_rd_en <= RD_CE;
        rd_insert_cnt <= rd_fsm_curr_state(max(log2(BLOCK_COUNT + 1), 1) - 1 downto 0);

        if fifo_rd_aempty = '1' then
            if rd_fsm_curr_state = BLOCK_COUNT + 1 then
                if rd_shift_check(rd_shift_check'high) = '1' then
                    rd_insert_cnt <= (others => '0');
                    data_out_signal <= rd_inserted_dout;
                    aux_out_signal <= rd_inserted_auxo;
                else
                    rd_insert_cnt <= (others => '0');
                    data_out_signal <= rd_data_mux_out_i;
                    aux_out_signal <= rd_auxo_mux_out_i;
                end if;
            elsif rd_fsm_curr_state = BLOCK_COUNT then
                data_out_signal <= rd_data_mux_out_i;
                aux_out_signal <= rd_auxo_mux_out_i;
                fifo_rd_en <= '0';
            else
                if rd_shift_check(rd_shift_check'high) = '1' then
                    data_out_signal <= rd_inserted_dout;
                    aux_out_signal <= rd_inserted_auxo;
                else
                    data_out_signal <= rd_data_mux_out_i;
                    aux_out_signal <= rd_auxo_mux_out_i;
                end if;
            end if;
        else
            data_out_signal <= rd_data_mux_out_i;
            aux_out_signal <= rd_auxo_mux_out_i;
            if rd_fsm_curr_state = BLOCK_COUNT + 1 then
                rd_insert_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- Generation of output registers
    output_reg_g : if OUTPUT_REGISTERS generate
        output_reg_p : process(RD_CLK)
        begin
            if rising_edge(RD_CLK) then
                if RD_CE = '1' then
                    dout_reg <= data_out_signal;
                    aux_out_reg <= aux_out_signal;
                end if;
            end if;
        end process;

        DOUT <= dout_reg;
        AUX_OUT <= aux_out_reg;
    end generate;

    not_output_reg_g : if not OUTPUT_REGISTERS generate
        DOUT <= data_out_signal;
        AUX_OUT <= aux_out_signal;
    end generate;

    -- Finds first idle block in FIFO DOUT (1 hot)
    rd_first_idle_e : entity work.FIRST_ONE
    generic map (
        DATA_WIDTH => BLOCK_COUNT
    )
    port map (
        DI => rd_mask_mux_out_i,
        DO => rd_first_idle
    );

    -- Used for checking whether data were shifted
    rd_shift_check <= std_logic_vector(((unsigned(not rd_first_idle)) + 1));
    -- All block after first are shifted: 000100 -> 111000
    rd_blocks_to_shift <=  rd_shift_check xor rd_first_idle;

    -- Findes first block which was shifted (marks place where IDLE block will be inserted)
    rd_first_shifted_e : entity work.FIRST_ONE
    generic map (
        DATA_WIDTH => BLOCK_COUNT
    )
    port map (
        DI => rd_blocks_to_shift,
        DO => rd_first_shifted
    );

    rd_mux_idle_sel <= rd_first_shifted;
    -- 0th is never shifted thus it needs no DEMUX
    rd_mux_idle_din(BLOCK_WIDTH - 1 downto 0) <= rd_data_mux_out_i(BLOCK_WIDTH - 1 downto 0);
    rd_mux_idle_auxin(BLOCK_WIDTH / 8 - 1 downto 0) <= rd_auxo_mux_out_i(BLOCK_WIDTH / 8 - 1 downto 0);

    -- DEMUXes to shift blocks by 1 block if needed
    rd_shift_demux_g : for i in 1 to BLOCK_COUNT - 1 generate

        -- Data shifting
        rd_data_shift_demux_e : entity work.GEN_DEMUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH,
            DEMUX_WIDTH => 2,
            DEF_VALUE => '0'
        )
        port map(
            DATA_IN     => rd_data_mux_out_i((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH),
            SEL         => rd_blocks_to_shift(i downto i),
            DATA_OUT    => rd_shift_data_demux_out_i(i * 2 * BLOCK_WIDTH - 1 downto (i - 1) * 2 * BLOCK_WIDTH)
        );

        -- Auxiliary data shifting
        rd_auxo_shift_demux_e : entity work.GEN_DEMUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH / 8,
            DEMUX_WIDTH => 2,
            DEF_VALUE => '0'
        )
        port map(
            DATA_IN     => rd_auxo_mux_out_i((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8),
            SEL         => rd_blocks_to_shift(i downto i),
            DATA_OUT    => rd_shift_auxo_demux_out_i(i * 2 * BLOCK_WIDTH / 8 - 1 downto (i - 1) * 2 * BLOCK_WIDTH / 8)
        );

        -- The 1. block does not need or gate because the 0. block is never shifted
        first_block_or_g : if i = 1 generate
            rd_mux_idle_din((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH) <= rd_shift_data_demux_out_i(i * BLOCK_WIDTH - 1 downto 0);
            rd_mux_idle_auxin((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8) <= rd_shift_auxo_demux_out_i(i * BLOCK_WIDTH / 8 - 1 downto 0);
        end generate;

        other_blocks_or_g : if i > 1 generate
            rd_mux_idle_din((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH) <=
                                    rd_shift_data_demux_out_i(BLOCK_WIDTH * (i * 2 - 1) - 1 downto BLOCK_WIDTH * (i - 1) * 2) or
                                    rd_shift_data_demux_out_i(BLOCK_WIDTH * (i - 1) * 2 - 1 downto BLOCK_WIDTH * ((i - 1) * 2 - 1));
            rd_mux_idle_auxin((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8) <=
                                    rd_shift_auxo_demux_out_i((BLOCK_WIDTH / 8) * (i * 2 - 1) - 1 downto (BLOCK_WIDTH / 8) * (i - 1) * 2) or
                                    rd_shift_auxo_demux_out_i((BLOCK_WIDTH / 8) * (i - 1) * 2 - 1 downto (BLOCK_WIDTH / 8) * ((i - 1) * 2 - 1));
        end generate;

    end generate;

    -- Converts 1 hot code into binary for selection of idle block which can be inserted
    rd_mux_get_idle_sel_enc_e : entity work.GEN_ENC
    generic map (
        ITEMS   => BLOCK_COUNT,
        DEVICE  => DEVICE
    )
    port map (
        DI      => rd_first_idle,
        ADDR    => rd_first_idle_addr
    );

    -- From selected blocks selects and idle block which can be inserted into data
    rd_mux_get_idle_e : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => BLOCK_WIDTH,
        MUX_WIDTH => BLOCK_COUNT
    )
    port map(
        DATA_IN     => rd_data_mux_out_i,
        SEL         => rd_first_idle_addr,
        DATA_OUT    => idle_block
    );

    rd_mux_get_idle_aux_e : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => BLOCK_WIDTH / 8,
        MUX_WIDTH => BLOCK_COUNT
    )
    port map(
        DATA_IN     => rd_auxo_mux_out_i,
        SEL         => rd_first_idle_addr,
        DATA_OUT    => idle_aux_data
    );

    -- Places and IDLE blocks and IDLE auxiliary data where data were not written (skipped block)
    rd_mux_idle_g : for i in 0 to BLOCK_COUNT - 1 generate

        -- Idle data block
        rd_idle_data_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH,
            MUX_WIDTH => 2
        )
        port map(
            DATA_IN     => idle_block &
                           rd_mux_idle_din((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH),
            SEL         => rd_mux_idle_sel(i downto i),
            DATA_OUT    => rd_inserted_dout((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH)
        );

        -- Idle auxiliary data
        rd_idle_auxo_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH / 8,
            MUX_WIDTH => 2
        )
        port map(
            DATA_IN     => idle_aux_data &
                           rd_mux_idle_auxin((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8),
            SEL         => rd_mux_idle_sel(i downto i),
            DATA_OUT    => rd_inserted_auxo((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8)
        );

    end generate;

    -- These MUXes select blocks and their auxiliary data that into which will be (if possible)
    -- an idle block inserted based on count of already inserted blocks
    rd_data_mux_g : for i in 0 to BLOCK_COUNT - 1 generate
        rd_dout_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH,
            MUX_WIDTH => BLOCK_COUNT + 1
        )
        port map(
            DATA_IN     => reverse_data(rd_dout_string((BLOCK_COUNT + i) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH)) &
                           rd_dout_string((BLOCK_COUNT + i + 1) * BLOCK_WIDTH - 1  downto (BLOCK_COUNT + i) * BLOCK_WIDTH),
            SEL         => std_logic_vector(rd_insert_cnt),
            DATA_OUT    => rd_data_mux_out_i((i + 1) * BLOCK_WIDTH - 1 downto i * BLOCK_WIDTH)
        );

        rd_auxo_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH / 8,
            MUX_WIDTH => BLOCK_COUNT + 1
        )
        port map (
            DATA_IN     => reverse_aux_data(rd_auxo_string((BLOCK_COUNT + i) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8)) &
                           rd_auxo_string((BLOCK_COUNT + i + 1) * BLOCK_WIDTH / 8 - 1 downto (BLOCK_COUNT + i) * BLOCK_WIDTH / 8),
            SEL         => std_logic_vector(rd_insert_cnt),
            DATA_OUT    => rd_auxo_mux_out_i((i + 1) * BLOCK_WIDTH / 8 - 1 downto i * BLOCK_WIDTH / 8)
        );

        rd_mask_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => 1,
            MUX_WIDTH => BLOCK_COUNT + 1
        )
        port map (
            DATA_IN     => reverse_mask(rd_mask_string((BLOCK_COUNT + i) - 1 downto i)) &
                           rd_mask_string((BLOCK_COUNT + i + 1) - 1 downto BLOCK_COUNT + i),
            SEL         => std_logic_vector(rd_insert_cnt),
            DATA_OUT    => rd_mask_mux_out_i((i + 1) - 1 downto i)
        );
    end generate;

    rd_dout_buff_p : process(RD_CLK)
    begin
        if rising_edge(RD_CLK) then
            if fifo_rd_en = '1' then
                rd_dout_buff <= fifo_rd_data(DIN_WIDTH - 1 downto 0);
            end if;
        end if;
    end process;

    rd_aux_buff_p : process(RD_CLK)
    begin
        if rising_edge(RD_CLK) then
            if fifo_rd_en = '1' then
                rd_auxo_buff <= fifo_rd_data(FIFO_DATA_WIDTH - BLOCK_COUNT - 1 downto DIN_WIDTH);
            end if;
        end if;
    end process;

    rd_mask_buff_p : process(RD_CLK)
    begin
        if rising_edge(RD_CLK) then
            if fifo_rd_en = '1' then
                rd_mask_buff <= fifo_rd_data(FIFO_DATA_WIDTH - 1 downto FIFO_DATA_WIDTH - BLOCK_COUNT);
            end if;
        end if;
    end process;


    -----------------
    -- WRITE LOGIC --
    -----------------

    wr_fsm_state_p : process(WR_CLK, wr_rst)
    begin
        if rising_edge(WR_CLK) then
            if wr_rst(1) then
                wr_fsm_curr_state <= (others => '0');
            elsif WR_CE = '1' then
                wr_fsm_curr_state <= wr_fsm_next_state;
            end if;
        end if;
    end process;

    wr_fsm_next_state_p : process(wr_fsm_curr_state, wr_shift, fifo_wr_en, WR_CE)
    begin
        if wr_fsm_curr_state = BLOCK_COUNT then
            wr_fsm_next_state <= (others => '0');
        else
            if (wr_shift = '1' and fifo_wr_en = '1') then
                wr_fsm_next_state <= wr_fsm_curr_state + 1;
            else
                wr_fsm_next_state <= wr_fsm_curr_state;
            end if;
        end if;
    end process;

    wr_fsm_out_logic_p : process(wr_fsm_curr_state)
    begin
        wr_fsm_fifo_wr_en <= '1';
        wr_mux_base_offset <= wr_fsm_curr_state;

        if wr_fsm_curr_state = BLOCK_COUNT then
            wr_fsm_fifo_wr_en <= '0';
        end if;
    end process;

    -- Joined 1 clock old input with actual input
    wr_mask_string <= wr_mask_in_prebuff & wr_mask_in_buff;
    wr_data_string <= wr_din_prebuff & wr_din_buff;
    wr_auxin_string <= wr_aux_in_prebuff & wr_aux_in_buff;

    -- Sets mux select to 1 if mux has to be shifted
    wr_data_mux_offset_g : for i in 1 to BLOCK_COUNT generate
        mux_sel_i(i - 1) <= '1' when wr_data_mux_offset_set(i) = '1' and fifo_wr_afull = '1' else '0';
    end generate;

    -- Select relevant part of mask
    wr_mux_mask_g : for i in BLOCK_COUNT downto 0 generate
        wr_mask_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => 1,
            MUX_WIDTH => BLOCK_COUNT
        )
        port map(
            DATA_IN     => wr_mask_string(BLOCK_COUNT + i - 1 downto i),
            SEL         => std_logic_vector(wr_mux_base_offset(max(log2(BLOCK_COUNT), 1) - 1 downto 0)),
            DATA_OUT    => wr_mux_mask_out(i downto i)
        );
    end generate;

    -- Finds sequence of "11" and into new vector places "10"
    wr_idle_seq_g : for i in BLOCK_COUNT downto 1 generate
        wr_mask_idle_seq(i) <= '1' when wr_mux_mask_out(i downto i - 1) = "11" else '0';
        wr_mask_idle_seq(0) <= '0';
    end generate;

    -- Finds the first sequence of "11"
    wr_idle_seq_fone_e : entity work.FIRST_ONE
    generic map (
        DATA_WIDTH => BLOCK_COUNT + 1
    )
    port map (
        DI => wr_mask_idle_seq,
        DO => wr_mask_first_seq
    );

    -- Fills every bit in vector after first log. "1"
    wr_data_mux_offset_neg <= not wr_mask_first_seq;
    wr_data_mux_offset_set <= std_logic_vector(unsigned(wr_data_mux_offset_neg) + 1);

    fifo_wr_data <= mux_mask_i & mux_auxo_i & mux_dout_i;

    fifo_wr_en <= WR_CE and wr_fsm_fifo_wr_en;

    wr_shift <= '1' when not (wr_mask_first_seq = (wr_mask_first_seq'range => '0')) and fifo_wr_afull = '1' else '0';

    -- DIN buffer
    wr_din_buff_p : process(WR_CLK)
    begin
        if rising_edge(WR_CLK) then
            if WR_CE = '1' then
                wr_din_prebuff <= DIN;
                wr_din_buff <= wr_din_prebuff;
            end if;
        end if;
    end process;

    -- AUX_IN buffer
    wr_aux_in_buff_p : process(WR_CLK)
    begin
        if rising_edge(WR_CLK) then
            if WR_CE = '1' then
                wr_aux_in_prebuff <= AUX_IN;
                wr_aux_in_buff <= wr_aux_in_prebuff;
            end if;
        end if;
    end process;

    -- MASK_IN buffer
    wr_mask_in_buff_p : process(WR_CLK)
    begin
        if rising_edge(WR_CLK) then
            if WR_CE = '1' then
                wr_mask_in_prebuff <= MASK_IN;
                wr_mask_in_buff <= wr_mask_in_prebuff;
            end if;
        end if;
    end process;

    wr_mux_data_g : for i in 0 to BLOCK_COUNT - 1 generate

        -- MUX which selects blocks from data string
        -- Every MUXi is in offset to MUX(i-1) by one block
        wr_data_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH,
            MUX_WIDTH => BLOCK_COUNT + 1
        )
        port map (
            DATA_IN     => wr_data_string(DIN_WIDTH + BLOCK_WIDTH * (i + 1) - 1 downto BLOCK_WIDTH * i),
            SEL         => std_logic_vector(wr_mux_base_offset + unsigned(mux_sel_i(i downto i))),
            DATA_OUT    => mux_dout_i(BLOCK_WIDTH * (i + 1) - 1 downto BLOCK_WIDTH * i)
        );

        wr_auxin_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => BLOCK_WIDTH / 8,
            MUX_WIDTH => BLOCK_COUNT + 1
        )
        port map (
            DATA_IN     => wr_auxin_string(AUX_DATA_WIDTH + (i + 1) * (BLOCK_WIDTH / 8) - 1 downto i * BLOCK_WIDTH / 8),
            SEL         => std_logic_vector(wr_mux_base_offset + unsigned(mux_sel_i(i downto i))),
            DATA_OUT    => mux_auxo_i((BLOCK_WIDTH / 8) * (i + 1) - 1 downto (BLOCK_WIDTH / 8) * i)
        );

        wr_maskin_mux_e : entity work.GEN_MUX
        generic map (
            DATA_WIDTH => 1,
            MUX_WIDTH => BLOCK_COUNT + 1
        )
        port map (
            DATA_IN     => wr_mask_string(BLOCK_COUNT + (i + 1) - 1 downto i),
            SEL         => std_logic_vector(wr_mux_base_offset + unsigned(mux_sel_i(i downto i))),
            DATA_OUT    => mux_mask_i(i downto i)
        );

    end generate;

    -- Reset synchronization into write clock domain
    wr_async_rst_e : entity work.ASYNC_RESET
    generic map (
        TWO_REG     => false,
        OUT_REG     => false,
        REPLICAS    => WR_RST_REPLICAS
    )
    port map (
        CLK => WR_CLK,
        ASYNC_RST => AS_RST,
        OUT_RST => wr_rst
    );

    -- Reset synchronization into read clock domain
    rd_async_rst_e : entity work.ASYNC_RESET
    generic map (
        TWO_REG     => false,
        OUT_REG     => false,
        REPLICAS    => RD_RST_REPLICAS
    )
    port map (
        CLK => RD_CLK,
        ASYNC_RST => AS_RST,
        OUT_RST => rd_rst
    );

    -- Asynchronous FIFO instance
    asfifox_e : entity work.ASFIFOX
    generic map (
        DATA_WIDTH          => FIFO_DATA_WIDTH,
        ITEMS               => FIFO_ITEMS,
        RAM_TYPE            => FIFO_RAM_TYPE,
        FWFT_MODE           => true,
        OUTPUT_REG          => FIFO_OUTPUT_REG,
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
        ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
    )
    port map (
        WR_CLK => WR_CLK,
        WR_RST => wr_rst(0),
        WR_DATA => fifo_wr_data,
        WR_EN => fifo_wr_en,
        WR_FULL => fifo_wr_full,
        WR_AFULL => fifo_wr_afull,
        WR_STATUS => fifo_wr_status,
        RD_CLK => RD_CLK,
        RD_RST => rd_rst(0),
        RD_DATA => fifo_rd_data,
        RD_EN => fifo_rd_en,
        RD_EMPTY => fifo_rd_empty,
        RD_AEMPTY => fifo_rd_aempty,
        RD_STATUS => fifo_rd_status
    );

end architecture;
