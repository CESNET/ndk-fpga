-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- ===========================================================================
--  Description
-- ===========================================================================

-- This component concatenates two AXI Stream packets into one output packet.
-- The packet from RX0 is transmitted first, followed immediately by the packet from RX1.
--
-- Operation:
-- 1. RX0 packet is forwarded unchanged until its last word.
-- 2. If RX0's last word is not completely filled (not all bytes valid), RX1 data
--    is shifted to fill the remaining bytes of that word.
-- 3. Subsequent RX1 words are shifted by the same amount.
-- 4. The concatenated packet is output on TX_AXIS.
--
-- ..warning::
--
--    For each packet on RX0, a corresponding packet on RX1 must be available.
--    It will wait forever otherwise.
--
-- This component is useful for appending headers or metadata to packets.
-- Guaranteed throughput: 1 word per clock cycle when both inputs are sufficiently fed.
--
entity AXIS_PACKET_CONCATENATOR is
    generic (
        -- Width of AXI-Stream data signal in bits.
        TDATA_WIDTH   : natural := 512;
        -- Target device: AGILEX, STRATIX10, ULTRASCALE, ...
        DEVICE        : string  := "AGILEX"
    );
    port (
        -- =========================================================================
        -- Clock and reset signals
        -- =========================================================================
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =========================================================================
        -- RX0 AXI-Stream interface
        -- =========================================================================
        RX0_AXIS_TDATA  : in  std_logic_vector(TDATA_WIDTH-1 downto 0);
        RX0_AXIS_TKEEP  : in  std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        RX0_AXIS_TLAST  : in  std_logic;
        RX0_AXIS_TVALID : in  std_logic;
        RX0_AXIS_TREADY : out std_logic;

        -- =========================================================================
        -- RX1 AXI-Stream interface
        -- =========================================================================
        RX1_AXIS_TDATA  : in  std_logic_vector(TDATA_WIDTH-1 downto 0);
        RX1_AXIS_TKEEP  : in  std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        RX1_AXIS_TLAST  : in  std_logic;
        RX1_AXIS_TVALID : in  std_logic;
        RX1_AXIS_TREADY : out std_logic;

        -- =========================================================================
        -- TX AXI-Stream interface
        -- =========================================================================
        TX_AXIS_TDATA  : out std_logic_vector(TDATA_WIDTH-1 downto 0);
        TX_AXIS_TKEEP  : out std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        TX_AXIS_TLAST  : out std_logic;
        TX_AXIS_TVALID : out std_logic;
        TX_AXIS_TREADY : in  std_logic
    );
end entity;

architecture FULL of AXIS_PACKET_CONCATENATOR is

    -- =========================================================================
    --                                CONSTANTS
    -- =========================================================================

    constant DATA_BYTES : natural := TDATA_WIDTH/8;
    constant BS_BLOCKS  : natural := 2*DATA_BYTES;
    constant BS_BLOCK_W : natural := 8+1; -- A byte of data concatenated with 1 bit from last_1hot.
    constant BS_DATA_W  : natural := BS_BLOCKS*BS_BLOCK_W;

    -- =========================================================================
    --                                 SIGNALS
    -- =========================================================================

    -- FSM states:
    -- ST_SEND_RX0     : Forwarding RX0 packet unchanged
    -- ST_SEND_RX0_RX1 : Concatenating RX0's last word with RX1's first word
    -- ST_SEND_RX1     : Forwarding shifted RX1 data
    type fsm_t is (ST_SEND_RX0, ST_SEND_RX0_RX1, ST_SEND_RX1);

    signal fsm_pstate                : fsm_t;
    signal fsm_nstate                : fsm_t;

    signal rx0_ready                 : std_logic;
    signal rx1_ready                 : std_logic;

    signal rx0_data_reg              : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal rx0_keep_reg              : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx0_last_reg              : std_logic;
    signal rx0_valid_reg             : std_logic;
    signal rx1_data_reg              : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal rx1_keep_reg              : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx1_last_reg              : std_logic;
    signal rx1_valid_reg             : std_logic;

    signal rx0_all_valid             : std_logic;
    signal rx0_all_valid_reg         : std_logic;
    signal rx0_last_complete         : std_logic;
    signal rx0_last_complete_reg     : std_logic;
    signal rx1_last_complete         : std_logic;
    signal rx1_packet_ending         : std_logic;
    signal rx0_packet_end_pending    : std_logic;
    signal rx0_short_in_reg          : std_logic;
    signal rx1_packet_ending_reg     : std_logic;
    signal rx1_keep_ones_reg         : natural range 0 to DATA_BYTES;

    signal rx0_last_valid_byte       : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx0_last_valid_byte_enc   : std_logic_vector(log2(DATA_BYTES)-1 downto 0);
    signal rx1_start_byte_pos        : std_logic_vector(log2(BS_BLOCKS)-1 downto 0);
    signal rx1_start_byte_pos_reg    : std_logic_vector(log2(BS_BLOCKS)-1 downto 0);
    signal new_bs_shift_en           : std_logic;
    signal new_bs_shift_src          : std_logic;
    signal rx1_packet_ending_reg_en  : std_logic;

    signal rx1_last_valid_byte       : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx1_last_valid_byte_reg   : std_logic_vector(DATA_BYTES-1 downto 0);

    signal bs_din                    : std_logic_vector(BS_DATA_W-1 downto 0);
    signal bs_shift                  : std_logic_vector(log2(BS_BLOCKS)-1 downto 0);
    signal bs_dout                   : std_logic_vector(BS_DATA_W-1 downto 0);

    signal bs_dout_blocks            : slv_array_t(BS_BLOCKS-1 downto 0)(BS_BLOCK_W-1 downto 0);
    signal rx1_shifted_last_1hot     : std_logic_vector(BS_BLOCKS-1 downto 0);
    signal rx1_shifted_data          : slv_array_t(BS_BLOCKS-1 downto 0)(8-1 downto 0);
    signal rx1_shifted_last_1hot_top : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx1_shifted_last_1hot_bot : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx1_shifted_data_top      : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal rx1_shifted_data_bot      : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal rx1_shifted_data_top_reg  : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);

    signal block_ptr                 : natural range 0 to DATA_BYTES-1;
    signal keep_ptr                  : integer range 0 to BS_BLOCKS-1;
    signal keep_ptr_reg              : integer range 0 to DATA_BYTES-1;

    signal s_tx_axis_tdata           : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal s_tx_axis_tkeep           : std_logic_vector(DATA_BYTES-1 downto 0);
    signal s_tx_axis_tlast           : std_logic;
    signal s_tx_axis_tvalid          : std_logic;

begin

    -- =========================================================================
    --  RX ready signals
    -- =========================================================================

    RX0_AXIS_TREADY <= TX_AXIS_TREADY and rx0_ready;
    RX1_AXIS_TREADY <= TX_AXIS_TREADY and rx1_ready;

    -- =========================================================================
    --  Input registers
    -- =========================================================================

    input_reg0_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RX0_AXIS_TREADY = '1') then
                rx0_data_reg           <= slv_array_deser(RX0_AXIS_TDATA, DATA_BYTES);
                rx0_keep_reg           <= RX0_AXIS_TKEEP;
                rx0_last_reg           <= RX0_AXIS_TLAST;
                rx0_valid_reg          <= RX0_AXIS_TVALID;
                rx0_all_valid_reg      <= rx0_all_valid;

                rx0_last_complete_reg  <= rx0_last_complete;
                rx1_start_byte_pos_reg <= rx1_start_byte_pos;
            end if;
            if (RESET = '1') then
                rx0_valid_reg         <= '0';
                rx0_last_complete_reg <= '0';
            end if;
        end if;
    end process;

    input_reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RX1_AXIS_TREADY = '1') then
                rx1_data_reg            <= slv_array_deser(RX1_AXIS_TDATA, DATA_BYTES);
                rx1_keep_reg            <= RX1_AXIS_TKEEP;
                rx1_last_reg            <= RX1_AXIS_TLAST;
                rx1_valid_reg           <= RX1_AXIS_TVALID;

                rx1_keep_ones_reg       <= count_ones(RX1_AXIS_TKEEP);
                rx1_last_valid_byte_reg <= rx1_last_valid_byte;
            end if;
            if (RESET = '1') then
                rx1_valid_reg           <= '0';
                rx1_last_valid_byte_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- =========================================================================
    --  FSM
    -- =========================================================================

    -- Detect if all bytes are valid in the last word
    rx0_all_valid          <= and RX0_AXIS_TKEEP;
    -- RX0 last word is complete => all bytes in the last word are valid.
    rx0_last_complete      <= rx0_all_valid and RX0_AXIS_TLAST and RX0_AXIS_TVALID;
    -- RX1 last word is complete => all bytes in the last word were able to fit into this word.
    rx1_last_complete      <= or rx1_shifted_last_1hot_bot;
    -- Validated rx1_last_complete.
    rx1_packet_ending      <= rx1_last_complete and rx1_last_reg and rx1_valid_reg;
    -- A packet's last word is arriving on RX0 and not all of its bytes are valid.
    rx0_packet_end_pending <= RX0_AXIS_TVALID and RX0_AXIS_TLAST and not rx0_all_valid;
    -- A one-word-long packet is preloaded in rx0_reg.
    rx0_short_in_reg       <= not rx0_all_valid_reg and rx0_last_reg;

    fsm_state_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_AXIS_TREADY = '1') then
                fsm_pstate <= fsm_nstate;
            end if;
            if (RESET = '1') then
                fsm_pstate <= ST_SEND_RX0;
            end if;
        end if;
    end process;

    fsm_state_transitions_p : process (all)
    begin
        case (fsm_pstate) is
            -- Forward complete words from RX0.
            when ST_SEND_RX0 =>
                if ((rx0_last_reg = '1') and (rx0_valid_reg = '1')) then
                    -- When the last word on RX0 has all bytes valid, we stay in ST_SEND_RX0 one more clock cycle
                    -- and then need to go straight to ST_SEND_RX1.
                    fsm_nstate <= ST_SEND_RX1;
                elsif ((RX0_AXIS_TVALID = '1') and (RX0_AXIS_TLAST = '1') and (rx0_all_valid = '0')) then
                    -- A packet's last word is arriving on RX0.
                    -- Need to complete this word with bytes from a packet data on RX1 or rx1_reg.
                    fsm_nstate <= ST_SEND_RX0_RX1;
                else
                    -- Stay in this state: if the last word is pending on RX0 and all its bytes are valid (tkeep = others => '1') OR
                    -- a non-last word OR an invalid word is pending.
                    fsm_nstate <= ST_SEND_RX0;
                end if;

            -- Fill the rest from the last word on RX0 with data from the first word on RX1.
            when ST_SEND_RX0_RX1 =>
                if (rx1_valid_reg = '0') then
                    -- Waiting for valid data on RX1
                    fsm_nstate <= ST_SEND_RX0_RX1;
                elsif ((rx1_last_complete = '0') or (rx1_last_reg = '0')) then
                    -- A longer-than-word packet is ready in rx1_reg.
                    fsm_nstate <= ST_SEND_RX1;
                elsif (rx0_packet_end_pending = '1') then
                    -- A short (less-than-word) packet in rx1_reg fits into the last word whole (no remainder).
                    -- Return to this state due to a short packet arriving on RX0.
                    fsm_nstate <= ST_SEND_RX0_RX1;
                else
                    -- A short (less-than-word) packet in rx1_reg fits into the last word whole (no remainder).
                    -- Return to default state.
                    fsm_nstate <= ST_SEND_RX0;
                end if;

            -- Transmit data from RX1, shifted as necessary.
            when ST_SEND_RX1 =>
                if (rx1_packet_ending = '0' and rx1_packet_ending_reg = '0') then
                    -- RX1 packet continues
                    fsm_nstate <= ST_SEND_RX1;
                elsif ((rx0_short_in_reg = '1') or (rx0_valid_reg = '0' and rx0_packet_end_pending = '1')) then
                    -- RX1 packet is ending and: a short (less-than-word) packet is preloaded in rx0_reg OR
                    -- rx0_reg is invalid but a short packet is on RX0.
                    fsm_nstate <= ST_SEND_RX0_RX1;
                else
                    -- RX1 packet is ending and: a preloaded packet in rx0_reg is at least a full word long OR
                    -- is arriving on RX0 OR there are no valid data yet.
                    fsm_nstate <= ST_SEND_RX0;
                end if;

        end case;
    end process;

    fsm_state_logic_p : process (all)
    begin
        case (fsm_pstate) is

            when ST_SEND_RX0 =>
                new_bs_shift_en          <= '1';
                -- New value for bs_shift can come from two sources: rx1_start_byte_pos_reg and rx1_start_byte_pos.
                -- 0: stage 0 (the input), 1: stage 1 (the input register)
                new_bs_shift_src         <= rx0_last_reg and rx0_valid_reg;
                -- rx1_packet_ending_reg could assert when the packet's last word on RX0 was arriving and a shorter-than-word packet was in rx1_reg.
                rx1_packet_ending_reg_en <= '0';

                rx0_ready <= '1';
                rx1_ready <= not rx1_valid_reg;

                s_tx_axis_tdata  <= rx0_data_reg;
                s_tx_axis_tkeep  <= rx0_keep_reg;
                s_tx_axis_tlast  <= '0';
                s_tx_axis_tvalid <= rx0_valid_reg;

            when ST_SEND_RX0_RX1 =>
                -- Even if the end of the last word on RX1 overflows into the next word,
                -- it will already be after the last shift -> we can store a new bs_shift.
                new_bs_shift_en          <= (rx1_last_reg and rx1_valid_reg and rx1_last_complete) or rx1_packet_ending_reg;
                -- New value for bs_shift can come from two sources: rx1_start_byte_pos_reg and rx1_start_byte_pos.
                -- 0: stage 0 (the input), 1: stage 1 (the input register)
                new_bs_shift_src         <= '0';
                rx1_packet_ending_reg_en <= '1';

                rx0_ready <= rx1_valid_reg; -- Load a new word to get rid of the last word (only when there is valid data in RX0).
                rx1_ready <= '1';

                for db in 0 to DATA_BYTES-1 loop
                    s_tx_axis_tdata(db) <= rx0_data_reg(db) when (db < block_ptr) else rx1_shifted_data_bot(db);
                    s_tx_axis_tkeep(db) <= '1'              when (db < keep_ptr ) else '0';
                end loop;
                s_tx_axis_tlast  <= rx1_last_complete and rx1_last_reg;
                s_tx_axis_tvalid <= rx0_valid_reg and rx1_valid_reg;

            when ST_SEND_RX1 =>
                -- Even if the end of the last word on RX1 overflows into the next word,
                -- it will already be after the last shift -> we can store a new bs_shift.
                new_bs_shift_en          <= (rx1_last_reg and rx1_valid_reg and rx1_last_complete) or rx1_packet_ending_reg;
                -- New value for bs_shift can come from two sources:
                -- 0: stage 0 (the input, rx1_start_byte_pos), 1: stage 1 (the input register, rx1_start_byte_pos_reg).
                new_bs_shift_src         <= rx0_last_reg and rx0_valid_reg;
                rx1_packet_ending_reg_en <= '1';

                rx0_ready <= not rx0_valid_reg;
                rx1_ready <= not rx1_packet_ending_reg;

                for db in 0 to DATA_BYTES-1 loop
                    s_tx_axis_tdata(db) <= rx1_shifted_data_top_reg(db) when (db < block_ptr) else rx1_shifted_data_bot(db);
                    s_tx_axis_tkeep(db) <= '1'                          when (db < keep_ptr ) else '0';
                end loop;
                s_tx_axis_tlast  <= (rx1_last_complete and rx1_last_reg) or rx1_packet_ending_reg;
                s_tx_axis_tvalid <= rx1_valid_reg or rx1_packet_ending_reg;

        end case;
    end process;

    block_ptr <= to_integer(unsigned(bs_shift));
    keep_ptr  <= block_ptr + rx1_keep_ones_reg when (rx1_packet_ending_reg = '0') else keep_ptr_reg;

    -- =========================================================================
    --  Shifting RX1 logic
    -- =========================================================================

    -- --------------------------------------------------------
    -- Calculate shift amount based on RX0 last word byte count.
    -- --------------------------------------------------------
    rx0_last_one_i : entity work.LAST_ONE
    generic map (
        DATA_WIDTH => DATA_BYTES
    )
    port map (
        DI => RX0_AXIS_TKEEP,
        DO => rx0_last_valid_byte
    );

    -- Convert one-hot encoded last byte position to binary address.
    rx0_last_one_enc_i : entity work.GEN_ENC
    generic map (
        ITEMS  => DATA_BYTES,
        DEVICE => DEVICE
    )
    port map (
        DI   => rx0_last_valid_byte,
        ADDR => rx0_last_valid_byte_enc
    );

    rx1_start_byte_pos <= std_logic_vector(resize(unsigned(rx0_last_valid_byte_enc)+1, log2(BS_BLOCKS)));

    bs_shift_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((new_bs_shift_en = '1') and (TX_AXIS_TREADY = '1')) then
                -- There may be a valid End-of-packet preloaded in the register.
                if (new_bs_shift_src = '1') then
                    bs_shift <= rx1_start_byte_pos_reg;
                else
                    bs_shift <= rx1_start_byte_pos;
                end if;
            end if;
            if (RESET = '1') then
                bs_shift <= (others => '0');
            end if;
        end if;
    end process;

    -- --------------------------------------------------------
    -- Get the packet's end position, shift it, and set Last in the right word.
    -- --------------------------------------------------------
    rx1_last_one_i : entity work.LAST_ONE
    generic map (
        DATA_WIDTH => DATA_BYTES
    )
    port map (
        DI => RX1_AXIS_TKEEP,
        DO => rx1_last_valid_byte
    );

    -- --------------------------------------------------------
    -- Shift data on RX1 (with Last Valid Byte indicator).
    --
    -- The shifter interfaces are twice as wide to easily
    -- detect an overflow into the next word.
    -- Optimization to use normal interface width possible.
    -- --------------------------------------------------------

    bs_din(BS_DATA_W  -1 downto BS_DATA_W/2) <= (others => '0');
    bs_din(BS_DATA_W/2-1 downto           0) <= slv_array_ser(concat_arr(rx1_data_reg, rx1_last_valid_byte_reg));

    -- Shift RX1 data
    rx1_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => BS_BLOCKS,
        BLOCK_SIZE => BS_BLOCK_W,
        SHIFT_LEFT => true
    )
    port map (
        DATA_IN  => bs_din,
        DATA_OUT => bs_dout,
        SEL      => bs_shift
    );

    bs_dout_blocks <= slv_array_deser(bs_dout, BS_BLOCKS);

    bs_dout_g : for b in 0 to BS_BLOCKS-1 generate
        rx1_shifted_last_1hot(b) <= bs_dout_blocks(b)(BS_BLOCK_W-1);
        rx1_shifted_data     (b) <= bs_dout_blocks(b)(BS_BLOCK_W-1-1 downto 0);
    end generate;

    rx1_shifted_last_1hot_top <= rx1_shifted_last_1hot(BS_BLOCKS  -1 downto BS_BLOCKS/2);
    rx1_shifted_last_1hot_bot <= rx1_shifted_last_1hot(BS_BLOCKS/2-1 downto           0);

    rx1_shifted_data_top <= rx1_shifted_data(BS_BLOCKS  -1 downto BS_BLOCKS/2);
    rx1_shifted_data_bot <= rx1_shifted_data(BS_BLOCKS/2-1 downto           0);

    -- =========================================================================
    --  Lay-aside register for the data shifted over this word
    -- =========================================================================

    lay_aside_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((rx1_valid_reg = '1') and (TX_AXIS_TREADY = '1')) then
                rx1_shifted_data_top_reg <= rx1_shifted_data_top;
                rx1_packet_ending_reg    <= (or rx1_shifted_last_1hot_top) and rx1_last_reg and rx1_packet_ending_reg_en;
                keep_ptr_reg             <= to_integer(to_unsigned(keep_ptr, log2(DATA_BYTES)));
            end if;
            if ((RESET = '1') or ((rx1_packet_ending_reg = '1') and (TX_AXIS_TREADY = '1'))) then
                rx1_packet_ending_reg <= '0';
            end if;
        end if;
    end process;

    -- =========================================================================
    --  Output register
    -- =========================================================================

    output_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_AXIS_TREADY = '1') then
                TX_AXIS_TDATA  <= slv_array_ser(s_tx_axis_tdata);
                TX_AXIS_TKEEP  <= s_tx_axis_tkeep;
                TX_AXIS_TLAST  <= s_tx_axis_tlast;
                TX_AXIS_TVALID <= s_tx_axis_tvalid;
            end if;
            if (RESET = '1') then
                TX_AXIS_TVALID <= '0';
            end if;
        end if;
    end process;

end architecture;
