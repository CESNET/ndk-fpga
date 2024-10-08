-- rx_dma_calypte_trans_buffer.vhd: this component divides each packet into 128B chunks when the
-- beginning of each chunk is set to the third MFB block of the first word
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;

-- This component contols the successfull buffering of input data on the block specified by the
-- `BUFFERED_DATA_SIZE` generic parameter. Whole buffer content is then set on the output MFB bus.
entity RX_DMA_CALYPTE_TRANS_BUFFER is
    generic (
        -- The amount of data which needs to be buffered in bytes
        BUFFERED_DATA_SIZE : integer := 128;
        -- Adds a skid buffer on the output
        REG_OUT_EN         : boolean := TRUE;

        -- =========================================================================================
        -- MFB bus parameters
        --
        -- The amount of regions is always set to 1
        -- =========================================================================================
        RX_REGION_SIZE : integer := 1;
        RX_BLOCK_SIZE  : integer := 4*8;
        RX_ITEM_WIDTH  : integer := 8);

    port (
        CLK : in std_logic;
        RST : in std_logic;

        -- =========================================================================================
        -- Data from the DMA input buffer
        --
        -- There is no SOF_POS because every input word is aligned to the beginning of the word
        -- =========================================================================================
        RX_MFB_DATA    : in  std_logic_vector(RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(max(1, log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF     : in  std_logic;
        RX_MFB_EOF     : in  std_logic;
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =========================================================================================
        -- Output MFB to Header insertor
        -- =========================================================================================
        TX_MFB_DATA    : out std_logic_vector((BUFFERED_DATA_SIZE/(RX_REGION_SIZE*RX_BLOCK_SIZE))*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
        -- The SOF_POS is propably useless because each output packet is aligned to the beginning of a word, only
        -- one block is used
        TX_MFB_SOF_POS : out std_logic_vector(max(1, log2(RX_REGION_SIZE))-1 downto 0) := (others => '0');
        TX_MFB_EOF_POS : out std_logic_vector(max(1, log2((BUFFERED_DATA_SIZE/(RX_REGION_SIZE*RX_BLOCK_SIZE))*RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF     : out std_logic;
        TX_MFB_EOF     : out std_logic;
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
        );

end entity;

architecture FULL of RX_DMA_CALYPTE_TRANS_BUFFER is

    constant BUFFER_DEPTH : positive := BUFFERED_DATA_SIZE/(RX_REGION_SIZE*RX_BLOCK_SIZE);

    type packing_fsm_state_t is (S_IDLE, S_PACKING, S_WAIT);
    signal packing_fsm_pst : packing_fsm_state_t := S_IDLE;
    signal packing_fsm_nst : packing_fsm_state_t := S_IDLE;

    -- NOTE: SOF_POS is not used internally because each output packet has this set to 0, e.g. it is aligned to the
    -- LSB of the output word. EOF_POS does not have a register but it is recalculated according to the currently
    -- buffered word's index.
    signal rx_mfb_data_reg_pst : slv_array_t((BUFFER_DEPTH - 1) downto 0)(RX_MFB_DATA'range);
    signal rx_mfb_sof_reg_pst  : std_logic_vector((BUFFER_DEPTH - 1) downto 0);
    signal rx_mfb_eof_reg_pst  : std_logic_vector((BUFFER_DEPTH - 1) downto 0);

    signal rx_mfb_data_reg_nst : slv_array_t((BUFFER_DEPTH - 1) downto 0)(RX_MFB_DATA'range);
    signal rx_mfb_sof_reg_nst  : std_logic_vector((BUFFER_DEPTH - 1) downto 0);
    signal rx_mfb_eof_reg_nst  : std_logic_vector((BUFFER_DEPTH - 1) downto 0);

    signal recalc_eof_pos_pst : unsigned(TX_MFB_EOF_POS'range);
    signal recalc_eof_pos_nst : unsigned(TX_MFB_EOF_POS'range);

    signal segment_ptr_pst : unsigned(log2(BUFFER_DEPTH) -1 downto 0);
    signal segment_ptr_nst : unsigned(log2(BUFFER_DEPTH) -1 downto 0);

    signal buff_tx_mfb_src_rdy_pst : std_logic;
    signal buff_tx_mfb_src_rdy_nst : std_logic;

    -- The FIFO stores MFB data, SOF, EOF and EOF_POS that was calculated from the state machine.
    constant FIFO_TX_DATA_WIDTH : natural := TX_MFB_DATA'length + 1 + 1 + recalc_eof_pos_nst'length;

    signal fifo_rx_mfb_dst_rdy   : std_logic;
    signal fifo_tx_mfb_data      : std_logic_vector(FIFO_TX_DATA_WIDTH -1 downto 0);
begin

    assert (RX_REGION_SIZE = 1 and (RX_BLOCK_SIZE = 4*8 or RX_BLOCK_SIZE = 8*8) and RX_ITEM_WIDTH = 8)
        report "RX_DMA_TRANS_BUFFER: The component was not designed for this RX MFB configuration, the allowed are: MFB#(1,1,32,8), MFB#(1,1,64,8)"
        severity FAILURE;

    assert (BUFFERED_DATA_SIZE = 128)
        report "RX_DMA_TRANS_BUFFER: the design does not currently support the specified length of the buffered data, the allowed are: 128"
        severity FAILURE;

    fsm_pst_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then

                packing_fsm_pst <= S_IDLE;
                segment_ptr_pst <= (others => '0');

                buff_tx_mfb_src_rdy_pst <= '0';
            else

                packing_fsm_pst <= packing_fsm_nst;
                segment_ptr_pst <= segment_ptr_nst;

                rx_mfb_data_reg_pst <= rx_mfb_data_reg_nst;
                rx_mfb_sof_reg_pst  <= rx_mfb_sof_reg_nst;
                rx_mfb_eof_reg_pst  <= rx_mfb_eof_reg_nst;

                recalc_eof_pos_pst <= recalc_eof_pos_nst;

                buff_tx_mfb_src_rdy_pst <= buff_tx_mfb_src_rdy_nst;
            end if;
        end if;
    end process;

    -- purpose: quasi demultiplexor which assigns the valid words to the specific registers in internal buffers.
    -- The process also handles the situation when the EOF occurs in the middle of the buffer.
    fsm_output_logic_p : process (all) is
    begin
        packing_fsm_nst <= packing_fsm_pst;
        segment_ptr_nst <= segment_ptr_pst;

        rx_mfb_data_reg_nst <= rx_mfb_data_reg_pst;
        rx_mfb_sof_reg_nst  <= rx_mfb_sof_reg_pst;
        rx_mfb_eof_reg_nst  <= rx_mfb_eof_reg_pst;

        recalc_eof_pos_nst <= recalc_eof_pos_pst;

        RX_MFB_DST_RDY          <= '1';
        buff_tx_mfb_src_rdy_nst <= buff_tx_mfb_src_rdy_pst;

        case packing_fsm_pst is
            when S_IDLE =>

                -- NOTE: Does not apply if the incoming packets can have size lower than the width
                -- of the input data bus.
                if (RX_MFB_SRC_RDY = '1') then
                    packing_fsm_nst <= S_PACKING;

                    rx_mfb_data_reg_nst(to_integer(segment_ptr_pst)) <= RX_MFB_DATA;
                    rx_mfb_sof_reg_nst(to_integer(segment_ptr_pst))  <= RX_MFB_SOF;
                    rx_mfb_eof_reg_nst(to_integer(segment_ptr_pst))  <= RX_MFB_EOF;

                    segment_ptr_nst <= segment_ptr_pst + 1;

                    if (RX_MFB_EOF = '1' and segment_ptr_pst < (BUFFER_DEPTH - 1)) then

                        packing_fsm_nst <= S_WAIT;

                        segment_ptr_nst <= (others => '0');

                        -- if buffer is not full, then deassert the remaining SOF/EOF bits in the rest of the words so
                        -- the would not cause bugs in the future
                        for i in 0 to (BUFFER_DEPTH - 1) loop
                            if (i > segment_ptr_pst and segment_ptr_pst < (BUFFER_DEPTH - 1)) then
                                rx_mfb_sof_reg_nst(i) <= '0';
                                rx_mfb_eof_reg_nst(i) <= '0';
                            end if;
                        end loop;

                        recalc_eof_pos_nst      <= segment_ptr_pst & unsigned(RX_MFB_EOF_POS);
                        buff_tx_mfb_src_rdy_nst <= '1';
                    end if;
                end if;

            when S_PACKING =>

                if (RX_MFB_SRC_RDY = '1') then

                    rx_mfb_data_reg_nst(to_integer(segment_ptr_pst)) <= RX_MFB_DATA;
                    rx_mfb_sof_reg_nst(to_integer(segment_ptr_pst))  <= RX_MFB_SOF;
                    rx_mfb_eof_reg_nst(to_integer(segment_ptr_pst))  <= RX_MFB_EOF;

                    segment_ptr_nst <= segment_ptr_pst + 1;

                    if (RX_MFB_EOF = '1' and segment_ptr_pst < (BUFFER_DEPTH - 1)) then

                        packing_fsm_nst <= S_WAIT;

                        segment_ptr_nst <= (others => '0');

                        -- if buffer is not full, then deassert the remaining SOF/EOF bits in the rest of the words so
                        -- the would not cause bugs in the future
                        for i in 0 to (BUFFER_DEPTH - 1) loop
                            if (i > segment_ptr_pst and segment_ptr_pst < (BUFFER_DEPTH - 1)) then
                                rx_mfb_sof_reg_nst(i) <= '0';
                                rx_mfb_eof_reg_nst(i) <= '0';
                            end if;
                        end loop;

                        recalc_eof_pos_nst      <= segment_ptr_pst & unsigned(RX_MFB_EOF_POS);
                        buff_tx_mfb_src_rdy_nst <= '1';

                    elsif (RX_MFB_EOF = '1' and segment_ptr_pst = (BUFFER_DEPTH - 1)) then

                        packing_fsm_nst <= S_WAIT;

                        recalc_eof_pos_nst      <= segment_ptr_pst & unsigned(RX_MFB_EOF_POS);
                        buff_tx_mfb_src_rdy_nst <= '1';

                    elsif (RX_MFB_EOF = '0' and segment_ptr_pst = (BUFFER_DEPTH - 1)) then
                        packing_fsm_nst <= S_WAIT;

                        buff_tx_mfb_src_rdy_nst <= '1';
                    end if;
                end if;

            when S_WAIT =>

                RX_MFB_DST_RDY <= fifo_rx_mfb_dst_rdy;

                if (fifo_rx_mfb_dst_rdy = '1') then

                    buff_tx_mfb_src_rdy_nst <= '0';

                    if (RX_MFB_SRC_RDY = '1') then
                        packing_fsm_nst <= S_PACKING;

                        rx_mfb_data_reg_nst(to_integer(segment_ptr_pst)) <= RX_MFB_DATA;
                        rx_mfb_sof_reg_nst(to_integer(segment_ptr_pst))  <= RX_MFB_SOF;
                        rx_mfb_eof_reg_nst(to_integer(segment_ptr_pst))  <= RX_MFB_EOF;

                        segment_ptr_nst <= segment_ptr_pst + 1;

                        if (RX_MFB_EOF = '1' and segment_ptr_pst < (BUFFER_DEPTH - 1)) then

                            packing_fsm_nst <= S_WAIT;

                            segment_ptr_nst <= (others => '0');

                            -- if buffer is not full, then deassert the remaining SOF/EOF bits in the rest of the words so
                            -- the would not cause bugs in the future
                            for i in 0 to (BUFFER_DEPTH - 1) loop
                                if (i > segment_ptr_pst and segment_ptr_pst < (BUFFER_DEPTH - 1)) then
                                    rx_mfb_sof_reg_nst(i) <= '0';
                                    rx_mfb_eof_reg_nst(i) <= '0';
                                end if;
                            end loop;

                            recalc_eof_pos_nst      <= segment_ptr_pst & unsigned(RX_MFB_EOF_POS);
                            buff_tx_mfb_src_rdy_nst <= '1';
                        end if;
                    else
                        packing_fsm_nst <= S_IDLE;
                    end if;
                end if;
            when others => null;
        end case;
    end process;

    reg_fifo_i : entity work.REG_FIFO
        generic map (
            DATA_WIDTH => FIFO_TX_DATA_WIDTH,
            ITEMS      => 1,
            FAKE_FIFO  => not REG_OUT_EN)
        port map (
            CLK => CLK,
            RST => RST,

            RX_DATA    => slv_array_ser(rx_mfb_data_reg_pst) & rx_mfb_sof_reg_pst(0) & (or rx_mfb_eof_reg_pst) & std_logic_vector(recalc_eof_pos_pst),
            RX_SRC_RDY => buff_tx_mfb_src_rdy_pst,
            RX_DST_RDY => fifo_rx_mfb_dst_rdy,

            TX_DATA    => fifo_tx_mfb_data,
            TX_SRC_RDY => TX_MFB_SRC_RDY,
            TX_DST_RDY => TX_MFB_DST_RDY);

    TX_MFB_DATA    <= fifo_tx_mfb_data(FIFO_TX_DATA_WIDTH -1 downto 1 + 1 + recalc_eof_pos_nst'length);
    TX_MFB_SOF     <= fifo_tx_mfb_data(1 + 1 + recalc_eof_pos_nst'length -1);
    TX_MFB_EOF     <= fifo_tx_mfb_data(1 + recalc_eof_pos_nst'length -1);
    TX_MFB_SOF_POS <= (others => '0');
    TX_MFB_EOF_POS <= fifo_tx_mfb_data(recalc_eof_pos_nst'length -1 downto 0);
end architecture;
