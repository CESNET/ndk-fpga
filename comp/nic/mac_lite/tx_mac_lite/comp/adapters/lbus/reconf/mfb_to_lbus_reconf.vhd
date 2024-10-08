-- mfb_to_lbus_reconf.vhd: converst received MFB packets to the LBUS formated packets on the output
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;

-- This entity does not have generic paramters alhough it is a MFB to MFB type interface. The
-- generic paremeters are set from input to output in the following manner: MFB#(1,8,8,8) ->
-- MFB#(1,4,16,8).
entity MFB_TO_LBUS_RECONF is
    port(
        CLK : in std_logic;
        RST : in std_logic;

        --==========================================================================================
        RX_MFB_DATA    : in  std_logic_vector(511 downto 0);
        RX_MFB_SOF     : in  std_logic;
        RX_MFB_EOF     : in  std_logic;
        RX_MFB_SOF_POS : in  std_logic_vector(2 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(5 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;
        --==========================================================================================

        --==========================================================================================
        TX_MFB_DATA    : out std_logic_vector(511 downto 0);
        TX_MFB_SOF     : out std_logic;
        TX_MFB_EOF     : out std_logic;
        TX_MFB_SOF_POS : out std_logic_vector(1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(5 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
        --==========================================================================================
        );
end entity;


architecture FULL of MFB_TO_LBUS_RECONF is

    type sh_fsm_t is (S_IDLE, S_PKT_PROCESS, S_PKT_END, S_PKT_HALT, S_WORD_REALIGN);
    signal sh_fsm_pst : sh_fsm_t := S_IDLE;
    signal sh_fsm_nst : sh_fsm_t := S_IDLE;

    signal rx_mfb_data_reg    : slv_array_t(1 downto 0)(511 downto 0);
    signal rx_mfb_sof_reg     : std_logic_vector(1 downto 0);
    signal rx_mfb_eof_reg     : std_logic_vector(1 downto 0);
    signal rx_mfb_sof_pos_reg : slv_array_t(1 downto 0)(2 downto 0);
    signal rx_mfb_eof_pos_reg : slv_array_t(1 downto 0)(5 downto 0);
    signal rx_mfb_src_rdy_reg : std_logic_vector(1 downto 0);
    signal rx_mfb_reg_dst_rdy : std_logic;
    -- general enable signal for the input register, the function of rx_mfb_reg_dst_rdy and last src_rdy stored in
    -- the register
    signal rx_mfb_reg_en      : std_logic;

    signal skdown_shift_data_out : std_logic_vector(1023 downto 0);
    signal skdown_shift_sel_pst  : unsigned(3 downto 0);
    signal skdown_shift_sel_nst  : unsigned(3 downto 0);

    signal word_shift_data_out : std_logic_vector(511 downto 0);
    signal word_shift_sel_pst  : unsigned(2 downto 0);
    signal word_shift_sel_nst  : unsigned(2 downto 0);

    -- indication if SOF has to be postponed one state later, used in case when the shift causes the SOF to be
    -- shifted-out of the current word
    signal postpone_sof_pst : std_logic;
    signal postpone_sof_nst : std_logic;

    signal sh_fsm_tx_sof     : std_logic;
    signal sh_fsm_tx_eof     : std_logic;
    signal sh_fsm_tx_sof_pos : std_logic_vector(1 downto 0);
    signal sh_fsm_tx_eof_pos : std_logic_vector(5 downto 0);
    signal sh_fsm_tx_src_rdy : std_logic;

begin

    -- purpose: input register of the MFB words and its attributes
    rx_mfb_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then

                rx_mfb_src_rdy_reg <= (others => '0');

            elsif (rx_mfb_reg_en = '1') then

                rx_mfb_data_reg    <= rx_mfb_data_reg(0) & RX_MFB_DATA;
                rx_mfb_sof_reg     <= rx_mfb_sof_reg(0) & RX_MFB_SOF;
                rx_mfb_eof_reg     <= rx_mfb_eof_reg(0) & RX_MFB_EOF;
                rx_mfb_sof_pos_reg <= rx_mfb_sof_pos_reg(0) & RX_MFB_SOF_POS;
                rx_mfb_eof_pos_reg <= rx_mfb_eof_pos_reg(0) & RX_MFB_EOF_POS;
                rx_mfb_src_rdy_reg <= rx_mfb_src_rdy_reg(0) & RX_MFB_SRC_RDY;

            end if;
        end if;
    end process;

    rx_mfb_reg_en  <= (not rx_mfb_src_rdy_reg(1)) or rx_mfb_reg_dst_rdy;
    RX_MFB_DST_RDY <= rx_mfb_reg_en;


    sh_fsm_state_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then

                sh_fsm_pst <= S_IDLE;

                skdown_shift_sel_pst <= (others => '0');
                word_shift_sel_pst   <= (others => '0');
                postpone_sof_pst     <= '0';

            elsif (TX_MFB_DST_RDY = '1') then

                sh_fsm_pst <= sh_fsm_nst;

                skdown_shift_sel_pst <= skdown_shift_sel_nst;
                word_shift_sel_pst   <= word_shift_sel_nst;
                postpone_sof_pst     <= postpone_sof_nst;

            end if;
        end if;
    end process;


    sh_fsm_nst_logic_p : process (all) is

        variable rdcd_sof_pos     : unsigned(1 downto 0);
        -- EOF's block position (the item position is the default)
        variable eof_blk_pos      : unsigned(2 downto 0);
        variable shifted_eof_blk_pos      : unsigned(2 downto 0);

    begin

        sh_fsm_nst <= sh_fsm_pst;

        eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(1)(5 downto 3));

        case sh_fsm_pst is
            when S_IDLE =>

                eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(0)(5 downto 3));

                -- a valid SOF occurs
                if (rx_mfb_src_rdy_reg(1) = '1' and rx_mfb_sof_reg(1) = '1') then

                    -- the packet begins in a current word but does not end in the next one
                    if (rx_mfb_eof_reg(0) = '0') then

                        sh_fsm_nst <= S_PKT_PROCESS;

                    else

                        -- happens when the beginnig of another packet occurs in the next word
                        -- together with the EOF of the current packet but the current
                        -- shift is not sufficent for that EOF to appear in the current word
                        if (rx_mfb_sof_reg(0) = '1') then
                            sh_fsm_nst <= S_WORD_REALIGN;
                        else
                            sh_fsm_nst <= S_PKT_END;
                        end if;

                        -- the end of a previously processed packet occurs in the current word but the shift causes for it
                        -- to appear in already sent word, the beginning of another packet COULD also occur
                        if (eof_blk_pos < unsigned(rx_mfb_sof_pos_reg(1))) then
                            sh_fsm_nst <= S_IDLE;
                        end if;

                    end if;

                    eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(1)(5 downto 3));

                    -- there is a small packet in a current word, regardless of a content of a next word, no
                    -- shift is performed
                    if (rx_mfb_eof_reg(1) = '1' and eof_blk_pos > unsigned(rx_mfb_sof_pos_reg(1))) then
                        sh_fsm_nst <= S_IDLE;
                    end if;

                end if;

            when S_PKT_PROCESS =>

                eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(0)(5 downto 3));

                if (rx_mfb_sof_reg(0) = '0') then

                    if (rx_mfb_eof_reg(0) = '1') then
                        -- after shift, the packet occurs entirely in a current word
                        if (eof_blk_pos < skdown_shift_sel_pst(2 downto 0)) then
                            sh_fsm_nst <= S_IDLE;
                        else
                            sh_fsm_nst <= S_PKT_END;
                        end if;
                    end if;

                else

                    if (rx_mfb_eof_reg(0) = '1') then
                        if (eof_blk_pos < skdown_shift_sel_pst(2 downto 0)) then
                            sh_fsm_nst <= S_IDLE;
                        else
                            sh_fsm_nst <= S_WORD_REALIGN;
                        end if;
                    end if;

                end if;


            when S_PKT_END =>

                -- no need to make this transition conditional, because despite there could be some data in the 0th
                -- register, the S_IDLE state reacts to the content in the first register
                sh_fsm_nst <= S_IDLE;

            when S_WORD_REALIGN =>

                -- points to the block in the OUTPUT word in which a SOF appears
                rdcd_sof_pos     := unsigned(rx_mfb_sof_pos_reg(1)(2 downto 1));

                shifted_eof_blk_pos := eof_blk_pos - word_shift_sel_pst;

                if (shifted_eof_blk_pos(2 downto 1) = rdcd_sof_pos) then

                    sh_fsm_nst <= S_PKT_HALT;

                else

                    if (rx_mfb_sof_reg(0) = '0') then

                        if (rx_mfb_eof_reg(0) = '1') then
                            sh_fsm_nst <= S_PKT_END;
                        else
                            sh_fsm_nst <= S_PKT_PROCESS;
                        end if;

                    else

                        -- NOTE: this is the condition that must be abided, there can not be a situation when the
                        -- SOF is followd by SOF without the EOF of the previdous packet
                        if (rx_mfb_eof_reg(0) = '1') then
                            sh_fsm_nst <= S_WORD_REALIGN;
                        end if;
                    end if;
                end if;

            -- the packet on the input needs to be halted because its SOF would appear in the same block as the
            -- EOF on the output
            when S_PKT_HALT =>

                eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(0)(5 downto 3));

                if (rx_mfb_eof_reg(0) = '1') then

                    if (eof_blk_pos = 7) then
                        sh_fsm_nst <= S_PKT_END;
                    else
                        sh_fsm_nst <= S_IDLE;
                    end if;

                else
                    sh_fsm_nst <= S_PKT_PROCESS;
                end if;

        end case;
    end process;


    sh_fsm_output_logic_p : process (all) is

        variable sof_pos_uns      : unsigned(2 downto 0);
        variable rdcd_sof_pos     : unsigned(1 downto 0);
        variable eof_blk_pos      : unsigned(2 downto 0);
        variable shifted_eof_blk_pos      : unsigned(2 downto 0);

    begin

        sh_fsm_tx_sof      <= '0';
        sh_fsm_tx_eof      <= '0';
        sh_fsm_tx_sof_pos  <= (others => '0');
        sh_fsm_tx_eof_pos  <= (others => '0');
        sh_fsm_tx_src_rdy  <= '0';
        rx_mfb_reg_dst_rdy <= TX_MFB_DST_RDY;

        postpone_sof_nst <= '0';

        skdown_shift_sel_nst <= skdown_shift_sel_pst;
        word_shift_sel_nst   <= word_shift_sel_pst;

        -- I care only about the block position of the EOF because the shifting is performed by blocks
        eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(0)(5 downto 3));

        case sh_fsm_pst is

            when S_IDLE =>

                if (rx_mfb_src_rdy_reg(1) = '1' and rx_mfb_sof_reg(1) = '1') then

                    skdown_shift_sel_nst <= '0' & unsigned(rx_mfb_sof_pos_reg(1));

                    sh_fsm_tx_sof     <= '1';
                    -- SOF pos is set to 0 implicitly
                    sh_fsm_tx_src_rdy <= '1';

                    eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(1)(5 downto 3));

                    -- a small packet in a whole word
                    if (rx_mfb_eof_reg(1) = '1' and eof_blk_pos > unsigned(rx_mfb_sof_pos_reg(1))) then

                        sh_fsm_tx_eof     <= '1';
                        sh_fsm_tx_eof_pos <= rx_mfb_eof_pos_reg(1);

                    else

                        eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(0)(5 downto 3));

                        -- the eof does not occur in the current word but in the next word does
                        if (rx_mfb_eof_reg(0) = '1') then

                            -- EOF occurs in the next word but the shift causes for it to appear in a current word
                            if (eof_blk_pos < unsigned(rx_mfb_sof_pos_reg(1))) then

                                sh_fsm_tx_eof     <= '1';
                                -- calculate the EOF_POS value by subtracting the value of SOF_POS from the EOF block
                                -- position, the first two bits are simply copied from the EOF_POS
                                -- value because the shift is done by blocks
                                sh_fsm_tx_eof_pos <= std_logic_vector(eof_blk_pos - unsigned(rx_mfb_sof_pos_reg(1))) & rx_mfb_eof_pos_reg(0)(2 downto 0);

                            else

                                -- the current shift does not cause for the EOF to appear in a current word and
                                -- there is also a SOF in the next word so the potential gap needs to be removed
                                if (rx_mfb_sof_reg(0) = '1') then
                                    word_shift_sel_nst <= unsigned(rx_mfb_sof_pos_reg(1));
                                end if;

                            end if;
                        end if;
                    end if;
                end if;

            -- general processing of the packet in its middle
            when S_PKT_PROCESS =>

                sh_fsm_tx_src_rdy <= '1';

                if (rx_mfb_eof_reg(0) = '1') then

                    -- the EOF occurs in the next word but current shift makes it appear in a current word
                    if (eof_blk_pos < skdown_shift_sel_pst(2 downto 0)) then

                        sh_fsm_tx_eof     <= '1';
                        sh_fsm_tx_eof_pos <= std_logic_vector(eof_blk_pos - skdown_shift_sel_pst(2 downto 0)) & rx_mfb_eof_pos_reg(0)(2 downto 0);

                    else

                        if (rx_mfb_sof_reg(0) = '1') then
                            word_shift_sel_nst <= skdown_shift_sel_pst(2 downto 0);
                        end if;

                    end if;
                end if;

            -- there is a rest of the packet's end in the current word and nothing else
            when S_PKT_END =>

                eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(1)(5 downto 3));

                sh_fsm_tx_eof     <= '1';
                sh_fsm_tx_eof_pos <= std_logic_vector(eof_blk_pos - skdown_shift_sel_pst(2 downto 0)) & rx_mfb_eof_pos_reg(1)(2 downto 0);
                sh_fsm_tx_src_rdy <= '1';

            when S_WORD_REALIGN =>

                sof_pos_uns      := unsigned(rx_mfb_sof_pos_reg(1));
                rdcd_sof_pos     := unsigned(rx_mfb_sof_pos_reg(1)(2 downto 1));
                eof_blk_pos      := unsigned(rx_mfb_eof_pos_reg(1)(5 downto 3));

                shifted_eof_blk_pos := eof_blk_pos - word_shift_sel_pst;

                sh_fsm_tx_eof     <= '1';
                sh_fsm_tx_sof_pos <= std_logic_vector(shifted_eof_blk_pos(2 downto 1) + 1);
                sh_fsm_tx_eof_pos <= std_logic_vector(eof_blk_pos - word_shift_sel_pst) & rx_mfb_eof_pos_reg(1)(2 downto 0);
                sh_fsm_tx_src_rdy <= '1';

                -- the input register is stopped because the beginning packet needs to be shifted back
                if (shifted_eof_blk_pos(2 downto 1) = rdcd_sof_pos) then

                    rx_mfb_reg_dst_rdy <= '0';

                    -- special case when the SOF and EOF occur in the last block in the output word, thus the
                    -- back-shift of the SOF causes for it to appear in the next word. Therefore the SOF indication
                    -- for it needs to be postponed to the next state.
                    if (shifted_eof_blk_pos(2 downto 1) = 3) then
                        postpone_sof_nst <= '1';
                    else

                        sh_fsm_tx_sof <= '1';
                        skdown_shift_sel_nst <= "1111";

                    end if;

                else

                    sh_fsm_tx_sof <= '1';

                    -- eliminates the gap between packet in one word but respects the shifting of
                    -- the EOF
                    skdown_shift_sel_nst <= '0' & (rdcd_sof_pos - shifted_eof_blk_pos(2 downto 1) - 1) & sof_pos_uns(0);

                    -- sets the shifting in case there will be a sof and eof in the next word,
                    -- conditioning this assignment is obsolete
                    word_shift_sel_nst <= (rdcd_sof_pos - shifted_eof_blk_pos(2 downto 1) - 1) & sof_pos_uns(0);

                end if;

            when S_PKT_HALT =>

                skdown_shift_sel_nst <= "0111";

                sh_fsm_tx_sof <= postpone_sof_pst;
                -- NOTE: SOF_POS is 0 because the sof has not been processed in the previous cycle, the
                -- entire packet is shifted towards the beginning of the word

                sh_fsm_tx_src_rdy <= '1';

                if (rx_mfb_eof_reg(0) = '1') then

                    -- NOTE: when packet occurs in the last block, that means that after shift, the EOF needs to
                    -- be processed in the S_PKT_END state. When EOF occurs in the lower index blocks then, after
                    -- shift, it occurs in the current word.
                    if (eof_blk_pos < 7) then

                        sh_fsm_tx_eof     <= '1';
                        sh_fsm_tx_eof_pos <= std_logic_vector(eof_blk_pos - 7) & rx_mfb_eof_pos_reg(0)(2 downto 0);

                    end if;
                end if;

        end case;
    end process;


    -- shifts both words which are stored in the rx_mfb_data_reg
    shakedown_shifter_i : entity work.BARREL_SHIFTER_GEN
        generic map (
            BLOCKS     => 2*8,          -- shifts two MFB words
            BLOCK_SIZE => 8*8,          -- blocks from the input MFB
            SHIFT_LEFT => FALSE)
        port map (
            DATA_IN  => rx_mfb_data_reg(0) & rx_mfb_data_reg(1),
            DATA_OUT => skdown_shift_data_out,
            SEL      => std_logic_vector(skdown_shift_sel_nst));


    -- shifts only the last word in the input shift register
    word_shifter_i : entity work.BARREL_SHIFTER_GEN
        generic map (
            BLOCKS     => 8,            -- shifts inside one MFB word
            BLOCK_SIZE => 8*8,          -- blocks from the input MFB
            SHIFT_LEFT => FALSE)
        port map (
            DATA_IN  => rx_mfb_data_reg(1),
            DATA_OUT => word_shift_data_out,
            SEL      => std_logic_vector(word_shift_sel_pst));


    -- purpose: output registered multiplexer, when there is a need to have a combination of blocks from both of the shifters
    out_mux_p : process (CLK) is

        variable eof_blk_pos : unsigned(2 downto 0);

    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then

                eof_blk_pos := unsigned(rx_mfb_eof_pos_reg(1)(5 downto 3));

                if (sh_fsm_pst = S_WORD_REALIGN) then

                    -- iterate through output blocks
                    for i in 0 to 7 loop

                        -- reads the blocks containing the end of packet from the word_shifter_i and the rest from the
                        -- shakedown_shifter_i
                        if (i <= (eof_blk_pos - word_shift_sel_pst)) then
                            TX_MFB_DATA(63 + 64*i downto 64*i) <= word_shift_data_out(63 + 64*i downto 64*i);
                        else
                            TX_MFB_DATA(63 + 64*i downto 64*i) <= skdown_shift_data_out(63 + 64*i downto 64*i);
                        end if;

                    end loop;

                else

                    TX_MFB_DATA <= skdown_shift_data_out(TX_MFB_DATA'range);

                end if;
            end if;
        end if;
    end process;


    output_register_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then

                TX_MFB_SRC_RDY <= '0';

            elsif (TX_MFB_DST_RDY = '1') then

                TX_MFB_SOF     <= sh_fsm_tx_sof;
                TX_MFB_EOF     <= sh_fsm_tx_eof;
                TX_MFB_SOF_POS <= sh_fsm_tx_sof_pos;
                TX_MFB_EOF_POS <= sh_fsm_tx_eof_pos;
                TX_MFB_SRC_RDY <= sh_fsm_tx_src_rdy;

            end if;
        end if;
    end process;

end architecture;
