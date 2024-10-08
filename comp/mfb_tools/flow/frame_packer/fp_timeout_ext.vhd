-- fp_timeout_ext.vhd: Timeout and EOF setting for the FP_Channel
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The purpose of this component is set timeout when necessary
-- Also the correct SOF, EOF and SOF_POS, EOF_POS is set since these doesn't have to come at the same time as overflow
entity FP_TIMEOUT_EXT is
    generic(
        MFB_REGIONS         : natural := 4;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;
        RX_PKT_SIZE_MAX     : natural := 2**10;

        TIMEOUT_CLK_NO      : natural := 32
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        RX_SOF_ONE_HOT_CURR  : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_EOF_ONE_HOT_CURR  : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_PKT_LNG_CURR      : in  slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

        RX_SOF_ONE_HOT_REG   : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_EOF_ONE_HOT_REG   : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
        RX_PKT_LNG_REG       : in  slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

        RX_OVERFLOW          : in  std_logic;
        RX_TMP_PTR           : in  unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))-1 downto 0);

        TX_PKT_LNG           : out slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
        TX_SOF               : out std_logic_vector(MFB_REGIONS - 1 downto 0);
        TX_EOF               : out std_logic_vector(MFB_REGIONS - 1 downto 0);
        TX_SOF_POS           : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_EOF_POS           : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_TIMEOUT_EXT       : out std_logic
    );
end entity;

architecture FULL of FP_TIMEOUT_EXT is
    -- Time-machine
    type ext_timeout_fsm is (
        st_PASS,        -- Normal operation
        st_TIMEOUT      -- Possible timeout event
    );
    signal state, next_state: ext_timeout_fsm := st_PASS;

    signal sof                  : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal eof                  : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal eof_cmp_val          : unsigned(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE))-1 downto 0) := (others => '0');
    signal eof_compare          : std_logic;
    signal tx_sof_pos_s         : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_eof_pos_s         : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal sof_pos              : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal eof_pos              : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal pkt_lng              : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    signal pkt_lng_reg          : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);

    signal sof_reg              : std_logic_vector(MFB_REGIONS - 1 downto 0) := (others => '0');
    signal eof_reg              : std_logic_vector(MFB_REGIONS - 1 downto 0) := (others => '0');
    signal sof_pos_reg          : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal eof_pos_reg          : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE))-1 downto 0);


    -- Timeout
    signal timeout              : std_logic;
    signal timeout_event        : std_logic;
    signal timeout_en           : std_logic;
    signal timeout_cnt          : unsigned(max(1, log2(TIMEOUT_CLK_NO) + 1) - 1 downto 0):= (others => '0');
    signal timeout_block        : std_logic := '0';
    -- Fixup - output is a vector ...
    signal mux_out_sof_oh_arr   : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(0 downto 0);
    signal mux_out_eof_oh_arr   : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(0 downto 0);
    signal mux_out_sof_oh       : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal mux_out_eof_oh       : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    signal mux_out_pkt_lng      : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    -- TIME_SELECT
    signal sel_out              : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal sel_out_n            : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal sel_one_hot          : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    signal mux_select           : slv_array_t(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0)(0 downto 0);

    signal sof_mask             : std_logic_vector(MFB_REGIONS - 1 downto 0) := (others => '0');
    signal eof_mask             : std_logic_vector(MFB_REGIONS - 1 downto 0) := (others => '0');

begin
    --------------------------------------------------------------------------------
    ---                                TIME_SELECT                               ---
    --------------------------------------------------------------------------------
    -- MUX select based on pointer value
    sel_one_hot_p: process(all)
    begin
        sel_one_hot                         <= (others => '0');
        sel_one_hot(to_integer(RX_TMP_PTR)) <= '1';
    end process;

    sel_before_one_i : entity work.BEFORE_ONE
        generic map(
            DATA_WIDTH  => MFB_REGIONS*MFB_REGION_SIZE
        )
        port map(
            DI  => sel_one_hot,
            DO  => sel_out_n
        );

    sel_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            sel_out <= not sel_out_n;
        end if;
    end process;

    --------------------------------------------------------------------------------
    ---                                TIME_MUX                                  ---
    --------------------------------------------------------------------------------
    mux_select   <= slv_array_deser(sel_out, MFB_REGIONS*MFB_REGION_SIZE);

    sof_oh_g: for i in MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0 generate
        eof_oh_mux_i: entity work.GEN_MUX
            generic map(
                DATA_WIDTH  => 1,
                MUX_WIDTH   => 2
            )
            port map(
                DATA_IN     => RX_SOF_ONE_HOT_CURR(i) & RX_SOF_ONE_HOT_REG(i),
                SEL         => mux_select(i),
                DATA_OUT    => mux_out_sof_oh_arr(i)
        );
        mux_out_sof_oh(i)  <= mux_out_sof_oh_arr(i)(0);
    end generate;

    eof_oh_g: for i in MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0 generate
        eof_oh_mux_i: entity work.GEN_MUX
            generic map(
                DATA_WIDTH  => 1,
                MUX_WIDTH   => 2
            )
            port map(
                DATA_IN     => RX_EOF_ONE_HOT_CURR(i) & RX_EOF_ONE_HOT_REG(i),
                SEL         => mux_select(i),
                DATA_OUT    => mux_out_eof_oh_arr(i)
        );
        mux_out_eof_oh(i)  <= mux_out_eof_oh_arr(i)(0);
    end generate;

    pkt_lng_g: for i in MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0 generate
        pkt_lng_mux_i: entity work.GEN_MUX
            generic map(
                DATA_WIDTH  => max(1, log2(RX_PKT_SIZE_MAX+1)),
                MUX_WIDTH   => 2
            )
            port map(
                DATA_IN     => RX_PKT_LNG_CURR(i) & RX_PKT_LNG_REG(i),
                SEL         => mux_select(i),
                DATA_OUT    => mux_out_pkt_lng(i)
        );
    end generate;

    -- Position of SOF block
    sof_block_p: process(all)
        variable sof_v              : std_logic_vector(MFB_REGIONS - 1 downto 0);
        variable sof_pos_block_v    : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(MFB_REGION_SIZE)) - 1 downto 0);

        variable mux_out_sof_oh_v   : slv_array_t(MFB_REGIONS - 1 downto 0)(MFB_REGION_SIZE - 1 downto 0);
        variable pkt_lng_v          : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    begin
        mux_out_sof_oh_v    := slv_array_deser(mux_out_sof_oh, MFB_REGIONS);

        sof_v               := (others => '0');
        sof_pos_block_v     := (others => (others => '0'));
        pkt_lng_v           := (others => (others => '0'));

        sof_region_l: for r in 0 to MFB_REGIONS - 1 loop
            sof_block_l: for b in 0 to MFB_REGION_SIZE - 1 loop
                if mux_out_sof_oh_v(r)(b) = '1' then
                    sof_v(r)           := '1';
                    sof_pos_block_v(r) := std_logic_vector(to_unsigned(b, max(1, log2(MFB_REGION_SIZE))));
                    pkt_lng_v(r)       := mux_out_pkt_lng(r*MFB_REGION_SIZE + b);
                end if;
            end loop;
        end loop;

        sof <= sof_v;
        region_sof_pos_l: for r in 0 to MFB_REGIONS - 1 loop
            sof_pos(r)    <= sof_pos_block_v(r);
            pkt_lng(r)    <= pkt_lng_v(r);
        end loop;
    end process;

    -- Position of EOF block
    eof_block_p: process(all)
        variable eof_v              : std_logic_vector(MFB_REGIONS - 1 downto 0);
        variable eof_pos_block_v    : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(MFB_REGION_SIZE)) - 1 downto 0);

        variable mux_out_eof_oh_v   : slv_array_t(MFB_REGIONS - 1 downto 0)(MFB_REGION_SIZE - 1 downto 0);
        variable eof_pos_cmp_v      : unsigned(max(1, log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
    begin
        mux_out_eof_oh_v        := slv_array_deser(mux_out_eof_oh, MFB_REGIONS);

        eof_v           := (others => '0');
        eof_pos_block_v := (others => (others => '0'));

        eof_pos_cmp_v   := (others => '0');

        eof_region_l: for r in 0 to MFB_REGIONS - 1 loop
            eof_block_l: for b in 0 to MFB_REGION_SIZE - 1 loop
                if mux_out_eof_oh_v(r)(b) = '1' then
                    eof_v(r)           := '1';
                    eof_pos_block_v(r) := std_logic_vector(to_unsigned(b, max(1, log2(MFB_REGION_SIZE))));

                    -- Last valid value compare value
                    eof_pos_cmp_v      := to_unsigned(r*MFB_REGION_SIZE, eof_pos_cmp_v'length) + to_unsigned(b, eof_pos_cmp_v'length);
                end if;
            end loop;
        end loop;

        eof <= eof_v;
        region_eof_pos_l: for r in 0 to MFB_REGIONS - 1 loop
            eof_pos(r)    <= eof_pos_block_v(r);
        end loop;

        -- Compare value
        eof_cmp_val <= eof_pos_cmp_v;
    end process;

    -- Compare value - Find out if the timeout condition has been met
    eof_compare <= '1' when eof_cmp_val = RX_TMP_PTR - 1 else '0';

    eof_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            if RX_OVERFLOW  = '1' or timeout_block = '1' then
                sof_reg      <= (others => '0');
                sof_pos_reg  <= (others => (others => '0'));
                eof_reg      <= (others => '0');
                eof_pos_reg  <= (others => (others => '0'));
                pkt_lng_reg  <= (others => (others => '0'));
            else
                for r in 0 to MFB_REGIONS - 1 loop
                    if eof(r) = '1' then
                        eof_reg(r)      <= '1';
                        eof_pos_reg(r)  <= eof_pos(r);
                    end if;
                    if sof(r) = '1' then
                        sof_reg(r)      <= '1';
                        sof_pos_reg(r)  <= sof_pos(r);
                        pkt_lng_reg(r)  <= pkt_lng(r);
                    end if;
                end loop;
            end if;
        end if;
    end process;

    -- EOF mask
    process(all)
    begin
        if rising_edge(CLK) then
            if timeout_event = '1' then
                sof_mask    <= sof;
                eof_mask    <= eof;
            elsif RX_OVERFLOW = '1' then
                sof_mask    <= (others => '0');
                eof_mask    <= (others => '0');
            end if;
        end if;
    end process;

    process(all)
    begin
        if rising_edge(CLK) then
            if RX_OVERFLOW = '1' then
                timeout_block   <= '0';
            elsif timeout_event = '1' then
                timeout_block   <= '1';
            end if;
        end if;
    end process;

    ext_timeout_reg_p: process(all)
    begin
        if (rising_edge(CLK)) then
            if RST = '1' then
                state   <= st_PASS;
            else
                state   <= next_state;
            end if;
        end if;
    end process;

    ext_timeout_state_p: process (all)
        variable eof_v  : std_logic;
    begin
        next_state      <= state;
        timeout_en      <= '0';
        TX_SOF          <= (others => '0');
        TX_EOF          <= (others => '0');
        TX_PKT_LNG      <= (others => (others => '0'));
        tx_sof_pos_s    <= (others => (others => '0'));
        tx_eof_pos_s    <= (others => (others => '0'));

        eof_v   := or (eof);

        case(state) is
            when st_PASS    =>
                if timeout_block = '0' then
                    if RX_OVERFLOW = '1'  then
                        for r in 0 to MFB_REGIONS - 1 loop
                            if sof_reg(r) = '1' then
                                TX_SOF(r)       <= '1';
                                tx_sof_pos_s(r) <= sof_pos_reg(r);
                                TX_PKT_LNG(r)   <= pkt_lng_reg(r);
                            else
                                TX_SOF(r)       <= sof(r);
                                tx_sof_pos_s(r) <= sof_pos(r);
                                TX_PKT_LNG(r)   <= pkt_lng(r);
                            end if;

                            if eof_reg(r) = '1' then
                                TX_EOF(r)       <= '1';
                                tx_eof_pos_s(r) <= eof_pos_reg(r);
                            else
                                TX_EOF(r)       <= eof(r);
                                tx_eof_pos_s(r) <= eof_pos(r);
                            end if;
                        end loop;
                    elsif (eof_v = '1') and (eof_compare = '1') then
                        next_state  <=  st_TIMEOUT;
                    end if;
                -- More regions
                else
                    if RX_OVERFLOW = '1' then
                        for r in 0 to MFB_REGIONS - 1 loop
                            TX_SOF(r)       <= sof(r) and (not sof_mask(r));
                            tx_sof_pos_s(r) <= sof_pos(r);
                            TX_EOF(r)       <= eof(r) and (not eof_mask(r));
                            tx_eof_pos_s(r) <= eof_pos(r);
                            TX_PKT_LNG(r)   <= pkt_lng(r);
                        end loop;
                    end if;
                end if;

            when st_TIMEOUT =>
                timeout_en <= '1';
                if RX_OVERFLOW = '1' then
                    next_state  <= st_PASS;
                    for r in 0 to MFB_REGIONS - 1 loop
                        if sof_reg(r) = '1' then
                            TX_SOF(r)       <= sof_reg(r);
                            tx_sof_pos_s(r) <= sof_pos_reg(r);
                            TX_PKT_LNG(r)   <= pkt_lng_reg(r);
                        else
                            TX_SOF(r)       <= sof(r);
                            tx_sof_pos_s(r) <= sof_pos(r);
                            TX_PKT_LNG(r)   <= pkt_lng(r);
                        end if;

                        if eof_reg(r) = '1' then
                            TX_EOF(r)       <= eof_reg(r);
                            tx_eof_pos_s(r) <= eof_pos_reg(r);
                        else
                            TX_EOF(r)       <= eof(r);
                            tx_eof_pos_s(r) <= eof_pos(r);
                        end if;
                    end loop;
                elsif timeout_event = '1' then
                    next_state  <= st_PASS;
                    for r in 0 to MFB_REGIONS - 1 loop
                        if sof_reg(r) = '1' then
                            TX_SOF(r)       <= sof_reg(r);
                            tx_sof_pos_s(r) <= sof_pos_reg(r);
                            TX_PKT_LNG(r)   <= pkt_lng_reg(r);
                        else
                            TX_SOF(r)       <= '0';
                            tx_sof_pos_s(r) <= sof_pos(r);
                            TX_PKT_LNG(r)   <= pkt_lng(r);
                        end if;

                        if eof_reg(r) = '1' then
                            TX_EOF(r)       <= eof_reg(r);
                            tx_eof_pos_s(r) <= eof_pos_reg(r);
                        else
                            TX_EOF(r)       <= eof(r);
                            tx_eof_pos_s(r) <= eof_pos(r);
                        end if;
                    end loop;
                elsif eof_compare = '0' then
                    next_state  <= st_PASS;
                end if;

        end case;
    end process;

    TX_SOF_POS  <= slv_array_ser(tx_sof_pos_s);
    TX_EOF_POS  <= slv_array_ser(tx_eof_pos_s);

    --------------------------------------------------------------------------------
    ---                              EXTERNAL_TIMEOUT                            ---
    --------------------------------------------------------------------------------
    timeout_p: process(all)
    begin
        if rising_edge(CLK) then
            timeout <= '0';
            if timeout_en = '1' then
                if RX_OVERFLOW = '0' then
                    if timeout_cnt = TIMEOUT_CLK_NO then
                        timeout       <= '1';
                        timeout_cnt   <= (others => '0');
                    else
                        timeout_cnt <= timeout_cnt + 1;
                    end if;
                else
                    timeout_cnt <= (others => '0');
                end if;
            else
                timeout_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- This prevents timeout to occur when new packets arrives in timeout event
    timeout_event   <= timeout and eof_compare;

    TX_TIMEOUT_EXT  <= timeout_event when RX_OVERFLOW = '0' else '0';


end architecture;
