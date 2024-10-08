-- fp_fifo_ctrl.vhd: This unit handles transfer data from Buffer to FIFO
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FP_FIFO_CTRL is
    generic(
        MFB_REGIONS         : natural := 4;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;

        FIFO_DEPTH          : natural := 512;
        RX_PKT_SIZE_MAX     : natural := 2**10
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        -- FIFO TX interface
        FIFO_TX_SRC_RDY     : in  std_logic;
        FIFO_TX_DST_RDY     : out std_logic;
        FIFO_TX_SOF         : in  std_logic_vector(MFB_REGIONS - 1 downto 0);
        FIFO_TX_EOF         : in  std_logic_vector(MFB_REGIONS - 1 downto 0);
        FIFO_TX_SOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        FIFO_TX_EOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);

        -- Instructions for FIFO_CTRL
        -- Number of packets that make up the SuperPacket
        SPKT_RX_EOF_NUM     : in  std_logic_vector(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
        -- Length of the SuperPacket
        SPKT_RX_LENGTH      : in  std_logic_vector(log2(RX_PKT_SIZE_MAX+ 1) - 1 downto 0);
        SPKT_RX_SRC_RDY     : in  std_logic;
        SPKT_RX_DST_RDY     : out std_logic;

        -- SuperPacket length - valid with SOF
        TX_PKT_LEN_DST_RDY  : in  std_logic;
        TX_PKT_LEN_DATA     : out std_logic_vector(log2(RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);

        -- Channel TX interface
        CH_TX_SRC_RDY       : out std_logic;
        CH_TX_DST_RDY       : in  std_logic;
        CH_TX_SOF           : out std_logic_vector(MFB_REGIONS - 1 downto 0);
        CH_TX_EOF           : out std_logic_vector(MFB_REGIONS - 1 downto 0)
    );
end entity;

architecture FULL of FP_FIFO_CTRL is
    subtype MFB_EOF_BLOCK_SLICE     is natural range max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) - max(1,log2(MFB_REGION_SIZE));

    type fifo_ctrl_fsm is (
        st_LOAD_LNG,        -- Load length of the SuperPacket
        st_FIRST_PAC,       -- Pass SOF of the SuperPacket
        st_PASS             -- Pass rest of the SuperPacket
    );
    signal state, next_state: fifo_ctrl_fsm := st_LOAD_LNG;

    signal pkt_read         : std_logic;
    signal load_en          : std_logic;
    signal pkts_to_read     : unsigned(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
    signal pkt_underflow    : unsigned(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);

    signal block_counter    : std_logic;

    -- Indicator of EOF being in the last block
    signal pkt_cont         : std_logic_vector(MFB_REGIONS downto 0);
    signal pkt_last         : std_logic;

    signal pkts_read        : unsigned(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);

    signal new_sof          : std_logic_vector(MFB_REGIONS     downto 0);
    signal sof_mask         : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal eof_mask         : std_logic_vector(MFB_REGIONS downto 0);

    signal eof_enable       : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal before_one_mask  : std_logic_vector(MFB_REGIONS - 1 downto 0);

    -- Timeout handle
    signal eof_last         : std_logic_vector(MFB_REGIONS - 1 downto 0);
    signal fifo_eof_pos_arr : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);


begin
    -- Evaluate if the packet ends at the end of the region
    fifo_eof_pos_arr  <= slv_array_deser(FIFO_TX_EOF_POS, MFB_REGIONS);
    eof_last_g: for r in 0 to MFB_REGIONS - 1 generate
        eof_last(r) <= '1' when (FIFO_TX_EOF(r) = '1') and (unsigned(fifo_eof_pos_arr(r)(MFB_EOF_BLOCK_SLICE)) = MFB_REGION_SIZE - 1) else '0';
    end generate;

    -- SOF mask
    sof_mask_p: process(all)
        variable index  : integer range 0 to 4;
    begin
        new_sof    <= (others => '0');
        index      := 0;
        for r in 0 to MFB_REGIONS - 1 loop
            if eof_mask(r) = '1' then
                index := r;
                exit;
            end if;
        end loop;

        if pkt_cont(index+1) = '1' then
            new_sof(index)   <= '1';
        else
            if eof_last(index) = '1' then
                new_sof(index+1) <= '1';
            else
                new_sof(index)   <= '1';
            end if;
        end if;

    end process;

    sof_mask_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                sof_mask    <= (0 => '1', others => '0');
            elsif pkt_last = '1' then
                if new_sof(MFB_REGIONS) = '1' then
                    sof_mask    <= (0 => '1', others => '0');
                else
                    sof_mask    <= new_sof(new_sof'high - 1 downto 0);
                end if;
            end if;
        end if;
    end process;

    disable_i: entity work.BEFORE_ONE
        generic map(
           DATA_WIDTH     => MFB_REGIONS,
           IMPLEMENTATION => "BEHAV"
        )
        port map(
           DI => eof_mask(eof_mask'high - 1 downto 0),
           DO => before_one_mask
        );

    processed_eofs_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                eof_enable  <= (others => '0');
            elsif FIFO_TX_DST_RDY = '1' then
                eof_enable  <= (others => '0');
            elsif pkt_last = '1' then
                eof_enable  <= eof_mask(eof_mask'high - 1 downto 0) or before_one_mask;
            end if;
        end if;
    end process;

    -- EOF mask
    eof_mask_p: process(all)
        variable eof_cnt_v  : unsigned(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
        variable index      : integer range 0 to 4;
    begin
        eof_mask     <= (others => '0');

        index     := MFB_REGIONS;
        eof_cnt_v := (others => '0');
        for r in 0 to MFB_REGIONS - 1 loop
            if (FIFO_TX_EOF(r) and (not eof_enable(r))) = '1' then
                eof_cnt_v  := eof_cnt_v + 1;
            else
                eof_cnt_v  := eof_cnt_v;
            end if;

            if pkts_to_read - eof_cnt_v = 0 then
                index   := r;
                exit;
            end if;
        end loop;

        eof_mask(index) <= '1';
        pkts_read       <= eof_cnt_v;
    end process;

    -- Packet continues
    pkt_cont_g : for r in 0 to MFB_REGIONS - 1 generate
        pkt_cont(r+1) <=    (    FIFO_TX_SOF(r) and not FIFO_TX_EOF(r) and not pkt_cont(r)) or
                            (    FIFO_TX_SOF(r) and     FIFO_TX_EOF(r) and     pkt_cont(r)) or
                            (not FIFO_TX_SOF(r) and not FIFO_TX_EOF(r) and     pkt_cont(r));
    end generate;

    -- Transfer to the next word
    pkt_cont_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                pkt_cont(0) <= '0';
            elsif (FIFO_TX_SRC_RDY = '1') and (FIFO_TX_DST_RDY = '1') then
                pkt_cont(0) <= pkt_cont(MFB_REGIONS);
            end if;
        end if;
    end process;

    -- Load the number of sub-packets forming the superpacket
    load_en     <= SPKT_RX_SRC_RDY and SPKT_RX_DST_RDY;
    pkt_read    <= FIFO_TX_SRC_RDY and FIFO_TX_DST_RDY and (or(FIFO_TX_EOF));

    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                pkts_to_read    <= (others => '0');
            elsif load_en = '1' then
                pkts_to_read    <= pkts_to_read + unsigned(SPKT_RX_EOF_NUM);
            elsif block_counter = '1' then
                pkts_to_read    <= pkts_to_read;
            elsif (pkt_read = '1') or (pkt_last = '1') then
                pkts_to_read    <= pkts_to_read - pkts_read;
            end if;
        end if;
    end process;

    -- Indication that some packets are still in the word
    pkt_underflow <= pkts_to_read - to_unsigned(count_ones(FIFO_TX_EOF and (not eof_enable)),pkt_underflow'length);

    fifo_ctrl_reg_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                state   <= st_LOAD_LNG;
            else
                state   <= next_state;
            end if;
        end if;
    end process;

    fifo_ctrl_state_p: process(all)
        variable eof_v : std_logic;
        variable sof_v : std_logic;
    begin
        next_state  <= state;

        CH_TX_SRC_RDY   <= FIFO_TX_SRC_RDY;
        FIFO_TX_DST_RDY <= CH_TX_DST_RDY;

        CH_TX_SOF       <= FIFO_TX_SOF;
        CH_TX_EOF       <= FIFO_TX_EOF;

        SPKT_RX_DST_RDY  <= '0';

        sof_v := or (FIFO_TX_SOF);
        eof_v := or (eof_mask(eof_mask'high - 1 downto 0));

        block_counter   <= '0';
        pkt_last        <= '0';

        case (state) is
            when st_LOAD_LNG    =>
                if FIFO_TX_SRC_RDY = '1' then
                    CH_TX_SRC_RDY   <= '0';
                    FIFO_TX_DST_RDY <= '0';

                    -- Load number of packets within a SuperPacket
                    if SPKT_RX_SRC_RDY = '1' then
                        SPKT_RX_DST_RDY <= '1';
                        next_state      <= st_FIRST_PAC;
                    end if;
                end if;

            when st_FIRST_PAC   =>
                if (FIFO_TX_SRC_RDY and CH_TX_DST_RDY) = '1' then
                    -- Pass SOF of the SuperPacket
                    CH_TX_SOF       <= FIFO_TX_SOF and sof_mask;
                    CH_TX_EOF       <= FIFO_TX_EOF and eof_mask(eof_mask'high - 1 downto 0);
                    if eof_v = '1' then
                        FIFO_TX_DST_RDY <= (not pkt_cont(MFB_REGIONS)) and (not pkt_underflow(pkt_underflow'high));
                        next_state      <= st_LOAD_LNG;
                        pkt_last        <= '1';
                    else
                        next_state      <= st_PASS;
                    end if;
                end if;

            when st_PASS        =>
                if (FIFO_TX_SRC_RDY and CH_TX_DST_RDY) = '1' then
                    -- Mask off SOF and EOF of small packets
                    CH_TX_SOF   <= (others => '0');
                    CH_TX_EOF   <= FIFO_TX_EOF and eof_mask(eof_mask'high - 1 downto 0);
                    if eof_v = '1' then
                        FIFO_TX_DST_RDY <= (not pkt_cont(MFB_REGIONS)) and (not pkt_underflow(pkt_underflow'high));
                        next_state      <= st_LOAD_LNG;
                        pkt_last        <= '1';
                    end if;
                end if;

        end case;
    end process;

    -- Length register
    process(all)
    begin
        if rising_edge(CLK) then
            if (SPKT_RX_SRC_RDY = '1') and (SPKT_RX_DST_RDY = '1') then
                TX_PKT_LEN_DATA <= SPKT_RX_LENGTH;
            end if;
        end if;
    end process;

end architecture;
