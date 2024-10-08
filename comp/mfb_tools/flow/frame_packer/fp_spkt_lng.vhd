-- fp_spkt_lng.vhd: Unit handling size of SuperPacket
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity FP_SPKT_LNG is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8;
        FIFO_DEPTH          : natural := 512;
        TIMEOUT_CLK_NO      : natural := 32;

        -- This component tries to keep the packet size within these limits
        SPKT_SIZE_MIN       : natural := 2**13;
        SPKT_SIZE_MAX       : natural := 2**14;
        DEVICE              : string  := "AGILEX"
    );
    port(
        CLK : in std_logic;
        RST : in std_logic;

        RX_EXT_TIMEOUT     : in  std_logic;
        RX_PKT_SOF         : in  std_logic_vector(MFB_REGIONS - 1 downto 0);
        RX_PKT_EOF         : in  std_logic_vector(MFB_REGIONS - 1 downto 0);
        RX_PKT_SRC_RDY     : in  std_logic;
        RX_PKT_LENGTH      : in  slv_array_t(MFB_REGIONS - 1 downto 0)(log2(SPKT_SIZE_MAX+1)  - 1 downto 0);

        TX_SPKT_EOF_NUM     : out std_logic_vector(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
        TX_SPKT_LENGTH      : out std_logic_vector(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
        TX_SPKT_SRC_RDY     : out std_logic;
        TX_SPKT_DST_RDY     : in  std_logic
    );
end entity;

architecture FULL of FP_SPKT_LNG is
    constant EOF_NUM_LEN   : natural := max(1, log2(MFB_REGIONS*FIFO_DEPTH));

    signal pkt_lng_sum        : unsigned(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal length_reg_d       : unsigned(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal length_reg_q       : unsigned(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal spkt_wr_en         : std_logic;

    -- EOF counter
    signal spkt_eof_num       : unsigned(EOF_NUM_LEN - 1 downto 0);

    --FIFOX
    signal rx_fifox_length    : unsigned(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal rx_fifox_pkt_num   : unsigned(EOF_NUM_LEN - 1 downto 0);
    -- [length][eofs]
    signal rx_fifox_data      : std_logic_vector(((log2(SPKT_SIZE_MAX+ 1) ) + (EOF_NUM_LEN)) - 1 downto 0);
    signal tx_fifox_data      : std_logic_vector(((log2(SPKT_SIZE_MAX+ 1) ) + (EOF_NUM_LEN)) - 1 downto 0);
    signal fifox_empty        : std_logic;
    signal spkt_status        : std_logic_vector(max(1, log2(FIFO_DEPTH)) downto 0);

    -- Timeout
    signal timeout_event      : std_logic;
    signal timeout_en         : std_logic;
    signal timeout_cnt        : unsigned(max(1, log2(TIMEOUT_CLK_NO) + 1) - 1 downto 0):= (others => '0');
    signal timeout            : std_logic;

    -- Enable
    signal rd_en              : std_logic;
    signal eof_cnt            : unsigned(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);

begin

    -- Timeout
    timeout_p: process(all)
    begin
        if rising_edge(CLK) then
            timeout_event <= '0';
            if RX_EXT_TIMEOUT = '0' then
                if timeout_en = '1' then
                    if RX_PKT_SRC_RDY = '0' then
                        if timeout_cnt = TIMEOUT_CLK_NO then
                            timeout_event <= '1';
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
            else
                timeout_cnt <= (others => '0');
            end if;
        end if;
    end process;

    timeout <= ((timeout_event and (not RX_PKT_SRC_RDY)) or RX_EXT_TIMEOUT);

    -- Post timeout handle
    process(all)
    begin
        if rising_edge(CLK) then
            if timeout = '1' then
                timeout_en  <= '0';
            elsif RX_PKT_SRC_RDY = '1' then
                timeout_en  <= '1';
            end if;
        end if;
    end process;

    -- Sum possible length and decide whether it will fit into MTU
    pkt_lng_sum_p: process(all)
        variable pkt_lng_sum_v : u_array_t(MFB_REGIONS downto 0)(log2(SPKT_SIZE_MAX+1) - 1 downto 0);
    begin
        pkt_lng_sum_v   := (others => (others => '0'));
        for r in 0 to MFB_REGIONS - 1 loop
            pkt_lng_sum_v(r + 1)   := pkt_lng_sum_v(r) + unsigned(RX_PKT_LENGTH(r));
        end loop;

        pkt_lng_sum <= pkt_lng_sum_v(MFB_REGIONS);
    end process;

    -- Decide whether the packet will fit into SuperPacket
    process(all)
        variable new_length_v       : unsigned(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
        variable current_length_v   : unsigned(log2(SPKT_SIZE_MAX+ 1)  - 1 downto 0);
    begin
        spkt_wr_en  <= '0';
        new_length_v     := pkt_lng_sum + length_reg_q;
        current_length_v := pkt_lng_sum;

        length_reg_d    <= length_reg_q;

        -- Compare new_length_v with the upper limit of SuperPacket
        -- In other words if new_length >= 8192
        if (or (new_length_v(new_length_v'high downto log2(SPKT_SIZE_MIN)))) = '1' then
            -- overflow - Stored values are sent and the current length is stored
            length_reg_d    <= current_length_v;
            if spkt_eof_num = 0 then
                spkt_wr_en      <= '0';
            else
                spkt_wr_en      <= '1';
            end if;
        else
            -- the current packet will fit into set limits
            if timeout = '1' then
                if rx_fifox_pkt_num = 0 then
                    spkt_wr_en  <= '0';
                else
                    spkt_wr_en  <= '1';
                end if;
            else
                length_reg_d    <= new_length_v;
            end if;

        end if;
    end process;

    -- Length register
    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                length_reg_q  <= (others => '0');
            elsif (timeout = '1') then
                length_reg_q  <= (others => '0');
            elsif (RX_PKT_SRC_RDY = '1') then
                length_reg_q  <= length_reg_d;
            end if;
        end if;
    end process;

    -- EOF counter - This process determines how many packets make up a SuperPacket
    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                spkt_eof_num    <= (others => '0');
            elsif (timeout = '1') then
                spkt_eof_num    <= (others => '0');
            elsif (spkt_wr_en = '1') then
                if (or(RX_PKT_SOF) = '1') then
                    spkt_eof_num    <= to_unsigned(count_ones(RX_PKT_SOF), spkt_eof_num'length);
                else
                    spkt_eof_num    <= (others => '0');
                end if;
            elsif (RX_PKT_SRC_RDY = '1') and (or(RX_PKT_SOF) = '1') then
                spkt_eof_num    <= spkt_eof_num + to_unsigned(count_ones(RX_PKT_SOF), spkt_eof_num'length);
            end if;
        end if;
    end process;

    -- Send data at the same clock when timeout occurs
    timeout_handle_p: process(all)
    begin
        if timeout = '1' then
            rx_fifox_length     <= length_reg_q + pkt_lng_sum;
            rx_fifox_pkt_num    <= spkt_eof_num + to_unsigned(count_ones(RX_PKT_SOF), spkt_eof_num'length);
        else
            rx_fifox_length     <= length_reg_q;
            rx_fifox_pkt_num    <= spkt_eof_num;
        end if;
    end process;

    -- Concatenate number of packets and length of SuperPacket
    -- [spkt_len][eofs]
    --
    rx_fifox_data   <= std_logic_vector(rx_fifox_length) & std_logic_vector(rx_fifox_pkt_num);
    -- rx_fifox_data   <= std_logic_vector(length_reg_q) & std_logic_vector(spkt_eof_num);

    -- Let the output logic decide when to get the length of the superpacket
    pkt_len_fifo_i: entity work.FIFOX
    generic map(
        DATA_WIDTH  => ((log2(SPKT_SIZE_MAX+ 1) ) + (EOF_NUM_LEN)),
        ITEMS       => FIFO_DEPTH,
        DEVICE      => DEVICE
    )
    port map(
        CLK    => CLK,
        RESET  => RST,

        DI     => rx_fifox_data,
        WR     => spkt_wr_en,
        FULL   => open,
        AFULL  => open,
        STATUS => spkt_status,

        DO     => tx_fifox_data,
        RD     => TX_SPKT_DST_RDY,
        EMPTY  => fifox_empty,
        AEMPTY => open
    );

    -- EOF counter - to find out whether the SP is already in the FIFO or not
    eof_cnt_p: process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                eof_cnt <= (others => '0');
            elsif (TX_SPKT_SRC_RDY = '1') and (TX_SPKT_DST_RDY = '1') then
                eof_cnt <= eof_cnt - unsigned(tx_fifox_data(EOF_NUM_LEN - 1 downto 0));
                if (or(RX_PKT_EOF) = '1') and (RX_PKT_SRC_RDY = '1') then
                    eof_cnt <= eof_cnt - unsigned(tx_fifox_data(EOF_NUM_LEN - 1 downto 0)) + to_unsigned(count_ones(RX_PKT_EOF), eof_cnt'length);
                end if;
            elsif (or(RX_PKT_EOF) = '1') and (RX_PKT_SRC_RDY = '1') then
                eof_cnt <= eof_cnt + to_unsigned(count_ones(RX_PKT_EOF), eof_cnt'length);
            end if;
        end if;
    end process;

    -- Highest bit indicates whether the SP is ready or not (1 = not ready, 0 = ready)
    process(all)
        variable sp_completed_cnt_v : unsigned(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) downto 0);
    begin
        sp_completed_cnt_v := ('0' & eof_cnt) - unsigned(tx_fifox_data(EOF_NUM_LEN - 1 downto 0));

        if fifox_empty = '0' then
            rd_en   <= not(sp_completed_cnt_v(sp_completed_cnt_v'high));
        else
            rd_en   <= '0';
        end if;
    end process;

    TX_SPKT_SRC_RDY <= rd_en;
    TX_SPKT_EOF_NUM <= tx_fifox_data(EOF_NUM_LEN - 1 downto 0);
    TX_SPKT_LENGTH  <= tx_fifox_data(tx_fifox_data'high downto EOF_NUM_LEN);
end architecture;
