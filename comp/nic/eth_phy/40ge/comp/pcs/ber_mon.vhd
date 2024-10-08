-- ber_mon.vhd : Monitors BER by checking block header validity (IEEE802.3
--               figure 82-13)
-- Copyright (C) 2013-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity ber_mon is
    generic (
        NUM_LANES       : natural := 4;
        -- Window size - number of blocks to evaluate BER, max 2^24 (= number of
        -- headers received within the time interval defined in IEEE802.3
        -- section 82.2.18.2.5)
        HDR_CNT_MAX     : natural := 781250;
        -- Number of invalid headers to assert HI_BER.
        HI_BER_TRESHOLD : natural := 97
    );
    port (
        RESET         : in std_logic; -- Synchronous reset
        CLK           : in std_logic;
        CE            : in std_logic;   -- Clock enable for each lane
        SH            : in std_logic_vector(NUM_LANES*2-1 downto 0); -- Sync header for each lane
        --
        BER_CNT       : out std_logic_vector(23 downto 0);           -- Actual BER value (number of invalid blocks within the HDR_CNT_MAX window). See IEEE802.3 82.2.18.2.4: ber_cnt
        BER_COUNT_CLR : in std_logic; -- Async BER_COUNT clear
        BER_COUNT     : out std_logic_vector(21 downto 0);           -- Defined in IEEE802.3 82.2.18.2.4: ber_count
        HI_BER        : out std_logic := '0'
    );
end ber_mon;

architecture behavioral of ber_mon is

    constant BER_COUNTER_MAX : unsigned(BER_COUNT'high downto 0) := (others => '1');

    signal sh_valid             : std_logic_vector(NUM_LANES-1 downto 0);
    signal sh_invalid_count     : natural range 0 to NUM_LANES;
    signal sh_invalid_count_reg : natural range 0 to NUM_LANES;
    signal hdr_cntr             : natural range 0 to (HDR_CNT_MAX+NUM_LANES) := 0; -- Equivalent to IEEE802.3 Fig 82.13: xus_timer
    signal hdr_cntr_ov          : std_logic; -- Header counter overflow
    signal ber_cntr             : natural range 0 to (HDR_CNT_MAX+NUM_LANES) := 0; -- Defined in IEEE802.3 82.2.18.2.4: ber_cnt
    signal ber_cntr_ov          : std_logic; -- BER counter overflow
    signal ber_counter          : unsigned(BER_COUNT'high downto 0) := (others => '0');
    signal ber_counter_inc      : natural range 0 to NUM_LANES;
    signal timer_done           : std_logic;
    signal ber_count_reg        : natural;

begin

    GEN_HDR_CHECK: for i in 0 to NUM_LANES-1 generate
        sh_valid(i) <= SH(i*2) xor SH(i*2+1);
    end generate;

    INVLD_HDR_SUM: process(sh_valid)
    variable count1, count2 : natural range 0 to NUM_LANES;
    begin
        -- Compute number of invalid headers on all lanes
        count1 := 0; count2 := 0;
        for i in 0 to (NUM_LANES/2) loop
            if sh_valid(i) = '0' then
                count1 := count1 + 1;
            end if;
        end loop;
        for i in (NUM_LANES/2+1) to (NUM_LANES - 1) loop
            if sh_valid(i) = '0' then
                count2 := count2 + 1;
            end if;
        end loop;
        sh_invalid_count <= count1 + count2;
    end process;

    CNTRS: process(CLK)
    begin
        if CLK'event and CLK = '1' then
            -- Total header counter
            if (timer_done = '1') or (RESET = '1')  then
                hdr_cntr <= 0;
            elsif (CE = '1') and (hdr_cntr_ov = '0') then
                hdr_cntr <= hdr_cntr + NUM_LANES;
            end if;
            -- Invalid header (BER) counter
            if (timer_done = '1') or (RESET = '1') then
                ber_cntr <= 0;
                ber_count_reg <= 0;
            elsif (CE = '1') then
                ber_count_reg <= sh_invalid_count;
                ber_cntr <= ber_cntr + ber_count_reg;
            end if;

        end if;
    end process;

    -- Total invalid header counter
    BER_COUNTER_P: process(CLK, RESET, BER_COUNT_CLR)
    variable count1, count2 : natural;
    begin
        if (RESET = '1') or (BER_COUNT_CLR = '1') then
            ber_counter <= (others => '0');
        elsif CLK'event and CLK = '1' then
            if (CE = '1') then
                sh_invalid_count_reg <= sh_invalid_count;
                if ((ber_counter + sh_invalid_count_reg) < BER_COUNTER_MAX) then
                    ber_counter_inc <= sh_invalid_count_reg;
                else
                    ber_counter_inc <= 0;
                end if;
                ber_counter <= ber_counter + ber_counter_inc;
            end if;
        end if;
    end process;

    CONTROL: process(CLK)
    begin
        if CLK'event and CLK = '1' then

            if (hdr_cntr_ov = '1') then
                timer_done <= '1';
                BER_CNT    <= std_logic_vector(to_unsigned(ber_cntr, BER_CNT'length));
            else
                timer_done <= '0';
            end if;

            if (ber_cntr_ov = '1') then
                HI_BER <= '1';
            elsif (hdr_cntr_ov = '1') then
                HI_BER <= '0';
            end if;

        end if;
    end process;

    hdr_cntr_ov <= '1' when (hdr_cntr >= (HDR_CNT_MAX-NUM_LANES)) else '0';
    ber_cntr_ov <= '1' when (ber_cntr >= HI_BER_TRESHOLD) else '0';

    BER_COUNT <= std_logic_vector(ber_counter);

end behavioral;
