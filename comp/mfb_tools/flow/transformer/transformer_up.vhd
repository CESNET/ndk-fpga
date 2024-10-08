-- transformer_up.vhd: Implementation of UP architecture of MFB transformer component
-- Copyright (C) 2020 CESNET
-- Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity MFB_TRANSFORMER_UP is
    generic (
        RX_REGIONS  : integer := 2;
        TX_REGIONS  : integer := 4;
        REGION_SIZE : integer := 1;
        BLOCK_SIZE  : integer := 8;
        ITEM_WIDTH  : integer := 32;
        META_WIDTH  : integer := 0
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- MFB input interface
        RX_DATA    : in  std_logic_vector(RX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META    : in  std_logic_vector(RX_REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOP     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_EOP     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_SOP_POS : in  std_logic_vector(RX_REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        RX_EOP_POS : in  std_logic_vector(RX_REGIONS*max(1, log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- MFB output interface
        TX_DATA    : out std_logic_vector(TX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META    : out std_logic_vector(TX_REGIONS*META_WIDTH-1 downto 0);
        TX_SOP     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_EOP     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_SOP_POS : out std_logic_vector(TX_REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        TX_EOP_POS : out std_logic_vector(TX_REGIONS*max(1, log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of MFB_TRANSFORMER_UP is

    -- output/input ratio
    constant TX_BLOCKS : integer := TX_REGIONS/RX_REGIONS;

    -- calculation constants
    constant RX_DATA_WIDTH    : integer := RX_REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant RX_META_WIDTH    : integer := RX_REGIONS*META_WIDTH;
    constant RX_SOP_POS_WIDTH : integer := RX_REGIONS*log2(REGION_SIZE);
    constant RX_EOP_POS_WIDTH : integer := RX_REGIONS*log2(REGION_SIZE*BLOCK_SIZE);

    type fsm_t is (st_idle, st_load);

    signal rx_timout_cnt  : unsigned(log2(16*TX_BLOCKS)-1 downto 0);
    signal timeout_export : std_logic;

    signal fsm_pst : fsm_t;
    signal fsm_nst : fsm_t;

    -- output registers
    signal tx_data_reg    : std_logic_vector(TX_DATA'range);
    signal tx_meta_reg    : std_logic_vector(TX_META'range);
    signal tx_sop_reg     : std_logic_vector(TX_SOP'range);
    signal tx_eop_reg     : std_logic_vector(TX_EOP'range);
    signal tx_sop_pos_reg : std_logic_vector(TX_SOP_POS'range);
    signal tx_eop_pos_reg : std_logic_vector(TX_EOP_POS'range);

    -- counter signal
    signal cnt      : unsigned(log2(TX_BLOCKS+1)-1 downto 0);
    signal cnt_next : unsigned(log2(TX_BLOCKS+1)-1 downto 0);

    -- export incomplete word
    signal last_eop   : std_logic;
    signal export     : std_logic;
    signal export_sel : std_logic_vector(log2(TX_BLOCKS)-1 downto 0);
    signal mask       : std_logic_vector(TX_SOP'range);

    -- unmasked sop and eop
    signal tx_sop_unmasked : std_logic_vector(TX_SOP'range);
    signal tx_eop_unmasked : std_logic_vector(TX_EOP'range);

begin

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (rx_timout_cnt(rx_timout_cnt'high) = '0') then
                rx_timout_cnt <= rx_timout_cnt + 1;
            end if;
            if (RESET = '1' or RX_SRC_RDY = '1') then
                rx_timout_cnt <= (others => '0');
            end if;
        end if;
    end process;

    timeout_export <= rx_timout_cnt(rx_timout_cnt'high) and last_eop;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            fsm_pst <= fsm_nst;
            cnt <= cnt_next;
            if (RESET = '1') then
                fsm_pst <= st_idle;
                cnt <= (others => '0');
            end if;
        end if;
    end process;

    process (all)
    begin
        fsm_nst <= fsm_pst;
        cnt_next <= cnt;
        TX_SRC_RDY <= '0';
        RX_DST_RDY <= TX_DST_RDY;
        case (fsm_pst) is
            when st_idle =>
                RX_DST_RDY <= '1';
                if (RX_SRC_RDY = '1') then
                    fsm_nst <= st_load;
                    cnt_next <= cnt + 1;
                end if;

            when st_load =>
                if (cnt=TX_BLOCKS or timeout_export='1') then
                    TX_SRC_RDY <= '1';
                    RX_DST_RDY <= TX_DST_RDY;
                    if (TX_DST_RDY = '1') then
                        cnt_next <= (others => '0');
                        fsm_nst <= st_idle;
                        if (RX_SRC_RDY = '1') then
                            cnt_next <= to_unsigned(1,cnt_next'length);
                            fsm_nst <= st_load;
                        end if;
                    end if;
                else
                    RX_DST_RDY <= '1';
                    if (RX_SRC_RDY = '1') then
                        cnt_next <= cnt + 1;
                    end if;
                end if;
        end case;
    end process;

    export_sel <= std_logic_vector(cnt(log2(TX_BLOCKS)-1 downto 0));

    -- shift registers with output data
    shregs_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (RX_SRC_RDY = '1' and RX_DST_RDY = '1') then
                tx_data_reg    <= RX_DATA & tx_data_reg(TX_BLOCKS*RX_DATA_WIDTH-1 downto RX_DATA_WIDTH);
                tx_meta_reg    <= RX_META & tx_meta_reg(TX_BLOCKS*RX_META_WIDTH-1 downto RX_META_WIDTH);
                tx_sop_reg     <= RX_SOP & tx_sop_reg(TX_REGIONS-1 downto RX_REGIONS);
                tx_eop_reg     <= RX_EOP & tx_eop_reg(TX_REGIONS-1 downto RX_REGIONS);
                tx_eop_pos_reg <= RX_EOP_POS & tx_eop_pos_reg(TX_BLOCKS*RX_EOP_POS_WIDTH-1 downto RX_EOP_POS_WIDTH);
            end if;
        end if;
    end process;

    -- sop_pos has significance only when REGION_SIZE > 1
    gen_sop_pos_g : if REGION_SIZE > 1 generate
        sop_pos_p : process(CLK)
        begin
            if rising_edge(CLK)then
                if (RX_SRC_RDY = '1' and RX_DST_RDY = '1') then
                    tx_sop_pos_reg <= RX_SOP_POS & tx_sop_pos_reg(TX_BLOCKS*RX_SOP_POS_WIDTH-1 downto RX_SOP_POS_WIDTH);
                end if;
            end if;
        end process;

        sop_pos_shifter_i : entity work.BARREL_SHIFTER_GEN
        generic map (
            BLOCKS     => TX_BLOCKS,
            BLOCK_SIZE => RX_SOP_POS_WIDTH,
            SHIFT_LEFT => true)
        port map (
            DATA_IN    => tx_sop_pos_reg,
            DATA_OUT   => TX_SOP_POS,
            SEL        => export_sel
        );
    end generate;

    gen_sop_pos_fake_g : if REGION_SIZE = 1 generate
        tx_sop_pos_reg <= (others => '0');
        TX_SOP_POS     <= (others => '0');
    end generate;

    -- mask for SOP and EOP according to valid data in register
    mask_p : process(export_sel)
        variable tmp : std_logic_vector(TX_SOP'range);
    begin
        tmp := (others => '1');
        if unsigned(export_sel) /= 0 then
            for i in TX_REGIONS downto 1 loop
                if i > to_integer(unsigned(export_sel))*RX_REGIONS then
                    tmp := '0' & tmp(TX_REGIONS-1 downto 1);
                end if;
            end loop;
        end if;
        mask <= tmp;
    end process;

    -- output barrel shifters
    data_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS => TX_BLOCKS,
        BLOCK_SIZE => RX_DATA_WIDTH,
        SHIFT_LEFT => true)
    port map (
        DATA_IN => tx_data_reg,
        DATA_OUT => TX_DATA,
        SEL => export_sel
    );

    meta_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS => TX_BLOCKS,
        BLOCK_SIZE => RX_META_WIDTH,
        SHIFT_LEFT => true)
    port map (
        DATA_IN => tx_meta_reg,
        DATA_OUT => TX_META,
        SEL => export_sel
    );

    sop_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS => TX_BLOCKS,
        BLOCK_SIZE => RX_REGIONS,
        SHIFT_LEFT => true)
    port map (
        DATA_IN => tx_sop_reg,
        DATA_OUT => tx_sop_unmasked,
        SEL => export_sel
    );

    eop_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS => TX_BLOCKS,
        BLOCK_SIZE => RX_REGIONS,
        SHIFT_LEFT => true)
    port map (
        DATA_IN => tx_eop_reg,
        DATA_OUT => tx_eop_unmasked,
        SEL => export_sel
    );

    eop_pos_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS => TX_BLOCKS,
        BLOCK_SIZE => RX_EOP_POS_WIDTH,
        SHIFT_LEFT => true)
    port map (
        DATA_IN => tx_eop_pos_reg,
        DATA_OUT => TX_EOP_POS,
        SEL => export_sel
    );

    TX_SOP <= tx_sop_unmasked and mask;
    TX_EOP <= tx_eop_unmasked and mask;

    -- decides whether EOP came last for REGION_SIZE = 1
    last_eop_fake_g : if REGION_SIZE = 1 generate
        last_eop_fake_p : process(tx_sop_reg, tx_eop_reg)
        begin
            last_eop <= '0';
            for i in 0 to TX_REGIONS-1 loop
                if tx_eop_reg(i) = '1' then
                    last_eop <= '1';
                elsif tx_sop_reg(i) = '1' then
                    last_eop <= '0';
                end if;
            end loop;
        end process;
    end generate;

    -- decides whether EOP came last for REGION_SIZE /= 1
    last_eop_g : if REGION_SIZE /= 1 generate
        last_eop_p : process(tx_sop_reg, tx_eop_reg, tx_sop_pos_reg, tx_eop_pos_reg)
        begin
            last_eop <= '0';
            for i in 0 to TX_REGIONS-1 loop
                if tx_eop_reg(i) = '1' then
                    if tx_sop_reg(i) = '1' and to_integer(unsigned(tx_sop_pos_reg((i+1)*log2(REGION_SIZE)-1 downto i*log2(REGION_SIZE))))*BLOCK_SIZE > to_integer(unsigned(tx_eop_pos_reg((i+1)*log2(REGION_SIZE*BLOCK_SIZE)-1 downto i*log2(REGION_SIZE*BLOCK_SIZE)))) then
                        last_eop <= '0';
                    else
                        last_eop <= '1';
                    end if;
                elsif tx_sop_reg(i) = '1' then
                    last_eop <= '0';
                end if;
            end loop;
        end process;
    end generate;

end architecture;
