-- mfb_generator_core.vhd: This component generates packets of desired length.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity MFB_GENERATOR_CORE is
    Generic (
        -- number of regions in a data word
        REGIONS         : natural := 2;
        -- number of blocks in a region
        REGION_SIZE     : natural := 8;
        -- number of items in a block
        BLOCK_SIZE      : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH      : natural := 8;
        -- the width of length signal
        LENGTH_WIDTH    : natural := 10
    );
    Port (
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- Generator control special dynamic interface
        -- =====================================================================
        -- At begin are values in all regions same, when is set ACCEPT in some
        -- region, then in next region must be new value (in same clock cycle).
        GEN_LENGTH     : in  slv_array_t(REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
        GEN_VALID      : in  std_logic_vector(REGIONS-1 downto 0);
        GEN_ACCEPT     : out std_logic_vector(REGIONS-1 downto 0);

        -- TX MFB interface without data
        -- =====================================================================
        TX_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_GENERATOR_CORE is

    constant SOF_POS_WIDTH  : natural := log2(REGION_SIZE);
    constant EOF_POS_WIDTH  : natural := log2(REGION_SIZE*BLOCK_SIZE);
    constant BLOCK_WIDTH    : natural := log2(BLOCK_SIZE);
    constant WORD_CNT_WIDTH : natural := LENGTH_WIDTH-log2(REGIONS)-EOF_POS_WIDTH;

    signal s_word_cnt                : slv_array_t(REGIONS+1-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_word_cnt_clr            : std_logic_vector(REGIONS-1 downto 0);
    signal s_region_full             : std_logic_vector(REGIONS-1 downto 0);
    signal s_set_sof                 : std_logic_vector(REGIONS-1 downto 0);
    signal s_sof_pos_shared_region   : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_sof_pos                 : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_sof_pos_ext             : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_set_sof_fake            : std_logic_vector(REGIONS-1 downto 0);

    signal s_eof_offset_curr         : slv_array_t(REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal s_eof_offset_curr_regions : slv_array_t(REGIONS-1 downto 0)(LENGTH_WIDTH-EOF_POS_WIDTH-1 downto 0);
    signal s_eof_curr_ok             : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_offset_prev_new     : slv_array_t(REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal s_eof_offset_prev_word    : slv_array_t(REGIONS-1 downto 0)(WORD_CNT_WIDTH-1 downto 0);
    signal s_eof_offset_prev_region  : slv_array_t(REGIONS-1 downto 0)(log2(REGIONS)-1 downto 0);
    signal s_eof_prev_word_ok        : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_prev_region_ok      : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_prev_ok             : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_prev_pkt            : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_curr_pkt            : std_logic_vector(REGIONS-1 downto 0);
    signal s_set_eof                 : std_logic_vector(REGIONS-1 downto 0);
    signal s_eof_pos                 : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    signal s_eof_offset_prev         : slv_array_t(REGIONS+1-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal s_need_set_eof            : std_logic_vector(REGIONS+1-1 downto 0);

    signal s_src_rdy                 : std_logic;
    signal s_pkt_accept              : std_logic_vector(REGIONS-1 downto 0);

begin

    assert (REGION_SIZE > 1)
        report "MFB_GENERATOR_CORE: Unsupported REGION_SIZE, use higher than 1!"
        severity FAILURE;

    ----------------------------------------------------------------------------
    -- MFB WORD COUNTER
    ----------------------------------------------------------------------------

    word_cnt_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_word_cnt(0) <= (others => '0');
            elsif (TX_MFB_DST_RDY = '1') then
                s_word_cnt(0) <= std_logic_vector(unsigned(s_word_cnt(REGIONS)) + 1);
            end if;
        end if;
    end process;

    word_cnt_g : for r in 0 to REGIONS-1 generate
        s_word_cnt_clr(r) <= or s_set_sof_fake(r downto 0);
        s_word_cnt(r+1) <= (others => '0') when (s_word_cnt_clr(r) = '1') else s_word_cnt(0);

        --word_cnt_p : process (all)
        --    variable v_word_cnt : std_logic_vector(WORD_CNT_WIDTH-1 downto 0);
        --begin
        --    v_word_cnt := s_word_cnt(r);
        --    word_cnt_l : for i in 0 to r loop
        --        if (s_set_sof_fake(i) = '1') then
        --            v_word_cnt := (others => '0');
        --        end if;
        --    end loop;
        --    s_word_cnt(r+1) <= v_word_cnt;
        --end process;
        --s_word_cnt(r+1) <= (others => '0') when (s_set_sof_fake(r) = '1') else s_word_cnt(r);
    end generate;

    ----------------------------------------------------------------------------
    -- PACKET GENERATION
    ----------------------------------------------------------------------------

    pkt_gen_g : for r in 0 to REGIONS-1 generate
        -- region is full when previous packet ending on last block
        s_region_full(r) <= and s_eof_offset_prev(r)(EOF_POS_WIDTH-1 downto BLOCK_WIDTH);
        -- set SOF in this region
        s_set_sof(r) <= (GEN_VALID(r) and not s_need_set_eof(r)) or (GEN_VALID(r) and s_need_set_eof(r) and s_eof_prev_ok(r) and not s_region_full(r));
        -- SOF_POS for shared region (region with two packet)
        s_sof_pos_shared_region(r) <= std_logic_vector(unsigned(s_eof_offset_prev(r)(EOF_POS_WIDTH-1 downto BLOCK_WIDTH)) + 1);
        -- set correct SOF_POS in this region
        s_sof_pos(r) <= s_sof_pos_shared_region(r) when (s_need_set_eof(r) = '1') else (others => '0');
        -- extended SOF_POS value
        s_sof_pos_ext(r) <= s_sof_pos(r) & std_logic_vector(unsigned(to_unsigned(0,BLOCK_WIDTH)));
        -- SOF FAKE is inaccurate SOF, requires less logic
        s_set_sof_fake(r) <= (not s_need_set_eof(r)) or (s_need_set_eof(r) and s_eof_prev_ok(r));

        -- =====================================================================
        -- the current EOF offset is length minus 1, current packet start in firts block every time
        s_eof_offset_curr(r) <= std_logic_vector(unsigned(GEN_LENGTH(r)) - 1);
        -- unpack regions (region+word) part of current EOF offset
        s_eof_offset_curr_regions(r) <= s_eof_offset_curr(r)(LENGTH_WIDTH-1 downto EOF_POS_WIDTH);
        -- set when current EOF is in this region
        s_eof_curr_ok(r) <= '1' when (unsigned(s_eof_offset_curr_regions(r)) = 0) else '0';

        -- =====================================================================
        -- create new previous EOF offset signal
        s_eof_offset_prev_new(r) <= std_logic_vector(unsigned(s_eof_offset_curr(r)) + (r*REGION_SIZE*BLOCK_SIZE) + unsigned(s_sof_pos_ext(r)));
        -- unpack previous EOF offset to word and region part
        s_eof_offset_prev_word(r)   <= s_eof_offset_prev(r)(LENGTH_WIDTH-1 downto log2(REGIONS)+EOF_POS_WIDTH);
        s_eof_offset_prev_region(r) <= s_eof_offset_prev(r)(log2(REGIONS)+EOF_POS_WIDTH-1 downto EOF_POS_WIDTH);
        -- checking if current position matches the previous EOF offset
        s_eof_prev_word_ok(r)   <= '1' when (unsigned(s_eof_offset_prev_word(r)) = unsigned(s_word_cnt(r))) else '0';
        s_eof_prev_region_ok(r) <= '1' when ((REGIONS = 1) or (unsigned(s_eof_offset_prev_region(r)) = r)) else '0';
        s_eof_prev_ok(r)        <= s_eof_prev_word_ok(r) and s_eof_prev_region_ok(r);

        -- end of packet which start in some previous region
        s_eof_prev_pkt(r) <= s_need_set_eof(r) and s_eof_prev_ok(r);
        -- end of packet which start in current region
        s_eof_curr_pkt(r) <= GEN_VALID(r) and s_eof_curr_ok(r) and not s_need_set_eof(r);
        -- set EOF in this region
        s_set_eof(r) <= s_eof_prev_pkt(r) or s_eof_curr_pkt(r);
        -- set correct EOF_POS in this region
        s_eof_pos(r) <= s_eof_offset_prev(r)(EOF_POS_WIDTH-1 downto 0) when (s_need_set_eof(r) = '1') else s_eof_offset_curr(r)(EOF_POS_WIDTH-1 downto 0);

        -- =====================================================================
        -- create signal with previous EOF offset for next region
        s_eof_offset_prev(r+1) <= s_eof_offset_prev_new(r) when (s_set_sof_fake(r) = '1') else s_eof_offset_prev(r);

        --process (s_set_sof_fake,s_eof_offset_prev,s_eof_offset_prev_new)
        --    variable v_eof_offset_prev : std_logic_vector(LENGTH_WIDTH-1 downto 0);
        --begin
        --    v_eof_offset_prev := s_eof_offset_prev(0);
        --    eof_offset_prev_l : for i in 0 to r loop
        --        if (s_set_sof_fake(i) = '1') then
        --            v_eof_offset_prev := s_eof_offset_prev_new(i);
        --        end if;
        --    end loop;
        --    s_eof_offset_prev(r+1) <= v_eof_offset_prev;
        --end process;

        -- control of creating EOF signal
        s_need_set_eof(r+1) <= '1' when ((s_set_sof(r) = '1' and s_set_eof(r) = '0') or (s_set_sof(r) = '1' and s_set_eof(r) = '1' and s_need_set_eof(r) = '1')) else
                               '0' when (s_set_eof(r) = '1') else s_need_set_eof(r);
    end generate;

    s_src_rdy <= (or s_set_sof) or s_need_set_eof(0);

    eof_offset_prev_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then
                s_eof_offset_prev(0) <= s_eof_offset_prev(REGIONS);
            end if;
        end if;
    end process;

    need_set_eof_per_wb_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_need_set_eof(0) <= '0';
            elsif (TX_MFB_DST_RDY = '1') then
                s_need_set_eof(0) <= s_need_set_eof(REGIONS);
            end if;
        end if;
    end process;

    pkt_accept_p : process (s_set_sof)
        variable var_cnt    : integer range 0 to REGIONS;
        variable var_accept : std_logic_vector(REGIONS-1 downto 0);
    begin
        var_accept := (others => '0');
        var_cnt := 0;
        temp_or : for r in 0 to REGIONS-1 loop
            if (s_set_sof(r) = '1') then
                var_accept(var_cnt) := '1';
                var_cnt := var_cnt + 1;
            end if;
        end loop;
        s_pkt_accept <= var_accept;
    end process;

    -----------------------------------------------------------------------------
    -- OUTPUT SIGNALS
    -----------------------------------------------------------------------------

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then
                TX_MFB_SOF_POS <= slv_array_ser(s_sof_pos,REGIONS,SOF_POS_WIDTH);
                TX_MFB_EOF_POS <= slv_array_ser(s_eof_pos,REGIONS,EOF_POS_WIDTH);
                TX_MFB_SOF     <= s_set_sof;
                TX_MFB_EOF     <= s_set_eof;
                TX_MFB_SRC_RDY <= s_src_rdy;
            end if;
            if (RESET = '1') then
                TX_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    GEN_ACCEPT <= s_pkt_accept;

end architecture;
