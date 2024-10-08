-- umii_enc.vhd: Universal MII encoder (XGMII, XLGMII, CGMII, CDMII)
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity UMII_ENC is
    generic(
        -- =====================================================================
        -- UNIVERSAL MII ENCODER CONFIGURATION:
        -- =====================================================================
        -- Data width of MII data signal, must be power of two, minimum is 64
        MII_DW      : natural := 2048;
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        -- WARNING: The MFB parameters are calculated automatically, they cannot
        -- be changed manually!!!
        REGIONS     : natural := max(MII_DW/512,1);
        BLOCK_SIZE  : natural := tsel((MII_DW=64),4,8); -- SOF must be aligned by 8 or 4 bytes
        ITEM_WIDTH  : natural := 8; -- must be 8, one item = one byte
        REGION_SIZE : natural := (MII_DW/REGIONS)/(BLOCK_SIZE*ITEM_WIDTH)
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;
        -- =====================================================================
        -- INPUT MFB LIKE INTERFACE
        -- =====================================================================
        RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;
        -- =====================================================================
        -- OUTPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
        -- =====================================================================
        -- MII signal with data bits
        MII_TXD    : out std_logic_vector(MII_DW-1 downto 0);
        -- MII signal with control flags
        MII_TXC    : out std_logic_vector(MII_DW/8-1 downto 0);
        -- Valid signal of MII word (optional).
        MII_VLD    : out std_logic;
        -- Ready signal of MII word, set to VCC if this signal is not needed.
        MII_RDY    : in  std_logic := '1'
   );
end entity;

architecture FULL of UMII_ENC is

    constant MII_CW           : natural := MII_DW/8;
    constant WORD_BLOCKS      : natural := REGIONS*REGION_SIZE;
    constant SOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_SIZE     : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant LOG2_REGION_SIZE : natural := log2(REGION_SIZE);
    constant LOG2_BLOCK_SIZE  : natural := log2(BLOCK_SIZE);

    -- logic stage 1
    signal s_rx_sof_vld        : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof_vld        : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_sof_pos_arr    : slv_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
    signal s_rx_eof_pos_arr    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
    signal s_sfd_pos_plus_arr  : u_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE+1-1 downto 0);
    signal s_sfd_pos_under_bit : std_logic_vector(REGIONS-1 downto 0);
    signal s_sfd_vld           : std_logic_vector(REGIONS-1 downto 0);
    signal s_sfd_pos           : u_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
    signal s_sfd_in_prev_word  : std_logic;
    signal s_efd_pos_plus_arr  : u_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE+1-1 downto 0);
    signal s_efd_pos_over_bit  : std_logic_vector(REGIONS+1-1 downto 0);
    signal s_efd_vld           : std_logic_vector(REGIONS-1 downto 0);
    signal s_efd_pos           : u_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);

    -- register stage 1
    signal s_data_reg1         : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_sfd_vld_reg1      : std_logic_vector(REGIONS-1 downto 0);
    signal s_sfd_pos_reg1      : u_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
    signal s_efd_vld_reg1      : std_logic_vector(REGIONS-1 downto 0);
    signal s_efd_pos_reg1      : u_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);

    -- logic stage 2
    signal s_sfd_vld_final     : std_logic_vector(REGIONS-1 downto 0);
    signal s_sfd_pos_final     : u_array_t(REGIONS-1 downto 0)(SOF_POS_SIZE-1 downto 0);
    signal s_incomplete_word   : std_logic_vector(REGIONS+1-1 downto 0);
    signal s_word_vld          : std_logic;
    signal s_sfd_pos_oh        : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_efd_pos_oh        : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_incomplete_block  : std_logic_vector(WORD_BLOCKS+1-1 downto 0);
    signal s_block_vld         : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_efd_ctrl_wb       : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE-1 downto 0);
    signal s_data_wb           : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_efd_data_wb       : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);

    -- register stage 2
    signal s_data_wb_reg2      : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_sfd_pos_oh_reg2   : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_efd_pos_oh_reg2   : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_block_vld_reg2    : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_efd_ctrl_wb_reg2  : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE-1 downto 0);
    signal s_efd_data_wb_reg2  : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_valid_reg2        : std_logic;

    -- logic stage 3
    signal s_sfd_next_blk      : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_block_state       : slv_array_t(WORD_BLOCKS-1 downto 0)(4-1 downto 0);
    signal s_mii_mux_sel       : slv_array_t(WORD_BLOCKS-1 downto 0)(3-1 downto 0);
    signal s_mii_ctrl_wb       : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE-1 downto 0);
    signal s_mii_ctrl          : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE-1 downto 0);
    signal s_mii_data_wb       : slv_array_t(WORD_BLOCKS-1 downto 0)(BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_mii_data          : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_mii_vld_wb        : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_mii_vld           : std_logic;

    -- register stage 3
    signal s_mii_data_reg3     : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal s_mii_ctrl_reg3     : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE-1 downto 0);
    signal s_mii_vld_reg3      : std_logic;

begin

    -- asserts
    assert ((BLOCK_SIZE = 8 or BLOCK_SIZE = 4) and ITEM_WIDTH = 8)
        report "UMII_ENC: BLOCK_SIZE must be 8 or 4 and ITEM_WIDTH must be 8, other values are not supported!!!"
        severity failure;

    -- =========================================================================
    -- 1. LOGIC STAGE
    -- =========================================================================

    RX_DST_RDY <= MII_RDY;

    s_rx_sof_vld <= RX_SOF and RX_SRC_RDY;
    s_rx_eof_vld <= RX_EOF and RX_SRC_RDY;

    rx_sof_pos_arr_g : if REGION_SIZE > 1 generate
        s_rx_sof_pos_arr <= slv_array_deser(RX_SOF_POS,REGIONS,SOF_POS_SIZE);
    else generate
        s_rx_sof_pos_arr <= (others => (others => '0'));
    end generate;

    s_rx_eof_pos_arr <= slv_array_deser(RX_EOF_POS,REGIONS,EOF_POS_SIZE);

    sfd_in_prev_region_g : for r in 0 to REGIONS-1 generate
        -- Position of SFD flag, SFD is one byte before SOF.
        s_sfd_pos_plus_arr(r) <= resize(unsigned(s_rx_sof_pos_arr(r)),(SOF_POS_SIZE+1)) - 1;
        -- Detect case when SFD flag underflow to previous region.
        s_sfd_pos_under_bit(r) <= s_sfd_pos_plus_arr(r)(SOF_POS_SIZE) and s_rx_sof_vld(r);
    end generate;

    sfd_flag_g : for r in 0 to REGIONS-2 generate
        s_sfd_vld(r) <= (s_rx_sof_vld(r) and not s_sfd_pos_under_bit(r)) or s_sfd_pos_under_bit(r+1);
        s_sfd_pos(r) <= to_unsigned(REGION_SIZE-1,SOF_POS_SIZE) when (s_sfd_pos_under_bit(r+1) = '1') else
                        s_sfd_pos_plus_arr(r)(SOF_POS_SIZE-1 downto 0);
    end generate;
    s_sfd_vld(REGIONS-1) <= s_rx_sof_vld(REGIONS-1) and not s_sfd_pos_under_bit(REGIONS-1);
    s_sfd_pos(REGIONS-1) <= unsigned(s_sfd_pos_plus_arr(REGIONS-1)(SOF_POS_SIZE-1 downto 0));

    s_sfd_in_prev_word <= s_sfd_pos_under_bit(0);

    efd_flag_g : for r in 0 to REGIONS-1 generate
        -- Position of EFD flag, EFD is one byte after EOF.
        s_efd_pos_plus_arr(r) <= resize(unsigned(s_rx_eof_pos_arr(r)),(EOF_POS_SIZE+1)) + 1;
        -- Detect case when EFD flag overflow to next region.
        s_efd_pos_over_bit(r+1) <= s_efd_pos_plus_arr(r)(EOF_POS_SIZE) and s_rx_eof_vld(r);
        -- EFD flag of current region.
        s_efd_vld(r) <= (s_rx_eof_vld(r) and not s_efd_pos_over_bit(r+1)) or s_efd_pos_over_bit(r);
        -- EFD flag position of current region.
        s_efd_pos(r) <= to_unsigned(0,EOF_POS_SIZE) when (s_efd_pos_over_bit(r) = '1') else
                        s_efd_pos_plus_arr(r)(EOF_POS_SIZE-1 downto 0);
    end generate;

    efd_pos_over_bit_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_efd_pos_over_bit(0) <= '0';
            elsif (MII_RDY = '1') then
                s_efd_pos_over_bit(0) <= s_efd_pos_over_bit(REGIONS);
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 1. REGISTERS STAGE
    -- =========================================================================

    reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (MII_RDY = '1') then
                s_data_reg1    <= RX_DATA;
                s_sfd_pos_reg1 <= s_sfd_pos;
                s_efd_pos_reg1 <= s_efd_pos;
            end if;
        end if;
    end process;

    vld_reg1_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_sfd_vld_reg1 <= (others => '0');
                s_efd_vld_reg1 <= (others => '0');
            elsif (MII_RDY = '1') then
                s_sfd_vld_reg1 <= s_sfd_vld;
                s_efd_vld_reg1 <= s_efd_vld;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 2. LOGIC STAGE
    -- =========================================================================

    sfd_flag_final_g : for r in 0 to REGIONS-2 generate
        s_sfd_vld_final(r) <= s_sfd_vld_reg1(r);
        s_sfd_pos_final(r) <= s_sfd_pos_reg1(r);
    end generate;
    s_sfd_vld_final(REGIONS-1) <= s_sfd_vld_reg1(REGIONS-1) or s_sfd_in_prev_word;
    s_sfd_pos_final(REGIONS-1) <= to_unsigned(REGION_SIZE-1,SOF_POS_SIZE) when (s_sfd_in_prev_word = '1') else
                                  s_sfd_pos_reg1(REGIONS-1);

    incomplete_word_g : for r in 0 to REGIONS-1 generate
        s_incomplete_word(r+1) <= (s_sfd_vld_final(r) and not s_efd_vld_reg1(r) and not s_incomplete_word(r)) or
            (s_sfd_vld_final(r) and s_efd_vld_reg1(r) and s_incomplete_word(r)) or
            (not s_sfd_vld_final(r) and not s_efd_vld_reg1(r) and s_incomplete_word(r));
    end generate;

    incomplete_word_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_incomplete_word(0) <= '0';
            elsif (MII_RDY = '1') then
                s_incomplete_word(0) <= s_incomplete_word(REGIONS);
            end if;
        end if;
    end process;

    s_word_vld <= (or s_sfd_vld_final) or s_incomplete_word(0);

    sfd_efd_oh_g : for r in 0 to REGIONS-1 generate
        sfd_oh_g : if REGION_SIZE > 1 generate
            bin2hot_sfd_i : entity work.BIN2HOT
            generic map(
                DATA_WIDTH => LOG2_REGION_SIZE
            )
            port map(
                EN     => s_sfd_vld_final(r),
                INPUT  => std_logic_vector(s_sfd_pos_final(r)),
                OUTPUT => s_sfd_pos_oh((r+1)*REGION_SIZE-1 downto r*REGION_SIZE)
            );
        else generate
            s_sfd_pos_oh <= s_sfd_vld_final;
        end generate;

        bin2hot_efd_i : entity work.BIN2HOT
        generic map(
            DATA_WIDTH => LOG2_REGION_SIZE
        )
        port map(
            EN     => s_efd_vld_reg1(r),
            INPUT  => std_logic_vector(s_efd_pos_reg1(r)(LOG2_REGION_SIZE+LOG2_BLOCK_SIZE-1 downto LOG2_BLOCK_SIZE)),
            OUTPUT => s_efd_pos_oh((r+1)*REGION_SIZE-1 downto r*REGION_SIZE)
        );
    end generate;

    incomplete_block_g : for b in 0 to WORD_BLOCKS-1 generate
        incomplete_block_p : process (s_incomplete_block,s_sfd_pos_oh,s_efd_pos_oh)
            variable v_inc_blk : std_logic;
        begin
            v_inc_blk := s_incomplete_block(0);
            inc_blk_l : for i in 0 to b loop
                v_inc_blk := (s_sfd_pos_oh(i) or v_inc_blk) and not s_efd_pos_oh(i);
            end loop;
            s_incomplete_block(b+1) <= v_inc_blk;
        end process;
    end generate;

    incomplete_block_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_incomplete_block(0) <= '0';
            elsif (MII_RDY = '1') then
                s_incomplete_block(0) <= s_incomplete_block(WORD_BLOCKS);
            end if;
        end if;
    end process;

    block_vld_g : for i in 0 to WORD_BLOCKS-1 generate
        s_block_vld(i) <= (s_sfd_pos_oh(i) or s_efd_pos_oh(i) or s_incomplete_block(i));
    end generate;

    efd_ctrl_mux_g : for r in 0 to REGIONS-1 generate
        efd_ctrl_mux_g2 : for b in 0 to REGION_SIZE-1 generate
            process (s_efd_pos_reg1)
            begin
                s_efd_ctrl_wb(r*REGION_SIZE+b) <= (others => '1');
                efd_ctrl_wb_l : for i in 0 to BLOCK_SIZE-1 loop
                    if (unsigned(s_efd_pos_reg1(r)(LOG2_BLOCK_SIZE-1 downto 0)) > i) then
                        s_efd_ctrl_wb(r*REGION_SIZE+b)(i) <= '0';
                    end if;
                end loop;
            end process;
        end generate;
    end generate;

    s_data_wb <= slv_array_deser(s_data_reg1,WORD_BLOCKS,(BLOCK_SIZE*ITEM_WIDTH));

    efd_block_mux_g : for r in 0 to REGIONS-1 generate
        efd_block_mux_g2 : for b in 0 to REGION_SIZE-1 generate
            block8_g : if (BLOCK_SIZE = 8) generate
                process (s_efd_pos_reg1, s_data_wb)
                begin
                    case s_efd_pos_reg1(r)(LOG2_BLOCK_SIZE-1 downto 0) is
                        when "000" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"07070707070707FD";
                        when "001" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"070707070707FD" & s_data_wb(r*REGION_SIZE+b)(1*ITEM_WIDTH-1 downto 0);
                        when "010" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"0707070707FD" & s_data_wb(r*REGION_SIZE+b)(2*ITEM_WIDTH-1 downto 0);
                        when "011" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"07070707FD" & s_data_wb(r*REGION_SIZE+b)(3*ITEM_WIDTH-1 downto 0);
                        when "100" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"070707FD" & s_data_wb(r*REGION_SIZE+b)(4*ITEM_WIDTH-1 downto 0);
                        when "101" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"0707FD" & s_data_wb(r*REGION_SIZE+b)(5*ITEM_WIDTH-1 downto 0);
                        when "110" =>  s_efd_data_wb(r*REGION_SIZE+b) <= X"07FD" & s_data_wb(r*REGION_SIZE+b)(6*ITEM_WIDTH-1 downto 0);
                        when others => s_efd_data_wb(r*REGION_SIZE+b) <= X"FD" & s_data_wb(r*REGION_SIZE+b)(7*ITEM_WIDTH-1 downto 0);
                    end case;
                end process;
            end generate;
            block4_g : if (BLOCK_SIZE = 4) generate
                process (s_efd_pos_reg1, s_data_wb)
                begin
                    case s_efd_pos_reg1(r)(LOG2_BLOCK_SIZE-1 downto 0) is
                        when "00"   => s_efd_data_wb(r*REGION_SIZE+b) <= X"070707FD";
                        when "01"   => s_efd_data_wb(r*REGION_SIZE+b) <= X"0707FD" & s_data_wb(r*REGION_SIZE+b)(1*ITEM_WIDTH-1 downto 0);
                        when "10"   => s_efd_data_wb(r*REGION_SIZE+b) <= X"07FD" & s_data_wb(r*REGION_SIZE+b)(2*ITEM_WIDTH-1 downto 0);
                        when others => s_efd_data_wb(r*REGION_SIZE+b) <= X"FD" & s_data_wb(r*REGION_SIZE+b)(3*ITEM_WIDTH-1 downto 0);
                    end case;
                end process;
            end generate;
        end generate;
    end generate;

    -- =========================================================================
    -- 2. REGISTERS STAGE
    -- =========================================================================

    reg2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (MII_RDY = '1') then
                s_data_wb_reg2     <= s_data_wb;
                s_sfd_pos_oh_reg2  <= s_sfd_pos_oh;
                s_efd_pos_oh_reg2  <= s_efd_pos_oh;
                s_efd_ctrl_wb_reg2 <= s_efd_ctrl_wb;
                s_efd_data_wb_reg2 <= s_efd_data_wb;
            end if;
        end if;
    end process;

    vld_reg2_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg2     <= '0';
                s_block_vld_reg2 <= (others => '0');
            elsif (MII_RDY = '1') then
                s_valid_reg2     <= s_word_vld;
                s_block_vld_reg2 <= s_block_vld;
            end if;
        end if;
    end process;

    -- =========================================================================
    -- 3. LOGIC STAGE
    -- =========================================================================

    sfd_next_blk4_g : if (BLOCK_SIZE = 4) generate
        sfd_next_blk_g : for b in 0 to WORD_BLOCKS-2 generate
            s_sfd_next_blk(b) <= s_sfd_pos_oh_reg2(b+1) and s_block_vld_reg2(b+1);
        end generate;
        s_sfd_next_blk(WORD_BLOCKS-1) <= s_sfd_pos_oh(0) and s_block_vld(0);
    end generate;

    sfd_next_blk8_g : if (BLOCK_SIZE = 8) generate
        s_sfd_next_blk <= (others => '0');
    end generate;

    mii_mux_sel_g : for b in 0 to WORD_BLOCKS-1 generate
        s_block_state(b) <= s_sfd_next_blk(b) & s_block_vld_reg2(b) & s_sfd_pos_oh_reg2(b) & s_efd_pos_oh_reg2(b);

        -- conversion block state to mii mux select
        with s_block_state(b) select
        s_mii_mux_sel(b) <= "100" when "1000", -- Start + preamble (only BLOCK_SIZE = 4)
                            "000" when "0110", -- (Start) + preamble + SFD
                            "001" when "0100", -- frame data block
                            "010" when "0101", -- EFD block
                            "011" when others; -- idle block
    end generate;

    mii_mux_blk8_g : if (BLOCK_SIZE = 8) generate
        mii_mux_g : for b in 0 to WORD_BLOCKS-1 generate
            process (s_mii_mux_sel,s_efd_ctrl_wb_reg2,s_data_wb_reg2,s_efd_data_wb_reg2)
            begin
                case s_mii_mux_sel(b) is
                    when "000" => -- block with Start + preamble + SFD
                        s_mii_ctrl_wb(b) <= "00000001";
                        s_mii_data_wb(b) <= X"D5555555555555FB";
                    when "001" => -- frame data block
                        s_mii_ctrl_wb(b) <= (others => '0');
                        s_mii_data_wb(b) <= s_data_wb_reg2(b);
                    when "010" => -- EFD block
                        s_mii_ctrl_wb(b) <= s_efd_ctrl_wb_reg2(b);
                        s_mii_data_wb(b) <= s_efd_data_wb_reg2(b);
                    when others => -- idle block
                        s_mii_ctrl_wb(b) <= (others => '1');
                        s_mii_data_wb(b) <= X"0707070707070707";
                end case;
            end process;
        end generate;
        s_mii_vld <= s_valid_reg2;
    end generate;

    mii_mux_blk4_g : if (BLOCK_SIZE = 4) generate
        mii_mux_g : for b in 0 to WORD_BLOCKS-1 generate
            process (s_mii_mux_sel,s_efd_ctrl_wb_reg2,s_data_wb_reg2,s_efd_data_wb_reg2)
            begin
                case s_mii_mux_sel(b) is
                    when "100" => -- block with Start + first part of preamble
                        s_mii_ctrl_wb(b) <= "0001";
                        s_mii_data_wb(b) <= X"555555FB";
                        s_mii_vld_wb(b)  <= '1';
                    when "000" => -- block with second part of preamble + SFD
                        s_mii_ctrl_wb(b) <= (others => '0');
                        s_mii_data_wb(b) <= X"D5555555";
                        s_mii_vld_wb(b)  <= '1';
                    when "001" => -- frame data block
                        s_mii_ctrl_wb(b) <= (others => '0');
                        s_mii_data_wb(b) <= s_data_wb_reg2(b);
                        s_mii_vld_wb(b)  <= '1';
                    when "010" => -- EFD block
                        s_mii_ctrl_wb(b) <= s_efd_ctrl_wb_reg2(b);
                        s_mii_data_wb(b) <= s_efd_data_wb_reg2(b);
                        s_mii_vld_wb(b)  <= '1';
                    when others => -- idle block
                        s_mii_ctrl_wb(b) <= (others => '1');
                        s_mii_data_wb(b) <= X"07070707";
                        s_mii_vld_wb(b)  <= '0';
                end case;
            end process;
        end generate;
        s_mii_vld <= or s_mii_vld_wb;
    end generate;

    s_mii_ctrl <= slv_array_ser(s_mii_ctrl_wb,WORD_BLOCKS,BLOCK_SIZE);
    s_mii_data <= slv_array_ser(s_mii_data_wb,WORD_BLOCKS,(BLOCK_SIZE*ITEM_WIDTH));

    -- =========================================================================
    -- 3. REGISTERS STAGE
    -- =========================================================================

    reg3_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (MII_RDY = '1') then
                s_mii_data_reg3 <= s_mii_data;
                s_mii_ctrl_reg3 <= s_mii_ctrl;
            end if;
        end if;
    end process;

    vld_reg3_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_mii_vld_reg3 <= '0';
            elsif (MII_RDY = '1') then
                s_mii_vld_reg3 <= s_mii_vld;
            end if;
        end if;
    end process;

    -- MII OUTPUT
    MII_TXD <= s_mii_data_reg3;
    MII_TXC <= s_mii_ctrl_reg3;
    MII_VLD <= s_mii_vld_reg3;

end architecture;
