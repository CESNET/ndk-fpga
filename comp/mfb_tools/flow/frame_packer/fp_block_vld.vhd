-- fp_block_vld.vhd: Unit for validating MFB words
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            David Beneš <xbenes52@vutbr.cz>
--
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- This unit is based on mfb_auxiliary_signals.vhd and is adjusted for frame_packer purposes
entity FP_BLOCK_VLD is
    generic(
        MFB_REGIONS         : natural := 1;
        MFB_REGION_SIZE     : natural := 8;
        MFB_BLOCK_SIZE      : natural := 8;
        MFB_ITEM_WIDTH      : natural := 8

    );
    port(
        -- This port helps to control auxiliary signals in this application
        RX_PKT_CONT  : in  std_logic;

        RX_SOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_EOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_SOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_EOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_SRC_RDY   : in  std_logic;
        RX_DST_RDY   : out std_logic;

        TX_SRC_RDY   : out std_logic;
        TX_DST_RDY   : in  std_logic;

        -- Returns valid vector
        TX_BLOCK_VLD : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
        TX_SOF_OH    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
        TX_EOF_OH    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0)
    );
end entity;

architecture FULL of FP_BLOCK_VLD is
    -- Constants
    constant WORD_BLOCKS         : natural := MFB_REGIONS*MFB_REGION_SIZE;
    constant REGION_BLOCKS       : natural := MFB_REGION_SIZE;
    constant WORD_ITEMS          : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant REGION_ITEMS        : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant LOG2_REGION_BLOCKS  : natural := log2(REGION_BLOCKS);
    constant LOG2_REGION_ITEMS   : natural := log2(REGION_ITEMS);
    constant LOG2_BLOCK_SIZE     : natural := log2(MFB_BLOCK_SIZE);

     -- Constants
    signal s_rx_sof_block_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(LOG2_REGION_BLOCKS-1 downto 0);
    signal s_rx_eof_block_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(LOG2_REGION_BLOCKS-1 downto 0);

    signal s_rx_eof_item_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(LOG2_REGION_ITEMS-1 downto 0);

    signal s_rx_sof_block_onehot : std_logic_vector(WORD_BLOCKS-1 downto 0);
    signal s_rx_eof_block_onehot : std_logic_vector(WORD_BLOCKS-1 downto 0);

    signal s_incomplete_block    : std_logic_vector(WORD_BLOCKS downto 0);

    -- respect to SRC_RDY
    signal tx_block_vld_s : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
    signal tx_sof_oh_s    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);
    signal tx_eof_oh_s    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE-1 downto 0);

begin
    RX_DST_RDY              <= '1';
    TX_SRC_RDY              <= RX_SRC_RDY;

   --  CREATE MFB SOF_POS AND EOF_POS ARRAYS
    item_rx_sof_block_arr_g : if REGION_BLOCKS > 1 generate
        s_rx_sof_block_arr <= slv_array_downto_deser(RX_SOF_POS,MFB_REGIONS,LOG2_REGION_BLOCKS);
    else generate
        s_rx_sof_block_arr <= (others => (others => '0'));
    end generate;

    rx_eof_item_arr_g : if REGION_ITEMS > 1 generate
        s_rx_eof_item_arr <= slv_array_downto_deser(RX_EOF_POS,MFB_REGIONS,LOG2_REGION_ITEMS);
    else generate
        s_rx_eof_item_arr <= (others => (others => '0'));
    end generate;

    sof_eof_array_g : for r in 0 to MFB_REGIONS-1 generate
        s_rx_eof_block_arr(r) <= s_rx_eof_item_arr(r)(LOG2_REGION_ITEMS-1 downto LOG2_BLOCK_SIZE);
    end generate;

   -- --------------------------------------------------------------------------
   --  VALID FOR EACH BLOCK
   -- --------------------------------------------------------------------------

    block_onehot_g : for r in 0 to MFB_REGIONS-1 generate
        sof_block_onehot_i : entity work.BIN2HOT
            generic map(
                DATA_WIDTH => LOG2_REGION_BLOCKS
            )
            port map(
                EN     => RX_SOF(r),
                INPUT  => s_rx_sof_block_arr(r),
                OUTPUT => s_rx_sof_block_onehot((r+1)*REGION_BLOCKS-1 downto r*REGION_BLOCKS)
        );

        eof_block_onehot_i : entity work.BIN2HOT
            generic map(
                DATA_WIDTH => LOG2_REGION_BLOCKS
            )
            port map(
                EN     => RX_EOF(r),
                INPUT  => s_rx_eof_block_arr(r),
                OUTPUT => s_rx_eof_block_onehot((r+1)*REGION_BLOCKS-1 downto r*REGION_BLOCKS)
        );
    end generate;

    incomplete_block_g : for r in 0 to WORD_BLOCKS-1 generate
        incomplete_block_p : process (all)
                variable v_inc_blk : std_logic;
        begin
                v_inc_blk              := RX_PKT_CONT;
                inc_blk_l : for i in 0 to r loop
                    v_inc_blk := (s_rx_sof_block_onehot(i) or v_inc_blk) and not s_rx_eof_block_onehot(i);
                end loop;
                s_incomplete_block(r+1) <= v_inc_blk;
        end process;
    end generate;

    s_incomplete_block(0)  <= RX_PKT_CONT;
    block_vld_g : for i in 0 to WORD_BLOCKS-1 generate
        tx_block_vld_s(i) <= s_rx_sof_block_onehot(i) or s_rx_eof_block_onehot(i) or s_incomplete_block(i);
    end generate;

        tx_sof_oh_s   <= s_rx_sof_block_onehot;
        tx_eof_oh_s   <= s_rx_eof_block_onehot;

    -- Respect to SRC_RDY
    process(all)
    begin
        if RX_SRC_RDY = '1' then
            TX_BLOCK_VLD    <= tx_block_vld_s;
            TX_SOF_OH       <= tx_sof_oh_s;
            TX_EOF_OH       <= tx_eof_oh_s;
        else
            TX_BLOCK_VLD    <= (others => '0');
            TX_SOF_OH       <= (others => '0');
            TX_EOF_OH       <= (others => '0');
        end if;
    end process;
end architecture;
