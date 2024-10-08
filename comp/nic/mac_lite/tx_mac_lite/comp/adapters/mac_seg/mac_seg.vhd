-- mac_seg.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_ADAPTER_MAC_SEG is
    generic(
        REGIONS     : natural := 2;
        REGION_SIZE : natural := 8;
        SEGMENTS    : natural := REGIONS*REGION_SIZE
    );
    port(
        -- CLOCK AND RESET
        CLK               : in  std_logic;
        RESET             : in  std_logic;
        -- INPUT MFB INTERFACE
        -- (RX MAC LITE, allowed MFB configurations: REGIONS,REGION_SIZE,8,8
        IN_MFB_DATA       : in  std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
        IN_MFB_SOF        : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_SOF_POS    : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        IN_MFB_EOF        : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_EOF_POS    : in  std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
        IN_MFB_ERROR      : in  std_logic_vector(REGIONS-1 downto 0);
        IN_MFB_SRC_RDY    : in  std_logic;
        IN_MFB_DST_RDY    : out std_logic;
        -- OUTPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        OUT_MAC_DATA      : out std_logic_vector(SEGMENTS*64-1 downto 0);
        OUT_MAC_INFRAME   : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_MAC_EOP_EMPTY : out std_logic_vector(SEGMENTS*3-1 downto 0);
        OUT_MAC_ERROR     : out std_logic_vector(SEGMENTS-1 downto 0);
        OUT_MAC_VALID     : out std_logic;
        OUT_MAC_READY     : in  std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_ADAPTER_MAC_SEG is

    signal aux_data      : std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
    signal aux_err       : std_logic_vector(REGIONS-1 downto 0);
    signal aux_sof       : std_logic_vector(REGIONS-1 downto 0);
    signal aux_eof       : std_logic_vector(REGIONS-1 downto 0);
    signal aux_sof_pos   : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal aux_eof_pos   : std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
    signal aux_src_rdy   : std_logic;
    signal aux_block_vld : std_logic_vector(REGIONS*REGION_SIZE-1 downto 0);

    signal aux_eof_pos_arr   : slv_array_t(REGIONS-1 downto 0)(log2(REGION_SIZE*8)-1 downto 0);
    signal aux_eof_oh        : std_logic_vector(REGIONS*REGION_SIZE-1 downto 0);
    signal aux_err_oh        : std_logic_vector(REGIONS*REGION_SIZE-1 downto 0);
    signal aux_eop_empty_arr : slv_array_t(SEGMENTS-1 downto 0)(3-1 downto 0);

    signal out_mac_valid_sig : std_logic;

begin

    rx_aux_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map(
        REGIONS        => REGIONS,
        REGION_SIZE    => REGION_SIZE,
        BLOCK_SIZE     => 8,
        ITEM_WIDTH     => 8,
        META_WIDTH     => 1,
        REGION_AUX_EN  => false,
        BLOCK_AUX_EN   => true,
        ITEM_AUX_EN    => false
    )
    port map(
        CLK              => CLK  ,
        RESET            => RESET,

        RX_DATA          => IN_MFB_DATA,
        RX_META          => IN_MFB_ERROR,
        RX_SOF           => IN_MFB_SOF,
        RX_EOF           => IN_MFB_EOF,
        RX_SOF_POS       => IN_MFB_SOF_POS,
        RX_EOF_POS       => IN_MFB_EOF_POS,
        RX_SRC_RDY       => IN_MFB_SRC_RDY,
        RX_DST_RDY       => IN_MFB_DST_RDY,

        TX_DATA          => aux_data,
        TX_META          => aux_err,
        TX_SOF           => aux_sof,
        TX_EOF           => aux_eof,
        TX_SOF_POS       => aux_sof_pos,
        TX_EOF_POS       => aux_eof_pos,
        TX_SRC_RDY       => aux_src_rdy,
        TX_DST_RDY       => OUT_MAC_VALID,

        TX_REGION_SHARED => open         ,
        TX_REGION_VLD    => open         ,
        TX_BLOCK_VLD     => aux_block_vld,
        TX_ITEM_VLD      => open
    );

    aux_eof_pos_arr <= slv_array_deser(aux_eof_pos,REGIONS,log2(REGION_SIZE*8));

    aux_mfb_g : for i in 0 to REGIONS-1 generate

        one_mfb_block_g : if REGION_SIZE>1 generate
            eof_oh_i : entity work.DEC1FN_ENABLE
            generic map (
                ITEMS => REGION_SIZE
            )
            port map (
                ADDR   => aux_eof_pos_arr(i)(log2(REGION_SIZE*8)-1 downto 3),
                ENABLE => aux_eof(i),
                DO     => aux_eof_oh((i+1)*REGION_SIZE-1 downto i*REGION_SIZE)
            );

            err_oh_i : entity work.DEC1FN_ENABLE
            generic map (
                ITEMS => REGION_SIZE
            )
            port map (
                ADDR   => aux_eof_pos_arr(i)(log2(REGION_SIZE*8)-1 downto 3),
                ENABLE => aux_err(i),
                DO     => aux_err_oh((i+1)*REGION_SIZE-1 downto i*REGION_SIZE)
            );
        else generate
            aux_eof_oh(i) <= aux_eof(i);
            aux_err_oh(i) <= aux_err(i);
        end generate;

        aux_empty_g : for j in 0 to REGION_SIZE-1 generate
            process (all)
            begin
                aux_eop_empty_arr(i*REGION_SIZE+j) <= (others => '0');
                if (aux_eof_oh(i*REGION_SIZE+j) = '1') then
                    aux_eop_empty_arr(i*REGION_SIZE+j) <= std_logic_vector(7 - unsigned(aux_eof_pos_arr(i)(3-1 downto 0)));
                end if;
            end process;
        end generate;

    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (OUT_MAC_VALID = '1') then
                OUT_MAC_DATA      <= aux_data;
                OUT_MAC_INFRAME   <= aux_block_vld and not aux_eof_oh and aux_src_rdy;
                OUT_MAC_EOP_EMPTY <= slv_array_ser(aux_eop_empty_arr,SEGMENTS,3);
                OUT_MAC_ERROR     <= aux_err_oh;
            end if;
            if (RESET = '1') then
                OUT_MAC_INFRAME <= (others => '0');
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            OUT_MAC_VALID <= OUT_MAC_READY;
            if (RESET = '1') then
                OUT_MAC_VALID <= '0';
            end if;
        end if;
    end process;

end architecture;
