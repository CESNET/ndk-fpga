-- get_crc32.vhd: Get CRC32
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_GET_CRC32 is
    generic(
        REGIONS     : natural := 4; -- any possitive value
        REGION_SIZE : natural := 8; -- any possitive value
        BLOCK_SIZE  : natural := 8; -- any possitive value
        ITEM_WIDTH  : natural := 8; -- must be 8
        INBANDFCS   : boolean := True -- True = CRC is not removed, False = CRC is removed
    );
    port(
        -- CLOCK AND RESET
        CLK             : in  std_logic;
        RESET           : in  std_logic;
        -- INPUT MFB DATA INTERFACE
        RX_DATA         : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_EOF_POS      : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_EOF          : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY      : in  std_logic;
        -- OUTPUT CRC32 INTERFACE (latency is 2 cycle)
        CRC32           : out std_logic_vector(REGIONS*32-1 downto 0);
        CRC32_VLD       : out std_logic_vector(REGIONS-1 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_GET_CRC32 is

    constant REGION_WIDTH   : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant EOF_POS_SIZE   : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant BYTES_COUNT    : natural := REGION_WIDTH/8;

    signal s_data_arr       : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_data_arr_reg   : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_data_next      : std_logic_vector(REGION_WIDTH-1 downto 0);
    signal s_data_prev      : std_logic_vector(REGION_WIDTH-1 downto 0);

    signal s_data_ultra_arr : slv_array_t(REGIONS+1 downto 0)(REGION_WIDTH-1 downto 0);

    signal s_mux_sel_arr    : slv_array_t(REGIONS-1 downto 0)(EOF_POS_SIZE-1 downto 0);
    signal s_mux_din_arr    : slv_array_t(REGIONS-1 downto 0)(2*REGION_WIDTH-1 downto 0);

    signal s_crc32_arr      : slv_array_t(REGIONS-1 downto 0)(32-1 downto 0);
    signal s_valid_reg      : std_logic_vector(REGIONS-1 downto 0);

begin

    data_arr_g : for r in 0 to REGIONS-1 generate
        s_data_arr(r) <= RX_DATA((r+1)*REGION_WIDTH-1 downto r*REGION_WIDTH);
    end generate;

    s_data_next <= s_data_arr(0);

    data_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            s_data_arr_reg <= s_data_arr;
            s_data_prev    <= s_data_arr_reg(REGIONS-1);
        end if;
    end process;

    s_data_ultra_arr(0) <= s_data_prev;
    data_ultra_arr_g : for r in 0 to REGIONS-1 generate
        s_data_ultra_arr(r+1) <= s_data_arr_reg(r);
    end generate;
    s_data_ultra_arr(REGIONS+1) <= s_data_next;

    mux_sel_arr_g : for r in 0 to REGIONS-1 generate
        mux_sel_arr_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                s_mux_sel_arr(r) <= RX_EOF_POS((r+1)*EOF_POS_SIZE-1 downto r*EOF_POS_SIZE);
            end if;
        end process;
    end generate;

    -- INBANDFCS = true
    inbandfcs_g : if INBANDFCS generate
        mux_din_arr_g : for r in 0 to REGIONS-1 generate
            s_mux_din_arr(r) <= s_data_ultra_arr(r+1) & s_data_ultra_arr(r);

            mux_g : for i in 0 to 3 generate
                mux_i : entity work.GEN_MUX
                generic map(
                    DATA_WIDTH => 8,
                    MUX_WIDTH  => BYTES_COUNT
                )
                port map(
                    DATA_IN  => s_mux_din_arr(r)((2*BYTES_COUNT-i)*8-1 downto (BYTES_COUNT-i)*8),
                    SEL      => s_mux_sel_arr(r),
                    DATA_OUT => s_crc32_arr(r)(((3-i)+1)*8-1 downto (3-i)*8)
                );
            end generate;
        end generate;
    end generate;

    -- INBANDFCS = false, CRC must be after EOF!!!
    not_inbandfcs_g : if not INBANDFCS generate
        mux_din_arr_g : for r in 0 to REGIONS-1 generate
            s_mux_din_arr(r) <= s_data_ultra_arr(r+2) & s_data_ultra_arr(r+1);

            mux_g : for i in 0 to 3 generate
                mux_i : entity work.GEN_MUX
                generic map(
                    DATA_WIDTH => 8,
                    MUX_WIDTH  => BYTES_COUNT
                )
                port map(
                    DATA_IN  => s_mux_din_arr(r)((BYTES_COUNT+i+1)*8-1 downto (i+1)*8),
                    SEL      => s_mux_sel_arr(r),
                    DATA_OUT => s_crc32_arr(r)((i+1)*8-1 downto i*8)
                );
            end generate;
        end generate;
    end generate;

    crc32_g : for r in 0 to REGIONS-1 generate
        crc32_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                CRC32((r+1)*32-1 downto r*32) <= s_crc32_arr(r);
            end if;
        end process;
    end generate;

    crc32_vld_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_valid_reg <= (others => '0');
                CRC32_VLD   <= (others => '0');
            else
                s_valid_reg <= RX_EOF and RX_SRC_RDY;
                CRC32_VLD   <= s_valid_reg;
            end if;
        end if;
    end process;

end architecture;
