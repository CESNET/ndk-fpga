-- mvb_lut.vhd: MVB Lookup table with SW configuration (LUTRAM implementation)
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MVB_LOOKUP_TABLE_BRAM is
generic (
    MVB_ITEMS  : natural := 4;
    LUT_DEPTH  : natural := 128;
    LUT_WIDTH  : natural := 32;
    SW_WIDTH   : natural := 32;
    META_WIDTH : natural := 1;
    OUTPUT_REG : boolean := True;
    DEVICE     : string  := "AGILEX"
);
port (
    CLK             : in  std_logic;
    RESET           : in  std_logic;

    RX_MVB_LUT_ADDR : in  slv_array_t(MVB_ITEMS-1 downto 0)(log2(LUT_DEPTH)-1 downto 0);
    RX_MVB_METADATA : in  slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0) := (others => (others => '0'));
    RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_MVB_SRC_RDY  : in  std_logic;
    RX_MVB_DST_RDY  : out std_logic;

    TX_MVB_LUT_DATA : out slv_array_t(MVB_ITEMS-1 downto 0)(LUT_WIDTH-1 downto 0);
    TX_MVB_LUT_ADDR : out slv_array_t(MVB_ITEMS-1 downto 0)(log2(LUT_DEPTH)-1 downto 0);
    TX_MVB_METADATA : out slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    TX_MVB_VLD      : out std_logic_vector(MVB_ITEMS-1 downto 0);
    TX_MVB_SRC_RDY  : out std_logic;
    TX_MVB_DST_RDY  : in  std_logic;

    SW_ADDR         : in  std_logic_vector(log2(LUT_DEPTH)-1 downto 0);
    SW_SLICE        : in  std_logic_vector(max(log2(LUT_WIDTH/SW_WIDTH),1)-1 downto 0);
    SW_DIN          : in  std_logic_vector(SW_WIDTH-1 downto 0);
    SW_BE           : in  std_logic_vector(SW_WIDTH/8-1 downto 0);
    SW_WRITE        : in  std_logic;
    SW_READ         : in  std_logic;
    SW_DOUT         : out std_logic_vector(SW_WIDTH-1 downto 0);
    SW_DOUT_VLD     : out std_logic
);
end entity;

architecture FULL of MVB_LOOKUP_TABLE_BRAM is

    constant SW_WORDS_PER_LUT : natural := LUT_WIDTH/SW_WIDTH;
    constant SW_BYTES_W       : natural := SW_WIDTH/8;

    signal ram_be                : std_logic_vector(LUT_WIDTH/8-1 downto 0);
    signal ram_din               : std_logic_vector(LUT_WIDTH-1 downto 0);

    signal ram_copy_dout         : std_logic_vector(LUT_WIDTH-1 downto 0);
    signal ram_copy_dout_nsw     : std_logic_vector(SW_WORDS_PER_LUT*SW_WIDTH-1 downto 0);
    signal ram_copy_dout_nsw_arr : slv_array_t(SW_WORDS_PER_LUT-1 downto 0)(SW_WIDTH-1 downto 0);

    signal ram_mvb_lut_addr      : slv_array_t(MVB_ITEMS-1 downto 0)(log2(LUT_DEPTH)-1 downto 0);
    signal ram_mvb_metadata      : slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    signal ram_mvb_vld           : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal ram_mvb_src_rdy       : std_logic;

    signal sw_slice_reg          : std_logic_vector(max(log2(LUT_WIDTH/SW_WIDTH),1)-1 downto 0);

begin

    RX_MVB_DST_RDY <= TX_MVB_DST_RDY;

    process (all)
    begin
        if (SW_WORDS_PER_LUT > 1) then
            ram_be  <= (others => '0');
            ram_din <= (others => '0');
            for i in 0 to SW_WORDS_PER_LUT-1 loop
                ram_din((i+1)*SW_WIDTH-1 downto i*SW_WIDTH) <= SW_DIN;
                if (unsigned(SW_SLICE) = i) then
                    ram_be((i+1)*SW_BYTES_W-1 downto i*SW_BYTES_W) <= SW_BE;
                end if;
            end loop;
        else
            ram_din <= SW_DIN;
            ram_be  <= SW_BE;
        end if;
    end process;

    ram_g : for i in 0 to MVB_ITEMS-1 generate
        ram_i : entity work.SDP_BRAM_BE
        generic map(
            DATA_WIDTH     => LUT_WIDTH,
            ITEMS          => LUT_DEPTH,
            BLOCK_ENABLE   => true,
            BLOCK_WIDTH    => 8,
            COMMON_CLOCK   => True,
            OUTPUT_REG     => OUTPUT_REG,
            DEVICE         => DEVICE
        )
        port map(
            WR_CLK      => CLK,
            WR_RST      => RESET,
            WR_EN       => SW_WRITE,
            WR_BE       => ram_be,
            WR_ADDR     => SW_ADDR,
            WR_DATA     => ram_din,

            RD_CLK      => CLK,
            RD_RST      => RESET,
            RD_EN       => '1',
            RD_PIPE_EN  => TX_MVB_DST_RDY,
            RD_ADDR     => RX_MVB_LUT_ADDR(i),
            RD_DATA     => TX_MVB_LUT_DATA(i), -- 2 or 1 cycle latency
            RD_DATA_VLD => open
        );
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MVB_DST_RDY = '1') then
                ram_mvb_lut_addr <= RX_MVB_LUT_ADDR;
                ram_mvb_metadata <= RX_MVB_METADATA;
                ram_mvb_vld      <= RX_MVB_VLD;
                ram_mvb_src_rdy  <= RX_MVB_SRC_RDY;
            end if;
            if (RESET = '1') then
                ram_mvb_src_rdy <= '0';
            end if;
        end if;
    end process;

    mvb_out_reg_g : if OUTPUT_REG generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (TX_MVB_DST_RDY = '1') then
                    TX_MVB_LUT_ADDR <= ram_mvb_lut_addr;
                    TX_MVB_METADATA <= ram_mvb_metadata;
                    TX_MVB_VLD      <= ram_mvb_vld;
                    TX_MVB_SRC_RDY  <= ram_mvb_src_rdy;
                end if;
                if (RESET = '1') then
                    TX_MVB_SRC_RDY <= '0';
                end if;
            end if;
        end process;
    else generate
        TX_MVB_LUT_ADDR <= ram_mvb_lut_addr;
        TX_MVB_METADATA <= ram_mvb_metadata;
        TX_MVB_VLD      <= ram_mvb_vld;
        TX_MVB_SRC_RDY  <= ram_mvb_src_rdy;
    end generate;

    ram_sw_copy_i : entity work.SDP_BRAM_BE
    generic map(
        DATA_WIDTH     => LUT_WIDTH,
        ITEMS          => LUT_DEPTH,
        BLOCK_ENABLE   => true,
        BLOCK_WIDTH    => 8,
        COMMON_CLOCK   => True,
        OUTPUT_REG     => False,
        DEVICE         => DEVICE
    )
    port map(
        WR_CLK      => CLK,
        WR_RST      => RESET,
        WR_EN       => SW_WRITE,
        WR_BE       => ram_be,
        WR_ADDR     => SW_ADDR,
        WR_DATA     => ram_din,

        RD_CLK      => CLK,
        RD_RST      => RESET,
        RD_EN       => SW_READ,
        RD_PIPE_EN  => '1',
        RD_ADDR     => SW_ADDR,
        RD_DATA     => ram_copy_dout,
        RD_DATA_VLD => SW_DOUT_VLD
    );

    ram_copy_dout_nsw <= std_logic_vector(resize(unsigned(ram_copy_dout),(SW_WORDS_PER_LUT*SW_WIDTH)));
    ram_copy_dout_nsw_arr <= slv_array_deser(ram_copy_dout_nsw,SW_WORDS_PER_LUT);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            sw_slice_reg <= SW_SLICE;
        end if;
    end process;

    process (all)
    begin
        if (SW_WORDS_PER_LUT > 1) then
            SW_DOUT <= (others => '0');
            for i in 0 to SW_WORDS_PER_LUT-1 loop
                if (unsigned(sw_slice_reg) = i) then
                    SW_DOUT <= ram_copy_dout_nsw_arr(i);
                end if;
            end loop;
        else
            SW_DOUT <= ram_copy_dout_nsw_arr(0);
        end if;
    end process;

end architecture;
