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

entity MVB_LOOKUP_TABLE_LUTRAM is
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

architecture FULL of MVB_LOOKUP_TABLE_LUTRAM is

    constant LUT_BYTES_W      : natural := LUT_WIDTH/8;
    constant SW_WORDS_PER_LUT : natural := LUT_WIDTH/SW_WIDTH;
    constant SW_BYTES_W       : natural := SW_WIDTH/8;

    signal lram_wr_addr         : std_logic_vector(log2(LUT_DEPTH)-1 downto 0);
    signal lram_rd_addr         : slv_array_t(MVB_ITEMS+1-1 downto 0)(log2(LUT_DEPTH)-1 downto 0);
    signal lram_sel             : std_logic_vector(LUT_BYTES_W-1 downto 0);
    signal lram_wr              : std_logic_vector(LUT_BYTES_W-1 downto 0);
    signal lram_wr_data         : slv_array_t(LUT_BYTES_W-1 downto 0)(8-1 downto 0);
    signal lram_rd_data_byteser : slv_array_t(LUT_BYTES_W-1 downto 0)((MVB_ITEMS+1)*8-1 downto 0);
    signal lram_rd_data         : slv_array_t(MVB_ITEMS+1-1 downto 0)(LUT_WIDTH-1 downto 0);
    signal lram_rd_data_mi      : slv_array_t(SW_WORDS_PER_LUT-1 downto 0)(SW_WIDTH-1 downto 0);

    signal ram_sw_dout_nsw      : std_logic_vector(SW_WORDS_PER_LUT*SW_WIDTH-1 downto 0);
    signal ram_sw_dout_nsw_arr  : slv_array_t(SW_WORDS_PER_LUT-1 downto 0)(SW_WIDTH-1 downto 0);
    signal ram_sw_dout          : std_logic_vector(SW_WIDTH-1 downto 0);

begin

    RX_MVB_DST_RDY <= TX_MVB_DST_RDY;

    lram_wr_addr    <= SW_ADDR;
    lram_rd_addr(0) <= SW_ADDR;

    lram_rd_addr_g: for i in 0 to MVB_ITEMS-1 generate
        lram_rd_addr(i+1) <= RX_MVB_LUT_ADDR(i);
    end generate;

    lram_g: for i in 0 to LUT_BYTES_W-1 generate
        lram_sel_g : if SW_WORDS_PER_LUT > 1 generate
            lram_sel(i) <= '1' when (unsigned(SW_SLICE) = (i/SW_BYTES_W)) else '0';
        else generate
            lram_sel(i) <= '1';
        end generate;

        lram_wr(i)      <= lram_sel(i) and SW_BE(i mod SW_BYTES_W) and SW_WRITE;
        lram_wr_data(i) <= SW_DIN(((i mod SW_BYTES_W)+1)*8-1 downto (i mod SW_BYTES_W)*8);

        ram_i : entity work.GEN_LUTRAM
        generic map (
            DATA_WIDTH         => 8,
            ITEMS              => LUT_DEPTH,
            RD_PORTS           => 1+MVB_ITEMS, --SW+MVB
            RD_LATENCY         => 0,
            WRITE_USE_RD_ADDR0 => True,
            MLAB_CONSTR_RDW_DC => True,
            DEVICE             => DEVICE
        )
        port map (
            CLK     => CLK,
            WR_EN   => lram_wr(i),
            WR_ADDR => lram_wr_addr,
            WR_DATA => lram_wr_data(i),
            RD_ADDR => slv_array_ser(lram_rd_addr),
            RD_DATA => lram_rd_data_byteser(i)
        );
    end generate;

    lram_rd_data_g: for i in 0 to MVB_ITEMS generate
        lram_rd_data_g2: for j in 0 to LUT_BYTES_W-1 generate
            lram_rd_data(i)((j+1)*8-1 downto j*8) <= lram_rd_data_byteser(j)((i+1)*8-1 downto i*8);
        end generate;
    end generate;

    ram_sw_dout_nsw <= std_logic_vector(resize(unsigned(lram_rd_data(0)),(SW_WORDS_PER_LUT*SW_WIDTH)));
    ram_sw_dout_nsw_arr <= slv_array_deser(ram_sw_dout_nsw,SW_WORDS_PER_LUT);

    process (all)
    begin
        if (SW_WORDS_PER_LUT > 1) then
            ram_sw_dout <= (others => '0');
            for i in 0 to SW_WORDS_PER_LUT-1 loop
                if (unsigned(SW_SLICE) = i) then
                    ram_sw_dout <= ram_sw_dout_nsw_arr(i);
                end if;
            end loop;
        else
            ram_sw_dout <= ram_sw_dout_nsw_arr(0);
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            SW_DOUT     <= ram_sw_dout;
            SW_DOUT_VLD <= SW_READ;
            if (RESET = '1') then
                SW_DOUT_VLD <= '0';
            end if;
        end if;
    end process;

    out_reg_g: if OUTPUT_REG generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (TX_MVB_DST_RDY = '1') then
                    TX_MVB_METADATA <= RX_MVB_METADATA;
                    TX_MVB_LUT_ADDR <= RX_MVB_LUT_ADDR;
                    TX_MVB_LUT_DATA <= lram_rd_data(MVB_ITEMS downto 1);
                    TX_MVB_VLD      <= RX_MVB_VLD;
                    TX_MVB_SRC_RDY  <= RX_MVB_SRC_RDY;
                end if;
                if (RESET = '1') then
                    TX_MVB_SRC_RDY <= '0';
                end if;
            end if;
        end process;
    else generate
        TX_MVB_METADATA <= RX_MVB_METADATA;
        TX_MVB_LUT_ADDR <= RX_MVB_LUT_ADDR;
        TX_MVB_LUT_DATA <= lram_rd_data(MVB_ITEMS downto 1);
        TX_MVB_VLD      <= RX_MVB_VLD;
        TX_MVB_SRC_RDY  <= RX_MVB_SRC_RDY;
    end generate;

end architecture;
