-- mvb_lut.vhd: MVB Lookup table with SW configuration (TOP implementation)
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Component MVB_LOOKUP_TABLE allows to read values from the lookup table using
-- the MVB bus. The input MVB transaction must contain the address of an entry
-- in the lookup table. This MVB transaction will be transferred to the output
-- in a few clock cycles, where it will additionally contain the value of the
-- item read from the lookup table. This component allows the lookup table to be
-- implemented using LUTRAM, BRAM and a register (LUT_DEPTH=1 only). The contents
-- of the lookup table can be configured through a simple SW interface.
--
entity MVB_LOOKUP_TABLE is
generic (
    MVB_ITEMS  : natural := 4;
    LUT_DEPTH  : natural := 128;
    LUT_WIDTH  : natural := 32;
    LUT_ARCH   : string  := "AUTO";
    SW_WIDTH   : natural := 32;
    META_WIDTH : natural := 1;
    OUTPUT_REG : boolean := True;
    DEVICE     : string  := "AGILEX"
);
port (
    CLK             : in  std_logic;
    RESET           : in  std_logic;

    RX_MVB_LUT_ADDR : in  slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)-1 downto 0);
    RX_MVB_METADATA : in  slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0) := (others => (others => '0'));
    RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
    RX_MVB_SRC_RDY  : in  std_logic;
    RX_MVB_DST_RDY  : out std_logic;

    TX_MVB_LUT_DATA : out slv_array_t(MVB_ITEMS-1 downto 0)(LUT_WIDTH-1 downto 0);
    TX_MVB_LUT_ADDR : out slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)-1 downto 0);
    TX_MVB_METADATA : out slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    TX_MVB_VLD      : out std_logic_vector(MVB_ITEMS-1 downto 0);
    TX_MVB_SRC_RDY  : out std_logic;
    TX_MVB_DST_RDY  : in  std_logic;

    SW_ADDR         : in  std_logic_vector(max(log2(LUT_DEPTH),1)-1 downto 0);
    SW_SLICE        : in  std_logic_vector(max(log2(LUT_WIDTH/SW_WIDTH),1)-1 downto 0);
    SW_DIN          : in  std_logic_vector(SW_WIDTH-1 downto 0);
    SW_BE           : in  std_logic_vector(SW_WIDTH/8-1 downto 0);
    SW_WRITE        : in  std_logic;
    SW_READ         : in  std_logic;
    SW_DOUT         : out std_logic_vector(SW_WIDTH-1 downto 0);
    SW_DOUT_VLD     : out std_logic
);
end entity;

architecture FULL of MVB_LOOKUP_TABLE is

    constant LUT_BYTES_W      : natural := LUT_WIDTH/8;
    constant SW_WORDS_PER_LUT : natural := LUT_WIDTH/SW_WIDTH;
    constant SW_BYTES_W       : natural := SW_WIDTH/8;

    signal lram_sel           : std_logic_vector(LUT_BYTES_W-1 downto 0);
    signal lram_wr            : std_logic_vector(LUT_BYTES_W-1 downto 0);
    signal lram_wr_data       : slv_array_t(LUT_BYTES_W-1 downto 0)(8-1 downto 0);

    signal lut_reg_arr        : slv_array_t(LUT_BYTES_W-1 downto 0)(8-1 downto 0);
    signal lut_reg            : std_logic_vector(LUT_WIDTH-1 downto 0);

    signal lut_reg_sw_nsw     : std_logic_vector(SW_WORDS_PER_LUT*SW_WIDTH-1 downto 0);
    signal lut_reg_sw_nsw_arr : slv_array_t(SW_WORDS_PER_LUT-1 downto 0)(SW_WIDTH-1 downto 0);
    signal lut_reg_sw         : std_logic_vector(SW_WIDTH-1 downto 0);

begin

    single_reg_g: if (LUT_DEPTH = 1) generate
        RX_MVB_DST_RDY <= TX_MVB_DST_RDY;

        lreg_g: for i in 0 to LUT_BYTES_W-1 generate
            lram_sel_g : if SW_WORDS_PER_LUT > 1 generate
                lram_sel(i) <= '1' when (unsigned(SW_SLICE) = (i/SW_BYTES_W)) else '0';
            else generate
                lram_sel(i) <= '1';
            end generate;
            lram_wr(i)      <= lram_sel(i) and SW_BE(i mod SW_BYTES_W) and SW_WRITE;
            lram_wr_data(i) <= SW_DIN(((i mod SW_BYTES_W)+1)*8-1 downto (i mod SW_BYTES_W)*8);

            process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (lram_wr(i) = '1') then
                        lut_reg_arr(i) <= lram_wr_data(i);
                    end if;
                end if;
            end process;
        end generate;

        lut_reg <= slv_array_ser(lut_reg_arr);

        lut_reg_sw_nsw <= std_logic_vector(resize(unsigned(lut_reg),(SW_WORDS_PER_LUT*SW_WIDTH)));
        lut_reg_sw_nsw_arr <= slv_array_deser(lut_reg_sw_nsw,SW_WORDS_PER_LUT);

        process (all)
        begin
            if (SW_WORDS_PER_LUT > 1) then
                lut_reg_sw <= (others => '0');
                for i in 0 to SW_WORDS_PER_LUT-1 loop
                    if (unsigned(SW_SLICE) = i) then
                        lut_reg_sw <= lut_reg_sw_nsw_arr(i);
                    end if;
                end loop;
            else
                lut_reg_sw <= lut_reg_sw_nsw_arr(0);
            end if;
        end process;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                SW_DOUT     <= lut_reg_sw;
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
                        TX_MVB_LUT_DATA <= (others => lut_reg);
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
            TX_MVB_LUT_DATA <= (others => lut_reg);
            TX_MVB_VLD      <= RX_MVB_VLD;
            TX_MVB_SRC_RDY  <= RX_MVB_SRC_RDY;
        end generate;
    end generate;

    lutram_g: if ((LUT_DEPTH > 1 and LUT_DEPTH <= 64 and LUT_ARCH = "AUTO") or (LUT_DEPTH > 1 and LUT_ARCH = "LUT")) generate
        lutram_i : entity work.MVB_LOOKUP_TABLE_LUTRAM
        generic map(
            MVB_ITEMS  => MVB_ITEMS,
            LUT_DEPTH  => LUT_DEPTH,
            LUT_WIDTH  => LUT_WIDTH,
            SW_WIDTH   => SW_WIDTH,
            META_WIDTH => META_WIDTH,
            OUTPUT_REG => OUTPUT_REG,
            DEVICE     => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RESET,

            RX_MVB_LUT_ADDR => RX_MVB_LUT_ADDR,
            RX_MVB_METADATA => RX_MVB_METADATA,
            RX_MVB_VLD      => RX_MVB_VLD,
            RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

            TX_MVB_LUT_DATA => TX_MVB_LUT_DATA,
            TX_MVB_LUT_ADDR => TX_MVB_LUT_ADDR,
            TX_MVB_METADATA => TX_MVB_METADATA,
            TX_MVB_VLD      => TX_MVB_VLD,
            TX_MVB_SRC_RDY  => TX_MVB_SRC_RDY,
            TX_MVB_DST_RDY  => TX_MVB_DST_RDY,

            SW_ADDR         => SW_ADDR,
            SW_SLICE        => SW_SLICE,
            SW_DIN          => SW_DIN,
            SW_BE           => SW_BE,
            SW_WRITE        => SW_WRITE,
            SW_READ         => SW_READ,
            SW_DOUT         => SW_DOUT,
            SW_DOUT_VLD     => SW_DOUT_VLD
        );
    end generate;

    bram_g: if ((LUT_DEPTH > 64 and LUT_ARCH = "AUTO") or (LUT_DEPTH > 1 and LUT_ARCH = "BRAM")) generate
        bram_i : entity work.MVB_LOOKUP_TABLE_BRAM
        generic map(
            MVB_ITEMS  => MVB_ITEMS,
            LUT_DEPTH  => LUT_DEPTH,
            LUT_WIDTH  => LUT_WIDTH,
            SW_WIDTH   => SW_WIDTH,
            META_WIDTH => META_WIDTH,
            OUTPUT_REG => OUTPUT_REG,
            DEVICE     => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RESET,

            RX_MVB_LUT_ADDR => RX_MVB_LUT_ADDR,
            RX_MVB_METADATA => RX_MVB_METADATA,
            RX_MVB_VLD      => RX_MVB_VLD,
            RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

            TX_MVB_LUT_DATA => TX_MVB_LUT_DATA,
            TX_MVB_LUT_ADDR => TX_MVB_LUT_ADDR,
            TX_MVB_METADATA => TX_MVB_METADATA,
            TX_MVB_VLD      => TX_MVB_VLD,
            TX_MVB_SRC_RDY  => TX_MVB_SRC_RDY,
            TX_MVB_DST_RDY  => TX_MVB_DST_RDY,

            SW_ADDR         => SW_ADDR,
            SW_SLICE        => SW_SLICE,
            SW_DIN          => SW_DIN,
            SW_BE           => SW_BE,
            SW_WRITE        => SW_WRITE,
            SW_READ         => SW_READ,
            SW_DOUT         => SW_DOUT,
            SW_DOUT_VLD     => SW_DOUT_VLD
        );
    end generate;

end architecture;
