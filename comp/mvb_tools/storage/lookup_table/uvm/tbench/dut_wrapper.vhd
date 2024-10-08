-- metadata_insertor.vhd: DUT Wrapper
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

entity DUT_WRAPPER is
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

        RX_MVB_LUT_ADDR : in  slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)+2-1 downto 0);
        RX_MVB_METADATA : in  slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0) := (others => (others => '0'));
        RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY  : in  std_logic;
        RX_MVB_DST_RDY  : out std_logic;

        TX_MVB_LUT_DATA : out slv_array_t(MVB_ITEMS-1 downto 0)(LUT_WIDTH-1 downto 0);
        TX_MVB_LUT_ADDR : out slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)+2-1 downto 0);
        TX_MVB_METADATA : out slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY  : out std_logic;
        TX_MVB_DST_RDY  : in  std_logic;

        MI_ADDR         : in  std_logic_vector(max(log2(LUT_DEPTH),1)+2-1 downto 0);
        MI_SLICE        : in  std_logic_vector(max(log2(LUT_WIDTH/SW_WIDTH),1)-1 downto 0);
        MI_DIN          : in  std_logic_vector(SW_WIDTH-1 downto 0);
        MI_BE           : in  std_logic_vector(SW_WIDTH/8-1 downto 0);
        MI_WRITE        : in  std_logic;
        MI_READ         : in  std_logic;
        MI_DOUT         : out std_logic_vector(SW_WIDTH-1 downto 0);
        MI_DOUT_VLD     : out std_logic
    );
    end entity;


architecture FULL of DUT_WRAPPER is
    signal rx_mvb_lut_addr_sig : slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)-1 downto 0);
    signal tx_mvb_lut_addr_sig : slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)-1 downto 0);
    signal sw_addr_sig         : std_logic_vector(max(log2(LUT_DEPTH),1)-1 downto 0);
begin

    lut_depth_reg_g : if LUT_DEPTH = 1 generate
        lut_addr_g : for i in 0 to MVB_ITEMS-1 generate
            rx_mvb_lut_addr_sig(i)(0) <= '0';
            tx_mvb_lut_addr_sig(i)(0) <= '0';
        end generate;

        sw_addr_sig(0) <= '0';
    else generate
        lut_addr_g : for i in 0 to MVB_ITEMS-1 generate
            rx_mvb_lut_addr_sig(i) <= RX_MVB_LUT_ADDR(i)(max(log2(LUT_DEPTH), 1)+2-1 downto 2);
            tx_mvb_lut_addr_sig(i) <= TX_MVB_LUT_ADDR(i)(max(log2(LUT_DEPTH), 1)+2-1 downto 2);
        end generate;

        sw_addr_sig <= MI_ADDR(max(log2(LUT_DEPTH), 1)+2-1 downto 2);
    end generate;

    dut_i : entity work.MVB_LOOKUP_TABLE
    generic map(
        MVB_ITEMS  => MVB_ITEMS,
        LUT_DEPTH  => LUT_DEPTH,
        LUT_WIDTH  => LUT_WIDTH,
        LUT_ARCH   => LUT_ARCH,
        SW_WIDTH   => SW_WIDTH,
        META_WIDTH => META_WIDTH,
        OUTPUT_REG => OUTPUT_REG,
        DEVICE     => DEVICE
    )
    port map(
        CLK             => CLK,
        RESET           => RESET,

        RX_MVB_LUT_ADDR => rx_mvb_lut_addr_sig,
        RX_MVB_METADATA => RX_MVB_METADATA,
        RX_MVB_VLD      => RX_MVB_VLD,
        RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

        TX_MVB_LUT_DATA => TX_MVB_LUT_DATA,
        TX_MVB_LUT_ADDR => tx_mvb_lut_addr_sig,
        TX_MVB_METADATA => TX_MVB_METADATA,
        TX_MVB_VLD      => TX_MVB_VLD,
        TX_MVB_SRC_RDY  => TX_MVB_SRC_RDY,
        TX_MVB_DST_RDY  => TX_MVB_DST_RDY,

        SW_ADDR         => sw_addr_sig,
        SW_SLICE        => MI_SLICE,
        SW_DIN          => MI_DIN,
        SW_BE           => MI_BE,
        SW_WRITE        => MI_WRITE,
        SW_READ         => MI_READ,
        SW_DOUT         => MI_DOUT,
        SW_DOUT_VLD     => MI_DOUT_VLD
    );

end architecture;
