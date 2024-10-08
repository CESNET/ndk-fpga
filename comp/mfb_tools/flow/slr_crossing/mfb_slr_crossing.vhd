-- mvb_slr_crossing.vhd: MFB SLR Crossing
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity MFB_SLR_CROSSING is
generic(
    MFB_REGIONS    : integer := 2;
    MFB_REG_SIZE   : integer := 1;
    MFB_BLOCK_SIZE : integer := 4;
    MFB_ITEM_WIDTH : integer := 32;

    MFB_META_WIDTH : integer := 0;

    USE_OUTREG     : boolean:= true;
    FAKE_CROSSING  : boolean:= false;
    DEVICE         : string := "ULTRASCALE"
);
port(
    CLK        : in std_logic;

    RX_RESET   : in  std_logic;
    RX_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_META    : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    RX_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    TX_RESET   : in  std_logic;
    TX_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    TX_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    TX_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    TX_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic
);
end entity;

architecture arch of MFB_SLR_CROSSING is
    constant DATA_WIDTH    : integer := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant SOF_POS_WIDTH : integer := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant CROSSING_WIDTH        : integer := MFB_REGIONS*DATA_WIDTH
                                               +MFB_REGIONS*MFB_META_WIDTH
                                               +MFB_REGIONS
                                               +MFB_REGIONS
                                               +MFB_REGIONS*SOF_POS_WIDTH
                                               +MFB_REGIONS*EOF_POS_WIDTH;
    signal crossing_in_data        : std_logic_vector(CROSSING_WIDTH-1 downto 0);
    signal crossing_in_src_rdy     : std_logic;
    signal crossing_in_dst_rdy     : std_logic;
    signal crossing_out_data       : std_logic_vector(CROSSING_WIDTH-1 downto 0);
    signal crossing_out_src_rdy    : std_logic;
    signal crossing_out_dst_rdy    : std_logic;
begin
    crossing_in_data     <= RX_DATA & RX_META & RX_SOF & RX_EOF & RX_SOF_POS & RX_EOF_POS;
    crossing_in_src_rdy  <= RX_SRC_RDY;
    RX_DST_RDY           <= crossing_in_dst_rdy;

    TX_DATA    <= crossing_out_data(MFB_REGIONS*(DATA_WIDTH+MFB_META_WIDTH+1+1+SOF_POS_WIDTH+EOF_POS_WIDTH)-1 downto MFB_REGIONS*(MFB_META_WIDTH+1+1+SOF_POS_WIDTH+EOF_POS_WIDTH));
    TX_META    <= crossing_out_data(MFB_REGIONS*(           MFB_META_WIDTH+1+1+SOF_POS_WIDTH+EOF_POS_WIDTH)-1 downto MFB_REGIONS*(               1+1+SOF_POS_WIDTH+EOF_POS_WIDTH));
    TX_SOF     <= crossing_out_data(MFB_REGIONS*(                          1+1+SOF_POS_WIDTH+EOF_POS_WIDTH)-1 downto MFB_REGIONS*(                 1+SOF_POS_WIDTH+EOF_POS_WIDTH));
    TX_EOF     <= crossing_out_data(MFB_REGIONS*(                            1+SOF_POS_WIDTH+EOF_POS_WIDTH)-1 downto MFB_REGIONS*(                   SOF_POS_WIDTH+EOF_POS_WIDTH));
    TX_SOF_POS <= crossing_out_data(MFB_REGIONS*(                              SOF_POS_WIDTH+EOF_POS_WIDTH)-1 downto MFB_REGIONS*(                                 EOF_POS_WIDTH));
    TX_EOF_POS <= crossing_out_data(MFB_REGIONS*(                                            EOF_POS_WIDTH)-1 downto MFB_REGIONS*(                                             0));

    TX_SRC_RDY           <= crossing_out_src_rdy;
    crossing_out_dst_rdy <= TX_DST_RDY;

    SLR_CROSSING_I : entity work.SLR_CROSSING
    generic map(
        DATA_WIDTH      => CROSSING_WIDTH,
        USE_OUTREG      => USE_OUTREG,
        FAKE_CROSSING   => FAKE_CROSSING,
        DEVICE          => DEVICE
    ) port map(
        CLK         => CLK,
        IN_RESET     => RX_RESET,
        IN_DATA      => crossing_in_data,
        IN_SRC_RDY   => crossing_in_src_rdy,
        IN_DST_RDY   => crossing_in_dst_rdy,
        OUT_RESET    => TX_RESET,
        OUT_DATA     => crossing_out_data,
        OUT_SRC_RDY  => crossing_out_src_rdy,
        OUT_DST_RDY  => crossing_out_dst_rdy
    );
end architecture;
