--! cmp_decode.vhd
--!
--! \file
--! \brief CMP decoders mplemented
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! decoder entity
entity CMP_DECODE is
    port (
        --! input for comparatar with lower priority
        L_IN        : in  std_logic_vector(1 downto 0);
        --! input for comparatar with higher priority
        H_IN        : in  std_logic_vector(1 downto 0);
        --! output data
        P           : out std_logic_vector(1 downto 0)
    );
end entity;

--! architecture of CMP_DECODE
architecture DECODE of CMP_DECODE is
    signal decode   : std_logic_vector(3 downto 0);
begin
    decode(1 downto 0) <= L_IN;
    decode(3 downto 2) <= H_IN;

    with decode select P <=
        "00" when "0000",
        "00" when "0011",
        "00" when "0010",
        "10" when "1000",
        "10" when "1011",
        "10" when "1010",
        "00" when "1100",
        "10" when "1110",
        "11" when "1111",
        "UU" when others;
end architecture;
