-- bin2hot.vhd
--!
--! \file
--! \brief Binary to one-hot converter.
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

entity bin2hot is
    generic (
        DATA_WIDTH : integer := 4
    );
    port (
        EN : in std_logic;
        INPUT : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        OUTPUT : out std_logic_vector(2**DATA_WIDTH-1 downto 0)
    );
end bin2hot;

architecture full of bin2hot is
begin
    output_fakeg: if DATA_WIDTH = 0 generate
        OUTPUT(0) <= EN;
    end generate;
    outputg: if DATA_WIDTH >= 1 generate
        process(INPUT, EN)
        begin
            OUTPUT <= (others => '0');
            if (EN = '1') then
               OUTPUT(to_integer(unsigned(INPUT))) <= '1';
            end if;
        end process;
    end generate;
end architecture;
