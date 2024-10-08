-- hyper_pipe.vhd: Hyper Pipe Registers optimized for Stratix 10
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

entity HYPER_PIPE is
    generic(
        -- Data word width in bits.
        DATA_WIDTH : natural := 8;
        -- Latency in clock cycles, specifies the number of Hyper-Registers.
        LATENCY    : natural := 2
    );
    port(
        CLK  : in  std_logic;
        DIN  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        DOUT : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture behavioral of HYPER_PIPE is

    type reg_array_t is array (LATENCY-1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);

    signal hyper_pipe : reg_array_t;

    -- Prevent large hyper-pipes from going into memory-based altshift_taps.
    attribute ALTERA_ATTRIBUTE : string;
 	attribute ALTERA_ATTRIBUTE of hyper_pipe :
        signal is "-name AUTO_SHIFT_REGISTER_RECOGNITION off";

begin

    -- Only wire without Hyper-Registers
    only_wires_g : if LATENCY = 0 generate
        DOUT <= DIN;
    end generate;

    -- Pipe of Hyper-Registers
    hyper_pipe_on_g : if LATENCY > 0 generate
        hyper_pipe_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                hyper_pipe <= hyper_pipe(LATENCY-2 downto 0) & DIN;
            end if;
        end process;

        DOUT <= hyper_pipe(LATENCY-1);
    end generate;

end architecture;
