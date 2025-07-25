--!
--! sync_pgen.vhd: Synchronized enable pulse generator
--! Copyright (C) 2014 CESNET
--! Author(s): Jakub Cabal <cabal@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!
--! TODO:

library IEEE;
use IEEE.std_logic_1164.all;

--! -------------------------------------------------------------------------
--!                      Entity declaration
--! -------------------------------------------------------------------------

entity SYNC_PGEN is
    port (
        --! A clock domain
        ACLK      : in  STD_LOGIC;   --! Source CLK
        ARST      : in  STD_LOGIC;   --! Source reset
        ADATAIN   : in  STD_LOGIC;   --! Data input

        --! B clock domain
        BCLK      : in  STD_LOGIC;   --! Target CLK
        BRST      : in  STD_LOGIC;   --! Target reset
        BEN       : out STD_LOGIC;   --! Enable pulse
        BDATAOUT  : out STD_LOGIC    --! Data output
    );
end entity;

--! -------------------------------------------------------------------------
--!                      Architecture declaration
--! -------------------------------------------------------------------------

architecture FULL of SYNC_PGEN is

    signal signal_d1    : std_logic;
    signal signal_q1    : std_logic := '0';

    --! -------------------------------------------------------------------------
begin
    --! -------------------------------------------------------------------------

    --! Open-loop
    async_open_loop: entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG  => true,     --! We need input FF with reset, else !
        TWO_REG => false     --! Set three sync registers
    )
    port map (
        ACLK     => ACLK,
        BCLK     => BCLK,
        ARST     => ARST,
        BRST     => BRST,
        ADATAIN  => ADATAIN,
        BDATAOUT => signal_d1
    );

    --! -------------------------------------------------------------------------

    process (BCLK)
    begin
        if (rising_edge(BCLK)) then
            if (BRST = '1') then
                signal_q1 <= '0';
            else
                signal_q1 <= signal_d1;
            end if;
        end if;
    end process;

    BDATAOUT <= signal_q1;
    BEN      <= signal_d1 xor signal_q1;

    --! -------------------------------------------------------------------------

end architecture;
