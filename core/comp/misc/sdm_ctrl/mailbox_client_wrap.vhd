-- mailbox_client_wrap.vhd: Wrapper of Mailbox Client IP
-- Copyright (C) 2025 CESNET z.s.p.o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture FULL of SDM_CTRL_MAILBOX_CLIENT_WRAP is

    component mailbox_client_ip is
    port (
        in_clk_clk         : in  std_logic                     := 'X';             -- clk
        in_reset_reset     : in  std_logic                     := 'X';             -- reset
        avmm_address       : in  std_logic_vector(3 downto 0)  := (others => 'X'); -- address
        avmm_write         : in  std_logic                     := 'X';             -- write
        avmm_writedata     : in  std_logic_vector(31 downto 0) := (others => 'X'); -- writedata
        avmm_read          : in  std_logic                     := 'X';             -- read
        avmm_readdata      : out std_logic_vector(31 downto 0);                    -- readdata
        avmm_readdatavalid : out std_logic;                                        -- readdatavalid
        avmm_waitrequest   : out std_logic;                                        -- waitrequest
        irq_irq            : out std_logic                                         -- irq
    );
    end component mailbox_client_ip;

begin

    mailbox_client_i : component mailbox_client_ip
    port map (
        in_clk_clk         => CLK,
        in_reset_reset     => RESET,
        avmm_address       => AVMM_ADDRESS,
        avmm_write         => AVMM_WRITE,
        avmm_writedata     => AVMM_WRITEDATA,
        avmm_read          => AVMM_READ,
        avmm_readdata      => AVMM_READDATA,
        avmm_readdatavalid => AVMM_READDATAVALID,
        avmm_waitrequest   => AVMM_WAITREQUEST,
        irq_irq            => open
    );

end architecture;
