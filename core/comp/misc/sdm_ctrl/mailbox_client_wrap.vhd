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
            IN_CLK_CLK         : in  std_logic                     := 'X';
            IN_RESET_RESET     : in  std_logic                     := 'X';
            AVMM_ADDRESS       : in  std_logic_vector(3 downto 0)  := (others => 'X');
            AVMM_WRITE         : in  std_logic                     := 'X';
            AVMM_WRITEDATA     : in  std_logic_vector(31 downto 0) := (others => 'X');
            AVMM_READ          : in  std_logic                     := 'X';
            AVMM_READDATA      : out std_logic_vector(31 downto 0);
            AVMM_READDATAVALID : out std_logic;
            AVMM_WAITREQUEST   : out std_logic;
            IRQ_IRQ            : out std_logic
        );
    end component;

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
