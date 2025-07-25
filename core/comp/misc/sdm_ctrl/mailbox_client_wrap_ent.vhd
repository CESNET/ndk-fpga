-- mailbox_client_wrap_ent.vhd: Wrapper of Mailbox Client IP
-- Copyright (C) 2025 CESNET z.s.p.o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

entity SDM_CTRL_MAILBOX_CLIENT_WRAP is
    port (
        CLK                : in  std_logic;
        RESET              : in  std_logic;

        AVMM_ADDRESS       : in  std_logic_vector(3 downto 0);
        AVMM_WRITE         : in  std_logic;
        AVMM_WRITEDATA     : in  std_logic_vector(31 downto 0);
        AVMM_READ          : in  std_logic;
        AVMM_READDATA      : out std_logic_vector(31 downto 0);
        AVMM_READDATAVALID : out std_logic;
        AVMM_WAITREQUEST   : out std_logic := '0'
    );
end entity;
