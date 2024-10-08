-- sdm_client.vhd : Client for communication with Intel SDM via Mailbox Client IP using MI bus
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------
entity SDM_CLIENT is
    generic(
        -- Data word width in bits
        DATA_WIDTH : natural := 32;
        -- Address word width in bits
        ADDR_WIDTH : natural := 32;
        -- Target device (Intel only)
        -- (not used yet)
        DEVICE     : string  := "AGILEX"
    );
    port(
        -- ===============
        -- Clock and Reset
        -- ===============

        CLK   : in  std_logic;
        RESET : in  std_logic;

        -- ===============
        -- MI interface
        -- ===============

        -- Input Data
        MI_DWR   : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Address
        MI_ADDR  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        -- Read Request
        MI_RD    : in  std_logic;
        -- Write Request
        MI_WR    : in  std_logic;
        -- Byte Enable
        MI_BE    : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
        -- Output Data
        MI_DRD   : out std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Address Ready
        MI_ARDY  : out std_logic;
        -- Data Ready
        MI_DRDY  : out std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of SDM_CLIENT is

    constant MC_ADDR_WIDTH : natural := 4;

    component MAILBOX_CLIENT is
    port (
        IN_CLK_CLK         : in  std_logic;                                  -- clk
        IN_RESET_RESET     : in  std_logic;                                  -- reset
        AVMM_ADDRESS       : in  std_logic_vector(MC_ADDR_WIDTH-1 downto 0); -- address
        AVMM_WRITE         : in  std_logic;                                  -- write
        AVMM_WRITEDATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);    -- writedata
        AVMM_READ          : in  std_logic;                                  -- read
        AVMM_READDATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);    -- readdata
        AVMM_READDATAVALID : out std_logic;                                  -- readdatavalid
        IRQ_IRQ            : out std_logic                                   -- irq
    );
    end component;

    -- mailbox client signals
    signal mc_addr     : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal mc_wr       : std_logic;
    signal mc_rd       : std_logic;
    signal mc_dwr      : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mc_drd      : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal mc_drd_vld  : std_logic;

    signal mc_offset   : std_logic_vector(MC_ADDR_WIDTH-1 downto 0);

begin

    -- MI to Avalon MM interface converter
    mi2avmm_i : entity work.MI2AVMM
    generic map(
        DATA_WIDTH => DATA_WIDTH,
        ADDR_WIDTH => ADDR_WIDTH,
        META_WIDTH => 1,
        DEVICE     => DEVICE
    )
    port map(
        CLK                => CLK,
        RESET              => RESET,

        MI_DWR             => MI_DWR,
        MI_MWR             => (others => '0'),
        MI_ADDR            => MI_ADDR,
        MI_RD              => MI_RD,
        MI_WR              => MI_WR,
        MI_BE              => MI_BE,
        MI_DRD             => MI_DRD,
        MI_ARDY            => MI_ARDY,
        MI_DRDY            => MI_DRDY,

        AVMM_ADDRESS       => mc_addr,
        AVMM_WRITE         => mc_wr,
        AVMM_READ          => mc_rd,
        AVMM_BYTEENABLE    => open,
        AVMM_WRITEDATA     => mc_dwr,
        AVMM_READDATA      => mc_drd,
        AVMM_READDATAVALID => mc_drd_vld,
        AVMM_WAITREQUEST   => '0'
    );

    -- Mailbox Client address is shifted 2 bits due to different addressing of both interfaces (MI - bytes, AVMM - words)
    mc_offset <= mc_addr(MC_ADDR_WIDTH+2-1 downto 2);

    -- Mailbox Client IP component
    mailbox_client_i : component MAILBOX_CLIENT
    port map (
        IN_CLK_CLK         => CLK,
        IN_RESET_RESET     => RESET,
        AVMM_ADDRESS       => mc_offset,
        AVMM_WRITE         => mc_wr,
        AVMM_WRITEDATA     => mc_dwr,
        AVMM_READ          => mc_rd,
        AVMM_READDATA      => mc_drd,
        AVMM_READDATAVALID => mc_drd_vld,
        IRQ_IRQ            => open
    );

end architecture;
