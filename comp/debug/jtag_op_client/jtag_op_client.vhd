-- jtag_op_client.vhd : Client for JTAG-Over-Protocol communication
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------
entity JTAG_OP_CLIENT is
    generic(
        -- MI Address word width in bits.
        MI_ADDR_WIDTH : natural := 32;
        -- MI Data word width in bits.
        MI_DATA_WIDTH : natural := 32;
        -- MI Metadata word width in bits.
        MI_META_WIDTH : natural := 1;
        -- Target device (Intel only).
        DEVICE        : string  := "AGILEX"
    );
    port(
        -- =================
        --  Clock and Reset
        -- =================

        -- 200 MHz
        USER_CLK   : in  std_logic;
        USER_RESET : in  std_logic;

        -- Operating frequency of the JTAG-over-protocol IP must be 100 MHz or lower.
        JOP_CLK    : in  std_logic;
        JOP_RESET  : in  std_logic;

        -- ==============
        --  MI interface
        -- ==============

        -- Address
        MI_ADDR  : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
        -- Input Data
        MI_DWR   : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- Input Metadata
        MI_MWR   : in  std_logic_vector(MI_META_WIDTH-1 downto 0) := (others => '0');
        -- Byte Enable
        MI_BE    : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        -- Write Request
        MI_WR    : in  std_logic;
        -- Read Request
        MI_RD    : in  std_logic;
        -- Address Ready
        MI_ARDY  : out std_logic;
        -- Output Data
        MI_DRD   : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        -- Data Ready
        MI_DRDY  : out std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of JTAG_OP_CLIENT is

    -- synchronized MI interface
    signal sync_mi_addr          : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    signal sync_mi_dwr           : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_mwr           : std_logic_vector(MI_META_WIDTH-1 downto 0);
    signal sync_mi_be            : std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
    signal sync_mi_wr            : std_logic;
    signal sync_mi_rd            : std_logic;
    signal sync_mi_ardy          : std_logic;
    signal sync_mi_drd           : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_drdy          : std_logic;

    -- JTAG_OP IP
    constant JTAG_OP_ADDR_WIDTH  : natural := 14;
    signal jtag_op_address       : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    signal jtag_op_writedata     : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal jtag_op_byteenable    : std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
    signal jtag_op_write         : std_logic;
    signal jtag_op_read          : std_logic;
    signal jtag_op_waitrequest   : std_logic;
    signal jtag_op_readdata      : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal jtag_op_readdatavalid : std_logic;

    component JTAG_OP_IP is
    port (
        CLK_CLK              : in  std_logic;
        RESET_RESET          : in  std_logic;

        AVMM_S_ADDRESS       : in  std_logic_vector(JTAG_OP_ADDR_WIDTH-1 downto 0);
        AVMM_S_WRITEDATA     : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        AVMM_S_BYTEENABLE    : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        AVMM_S_WRITE         : in  std_logic;
        AVMM_S_READ          : in  std_logic;
        AVMM_S_WAITREQUEST   : out std_logic;
        AVMM_S_READDATA      : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        AVMM_S_READDATAVALID : out std_logic;

        AVMM_S_BURSTCOUNT    : in  std_logic_vector(1-1 downto 0);
        AVMM_S_DEBUGACCESS   : in  std_logic
    );
    end component;

begin

    -- =========================================================================
    --  MI32 LOGIC
    -- =========================================================================

    mi_async_i : entity work.MI_ASYNC
    generic map(
        ADDR_WIDTH => MI_ADDR_WIDTH,
        DATA_WIDTH => MI_DATA_WIDTH,
        META_WIDTH => MI_META_WIDTH,
        DEVICE     => DEVICE
    )
    port map(
        -- Master interface
        CLK_M     => USER_CLK,
        RESET_M   => USER_RESET,
        MI_M_DWR  => MI_DWR,
        MI_M_MWR  => MI_MWR,
        MI_M_ADDR => MI_ADDR,
        MI_M_RD   => MI_RD,
        MI_M_WR   => MI_WR,
        MI_M_BE   => MI_BE,
        MI_M_DRD  => MI_DRD,
        MI_M_ARDY => MI_ARDY,
        MI_M_DRDY => MI_DRDY,

        -- Slave interface
        CLK_S     => JOP_CLK,
        RESET_S   => JOP_RESET,
        MI_S_DWR  => sync_mi_dwr,
        MI_S_MWR  => sync_mi_mwr,
        MI_S_ADDR => sync_mi_addr,
        MI_S_RD   => sync_mi_rd,
        MI_S_WR   => sync_mi_wr,
        MI_S_BE   => sync_mi_be,
        MI_S_DRD  => sync_mi_drd,
        MI_S_ARDY => sync_mi_ardy,
        MI_S_DRDY => sync_mi_drdy
    );

    mi2avmm_i : entity work.MI2AVMM
    generic map(
        DATA_WIDTH => MI_DATA_WIDTH,
        ADDR_WIDTH => MI_ADDR_WIDTH,
        META_WIDTH => MI_META_WIDTH,
        DEVICE     => DEVICE
    )
    port map(
        CLK                => JOP_CLK,
        RESET              => JOP_RESET,

        MI_ADDR            => sync_mi_addr,
        MI_DWR             => sync_mi_dwr,
        MI_MWR             => sync_mi_mwr,
        MI_BE              => sync_mi_be,
        MI_WR              => sync_mi_wr,
        MI_RD              => sync_mi_rd,
        MI_ARDY            => sync_mi_ardy,
        MI_DRD             => sync_mi_drd,
        MI_DRDY            => sync_mi_drdy,

        AVMM_ADDRESS       => jtag_op_address,
        AVMM_WRITEDATA     => jtag_op_writedata,
        AVMM_BYTEENABLE    => jtag_op_byteenable,
        AVMM_WRITE         => jtag_op_write,
        AVMM_READ          => jtag_op_read,
        AVMM_WAITREQUEST   => jtag_op_waitrequest,
        AVMM_READDATA      => jtag_op_readdata,
        AVMM_READDATAVALID => jtag_op_readdatavalid
    );

    jtag_op_ip_i : component JTAG_OP_IP
    port map (
        CLK_CLK              => JOP_CLK,
        RESET_RESET          => JOP_RESET,

        AVMM_S_ADDRESS       => jtag_op_address(JTAG_OP_ADDR_WIDTH-1 downto 0),
        AVMM_S_WRITEDATA     => jtag_op_writedata,
        AVMM_S_BYTEENABLE    => jtag_op_byteenable,
        AVMM_S_WRITE         => jtag_op_write,
        AVMM_S_READ          => jtag_op_read,
        AVMM_S_WAITREQUEST   => jtag_op_waitrequest,
        AVMM_S_READDATA      => jtag_op_readdata,
        AVMM_S_READDATAVALID => jtag_op_readdatavalid,

        AVMM_S_BURSTCOUNT    => (others => '0'),
        AVMM_S_DEBUGACCESS   => '0'
    );

end architecture;
