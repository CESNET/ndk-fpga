-- fifox_multi_wrapper.vhd: FIFOX MULTI wrapper with multiple architectures for verification
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

entity FIFOX_MULTI_WRAPPER is
generic(
    DATA_WIDTH               : natural := 512;
    ITEMS                    : natural := 512;
    WRITE_PORTS              : natural := 4;
    READ_PORTS               : natural := 2;
    RAM_TYPE                 : string  := "AUTO";
    DEVICE                   : string  := "ULTRASCALE";
    ALMOST_FULL_OFFSET       : natural := 0;
    ALMOST_EMPTY_OFFSET      : natural := 0;
    ALLOW_SINGLE_FIFO        : boolean := true;
    SAFE_READ_MODE           : boolean := true;
    IMPLEMENTATION_SHAKEDOWN : boolean := false
);
port(
    CLK    : in  std_logic;
    RESET  : in  std_logic;

    DI     : in  std_logic_vector(WRITE_PORTS*DATA_WIDTH-1 downto 0);
    WR     : in  std_logic_vector(WRITE_PORTS-1 downto 0);
    FULL   : out std_logic;
    AFULL  : out std_logic;

    DO     : out std_logic_vector(READ_PORTS*DATA_WIDTH-1 downto 0);
    RD     : in  std_logic_vector(READ_PORTS-1 downto 0);
    EMPTY  : out std_logic_vector(READ_PORTS-1 downto 0);
    AEMPTY : out std_logic
);
end entity FIFOX_MULTI_WRAPPER;

architecture FULL of FIFOX_MULTI_WRAPPER is
begin

    -- -------------------------------------------------------------------------
    -- IMPLEMENTATION FULL
    -- -------------------------------------------------------------------------

    full_gen : if (not IMPLEMENTATION_SHAKEDOWN) generate
        fifox_multi_full_i : entity work.FIFOX_MULTI(FULL)
        generic map(
            DATA_WIDTH          => DATA_WIDTH,
            ITEMS               => ITEMS,
            WRITE_PORTS         => WRITE_PORTS,
            READ_PORTS          => READ_PORTS,
            RAM_TYPE            => RAM_TYPE,
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
            ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
            ALLOW_SINGLE_FIFO   => ALLOW_SINGLE_FIFO,
            SAFE_READ_MODE      => SAFE_READ_MODE
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => DI,
            WR     => WR,
            FULL   => FULL,
            AFULL  => AFULL,

            DO     => DO,
            RD     => RD,
            EMPTY  => EMPTY,
            AEMPTY => AEMPTY
        );
    end generate;

    -- -------------------------------------------------------------------------
    -- IMPLEMENTATION SHAKEDOWN
    -- -------------------------------------------------------------------------

    shakedown_gen : if (IMPLEMENTATION_SHAKEDOWN) generate
        fifox_multi_shakedown_i : entity work.FIFOX_MULTI(SHAKEDOWN)
        generic map(
            DATA_WIDTH          => DATA_WIDTH,
            ITEMS               => ITEMS,
            WRITE_PORTS         => WRITE_PORTS,
            READ_PORTS          => READ_PORTS,
            RAM_TYPE            => RAM_TYPE,
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
            ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
            ALLOW_SINGLE_FIFO   => ALLOW_SINGLE_FIFO,
            SAFE_READ_MODE      => SAFE_READ_MODE
        )
        port map(
            CLK    => CLK  ,
            RESET  => RESET,

            DI     => DI,
            WR     => WR,
            FULL   => FULL,
            AFULL  => AFULL,

            DO     => DO,
            RD     => RD,
            EMPTY  => EMPTY,
            AEMPTY => AEMPTY
        );
    end generate;

end architecture;
