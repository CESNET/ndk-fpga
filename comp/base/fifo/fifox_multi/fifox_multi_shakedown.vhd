-- fifox_multi_shakedown.vhd: FIFOX MULTI architecture
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             Description
-- ----------------------------------------------------------------------------
-- This architecture consists of a simple FIFOX and a MVB SHAKEDOWN at the end.
-- PROS:
--     - Less resources thanks to only one FIFOX being present.
--     - Output propagated directly from a register.
-- CONS:
--     - Output register is connected in a self-loop through a MVB SHAKEDOWN.
--       This SHAKEDOWN has MUXes twice as wide as would be needed
--       in architecture FULL.
--     - Worse buffering capabilities. (The data words FIFOX contain non-valid
--       items)
--     - Worse throughput (approximately 87% compared to architecture FULL
--       according to tests in simulation).

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture SHAKEDOWN of FIFOX_MULTI is

    -- Number of data words in SHAKEDOWN register
    -- Changes the width of MUXes in SHAKEDOWN and the throughput.
    -- Higher values -> higher width and higher throughput
    -- throughputs compared to architecture FULL:
    --   1 REG  -> ~50%
    --   2 REGS -> ~87%
    --   3 REGS -> ~94%
    --   4 REGS -> ~96%
    constant SHAKEDOWN_REGS      : integer := 2;

    constant FIFOX_AFULL_OFFSET  : integer := (ALMOST_FULL_OFFSET+WRITE_PORTS-1)/WRITE_PORTS; -- divide and round up
    constant FIFOX_AEMPTY_OFFSET : integer := max(0,(ALMOST_EMPTY_OFFSET-SHAKEDOWN_REGS+WRITE_PORTS-1)/WRITE_PORTS);

    -- -------------------------------------------------------------------------
    -- FIFOX
    -- -------------------------------------------------------------------------

    constant FIFOX_DATA_WIDTH : integer := DATA_WIDTH*WRITE_PORTS+WRITE_PORTS; -- data + valid bits
    signal fifox_rd      : std_logic;
    signal fifox_empty   : std_logic;
    signal fifox_do      : std_logic_vector(FIFOX_DATA_WIDTH-1 downto 0);
    signal fifox_do_data : std_logic_vector(WRITE_PORTS*DATA_WIDTH-1 downto 0);
    signal fifox_do_vld  : std_logic_vector(WRITE_PORTS-1 downto 0);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB SHAKEDOWN
    -- -------------------------------------------------------------------------

    signal sh_data : std_logic_vector(READ_PORTS*DATA_WIDTH-1 downto 0);
    signal sh_vld  : std_logic_vector(READ_PORTS-1 downto 0);
    signal sh_next : std_logic_vector(READ_PORTS-1 downto 0);

    -- -------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- Assert checking
    -- -------------------------------------------------------------------------

    assert_pr : process (CLK)
        variable rd_i  : natural;
        variable rd_en : boolean;
    begin
        if (rising_edge(CLK)) then
            if (RESET/='1') then
                rd_en := true;
                for i in 0 to READ_PORTS-1 loop
                    if (SAFE_READ_MODE=false and RD(i)='1' and EMPTY(i)='1') then
                        assert (false)
                            report "ERROR: FIFOX Multi: Non-safe Read Mode condition violated! Reading from port " & to_string(i) & " is forbidden when it is EMPTY!"
                            severity failure;
                    end if;

                    if (RD(i)/='1' and EMPTY(i)/='1') then
                        rd_i  := i;
                        rd_en := false;
                    end if;
                    if (rd_en=false and RD(i)='1' and EMPTY(i)/='1') then
                        assert (false)
                            report "ERROR: FIFOX Multi: Aligned read condition viloated! Reading from non-empty port " & to_string(i) & " is forbidden when not reading from port " & to_string(rd_i) & "!"
                            severity failure;
                    end if;
                end loop;
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- FIFOX
    -- -------------------------------------------------------------------------

    fifox_i : entity work.FIFOX
    generic map(
        DATA_WIDTH          => FIFOX_DATA_WIDTH   ,
        ITEMS               => ITEMS/WRITE_PORTS  ,
        RAM_TYPE            => RAM_TYPE           ,
        DEVICE              => DEVICE             ,
        ALMOST_FULL_OFFSET  => FIFOX_AFULL_OFFSET ,
        ALMOST_EMPTY_OFFSET => FIFOX_AEMPTY_OFFSET,
        FAKE_FIFO           => false
    )
    port map(
        CLK    => CLK  ,
        RESET  => RESET,

        DI     => DI & WR,
        WR     => (or WR),
        FULL   => FULL   ,
        AFULL  => AFULL  ,

        DO     => fifox_do   ,
        RD     => fifox_rd   ,
        EMPTY  => fifox_empty,
        AEMPTY => AEMPTY
    );

    fifox_do_data <= fifox_do(fifox_do'high downto WRITE_PORTS);
    fifox_do_vld  <= fifox_do(WRITE_PORTS-1 downto 0);

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- MVB SHAKEDOWN
    -- -------------------------------------------------------------------------

    shakedown_i : entity work.MVB_SHAKEDOWN
    generic map(
        RX_ITEMS    => WRITE_PORTS   ,
        TX_ITEMS    => READ_PORTS    ,
        ITEM_WIDTH  => DATA_WIDTH    ,
        SHAKE_PORTS => SHAKEDOWN_REGS
    )
    port map(
        CLK        => CLK  ,
        RESET      => RESET,

        RX_DATA    => fifox_do_data  ,
        RX_VLD     => fifox_do_vld   ,
        RX_SRC_RDY => not fifox_empty,
        RX_DST_RDY => fifox_rd       ,

        TX_DATA    => sh_data,
        TX_VLD     => sh_vld ,
        TX_NEXT    => sh_next
    );

    DO      <= sh_data;
    EMPTY   <= not sh_vld;
    sh_next <= RD;

    -- -------------------------------------------------------------------------

end architecture;
