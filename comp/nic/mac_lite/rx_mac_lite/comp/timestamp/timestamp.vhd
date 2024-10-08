-- crc_check.vhd: timestamp for GMII decoder
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_TIMESTAMP is
    generic(
        REGIONS : natural := 4 -- any possitive value
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;
        -- =====================================================================
        -- INPUT MFB SIGNALS
        -- =====================================================================
        RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        -- =====================================================================
        -- INPUT TIMESTAMP INTERFACE FROM TSU
        -- =====================================================================
        -- Timestamp in nanosecond (new) format, more info in TSU.
        TSU_TS_NS  : in  std_logic_vector(63 downto 0);
        -- Valid flag of timestamp.
        TSU_TS_DV  : in  std_logic;
        -- =====================================================================
        -- OUTPUT MVB TIMESTAMP INTERFACE ALIGNED ON EOF
        -- =====================================================================
        -- Timestamp MVB data, LSB bit is valid.
        TS_DATA    : out std_logic_vector(REGIONS*65-1 downto 0);
        -- Timestamp MVB valid flag aligned on EOF.
        TS_VLD     : out std_logic_vector(REGIONS-1 downto 0);
        -- Timestamp MVB source ready flag.
        TS_SRC_RDY : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_TIMESTAMP is

begin

    -- timestamping registers
    time_stamping_g : for r in 0 to REGIONS-1 generate
        s_ts_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                TS_DATA((r+1)*65-1 downto r*65) <= TSU_TS_NS & TSU_TS_DV;
                TS_VLD(r)  <= RX_EOF(r);
            end if;
        end process;
    end generate;

    -- timestamping source ready register
    s_ts_src_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                TS_SRC_RDY <= '0';
            else
                TS_SRC_RDY <= (or RX_EOF) and RX_SRC_RDY;
            end if;
        end if;
    end process;

end architecture;
