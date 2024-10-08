-- deficit_idle_counter.vhd: Ethernet DIC and inter packet gap counter
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

use work.dma_bus_pack.all;

-- =========================================================================
--                                 Description
-- =========================================================================
-- Calculates gap sizes for each input packet while maintaining
-- deficit idle count according to Ethernet specification.
-- =========================================================================

entity DEFICIT_IDLE_COUNTER is
generic(
    -- Maximum number of pakcets processed in one cycle
    PKTS         : natural := 4;
    -- Maximum packet size
    PKT_SIZE     : natural := 2**12;
    -- Required average inter-packet gap size (same units as PKT_SIZE)
    GAP_SIZE     : natural := 12;
    -- Start of packet alignment (causes inter-packet gap enlargement) (same units as PKT_SIZE)
    ALIGN        : natural := 8;
    -- Minimum inter-packet gap size (same units as PKT_SIZE)
    -- Minimum value: GAP_SIZE-ALIGN+1
    MIN_GAP_SIZE : integer := GAP_SIZE-4
);
port(
    -- =====================================================================
    --  Clock and Reset
    -- =====================================================================
    -- The Clock is only used for internal DIC register.
    -- The inner RX-to-TX logic is purely asynchronous.

    CLK   : in  std_logic;
    RESET : in  std_logic;

    -- =====================================================================

    -- =====================================================================
    --  Other interfaces
    -- =====================================================================

    -- Input Packet lengths
    RX_PKT_LEN     : in  slv_array_t     (PKTS-1 downto 0)(log2(PKT_SIZE+1)-1 downto 0);
    RX_PKT_VLD     : in  std_logic_vector(PKTS-1 downto 0);
    RX_PKT_SRC_RDY : in  std_logic;
    RX_PKT_DST_RDY : out std_logic; -- propagated from TX_PKT_DST_RDY

    -- Output Packet gap lengths
    TX_PKT_GAP     : out slv_array_t     (PKTS-1 downto 0)(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
    TX_PKT_VLD     : out std_logic_vector(PKTS-1 downto 0);
    TX_PKT_SRC_RDY : out std_logic; -- propagated from RX_PKT_SRC_RDY
    TX_PKT_DST_RDY : in  std_logic

    -- =====================================================================
);
end entity;

architecture FULL of DEFICIT_IDLE_COUNTER is

    -- =====================================================================
    --  Constants, aliases, functions
    -- =====================================================================

    -- The component only reduces gap sizes down to GAP_SIZE-ALIGN+1
    -- Cannot be negative.
    constant ACT_MIN_GAP_SIZE : integer := maximum(maximum(GAP_SIZE-ALIGN+1,MIN_GAP_SIZE),0);
    -- Maximum DIC used by one packet while not violating the minimum Gap size
    constant MAX_DIC          : natural := GAP_SIZE-ACT_MIN_GAP_SIZE;

    -- =====================================================================

    -- =====================================================================
    --  Deficit idle count register
    -- =====================================================================

    signal dic_reg             : unsigned(log2(PKTS*ALIGN)-1 downto 0);
    signal dic_reg_part        : unsigned(log2(PKTS*ALIGN/PKTS)-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  Gaps counting
    -- =====================================================================

    signal rx_pkt_len_end      : u_array_t(PKTS-1 downto 0)(log2(ALIGN)-1 downto 0);
    signal rx_pkt_len_end_rest : u_array_t(PKTS-1 downto 0)(log2(ALIGN)-1 downto 0);

    -- =====================================================================

begin

    -- =====================================================================
    --  Deficit idle count register
    -- =====================================================================

    dic_reg_pr : process (CLK)
        variable dic : unsigned(log2(PKTS*ALIGN)-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            dic := dic_reg;

            if (TX_PKT_DST_RDY='1' and RX_PKT_SRC_RDY='1') then
                for i in 0 to PKTS-1 loop
                    if (RX_PKT_VLD(i)='1') then
                        -- The DIC increases for every gap larger than average and decreases for every smaller one
                        dic := dic + (resize_left(unsigned(TX_PKT_GAP(i)),log2(PKTS*ALIGN)) - to_unsigned(GAP_SIZE,log2(PKTS*ALIGN)));
                    end if;
                end loop;
            end if;

            -- Apply roofing by maximum value of DIC
            if (dic>PKTS*MAX_DIC) then
                dic_reg <= to_unsigned(PKTS*MAX_DIC,log2(PKTS*ALIGN));
            else
                dic_reg <= dic;
            end if;

            if (RESET='1') then
                dic_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- Part of current DIC reserved for each packet in this cycle
    -- (This allows parallelism of DIC usage by individual packets,
    --  but might reduce effectivity in certain cases. The ineffectivness
    --  should however be accumulated over mutliple cycles and be
    --  compensated when it reaches a certain point.)
    -- (Example: PKTS = 4
    --  Cycle 1: dic_reg accumulates to 1 after, but 1/4 = 0, so it cannot be used.
    --  Cycle 2: dic_reg accumulates to 3 after, but 3/4 = 0, so it cannot be used.
    --  Cycle 3: dic_reg accumulates to 5 after, 5/4 = 1, so each packet can have Gap reduced by up to 1 byte.
    --  Cycle 4: dic_reg changes to 13, 13/4 = 3, so each packet can reduce its Gap by up to 3 bytes.)
    dic_reg_part <= enlarge_right(dic_reg,-log2(PKTS));

    -- =====================================================================

    -- =====================================================================
    --  Gaps counting
    -- =====================================================================

    rx_pkt_len_gen : for i in 0 to PKTS-1 generate
        rx_pkt_len_end     (i) <= resize_left(unsigned(RX_PKT_LEN(i)),log2(ALIGN));
        rx_pkt_len_end_rest(i) <= 0-rx_pkt_len_end(i);
    end generate;

    -- Gap is calculated independently for each packet to eliminate
    -- inter-packet dependency and improve timing.
    gap_cnt_gen : for i in 0 to PKTS-1 generate
        gap_cnt_pr : process(all)
            variable gap : unsigned(log2(GAP_SIZE+ALIGN+1)-1 downto 0);
        begin
            gap := to_unsigned(GAP_SIZE,gap'length);
            if (rx_pkt_len_end(i)<=dic_reg_part) then
                -- The gap can be reduced by the size of rx_pkt_len_end
                gap := gap - resize_left(rx_pkt_len_end(i),gap'length);
            else
                -- The gap must be enlarged by the size of rx_pkt_len_end_rest
                gap := gap + resize_left(rx_pkt_len_end_rest(i),gap'length);
            end if;
            TX_PKT_GAP(i) <= std_logic_vector(gap);
        end process;
    end generate;

    -- =====================================================================

    -- =====================================================================
    --  Propagate VLD, SRC_RDY and DST_RDY
    -- =====================================================================

    TX_PKT_VLD     <= RX_PKT_VLD;
    TX_PKT_SRC_RDY <= RX_PKT_SRC_RDY;
    RX_PKT_DST_RDY <= TX_PKT_DST_RDY;

    -- =====================================================================

end architecture;
