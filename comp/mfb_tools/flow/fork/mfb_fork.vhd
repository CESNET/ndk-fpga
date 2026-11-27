-- mfb_fork.vhd: Fork component for MFB
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;
use work.math_pack.all;



entity MFB_FORK is
    generic (
        OUTPUT_PORTS   : integer := 2; -- any possitive value

        -- =============================
        -- BUS characteristics
        --
        -- Frame size restrictions: none
        -- =============================

        -- any possitive value
        REGIONS        : integer := 4;
        -- any possitive value
        REGION_SIZE    : integer := 8;
        -- any possitive value
        BLOCK_SIZE     : integer := 8;
        -- any possitive value
        ITEM_WIDTH     : integer := 8;
        -- any possitive value
        META_WIDTH     : integer := 0;
        USE_DST_RDY    : boolean := true;

        -- =============================
        -- Others
        -- =============================

        -- Do not care when USE_DST_RDY is false.
        -- "logic"    - Fork waits with each word for all TX ports to set DST_RDY in the same cycle. Pure logic implementation.
        -- "register" - Fork can send each word independently to each TX port as soon as they are ready. The RX word is stored in an input register until it is sent to all TX ports, which adds one clock cycle of latency. Logic functions are simpler for larger forks.
        -- "simple"   - Same behaviour as "logic", but using simpler logic on SRC_RDY and DST_RDY with a potencial of logic loop creation. USE WITH CARE!
        VERSION        : string := "logic"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        RX_DATA       : in std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_META       : in std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS    : in std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF        : in std_logic_vector(REGIONS-1 downto 0);
        RX_EOF        : in std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY    : in std_logic;
        RX_DST_RDY    : out std_logic;

        TX_DATA       : out std_logic_vector(OUTPUT_PORTS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META       : out std_logic_vector(OUTPUT_PORTS*REGIONS*META_WIDTH-1 downto 0);
        TX_SOF_POS    : out std_logic_vector(OUTPUT_PORTS*REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS    : out std_logic_vector(OUTPUT_PORTS*REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF        : out std_logic_vector(OUTPUT_PORTS*REGIONS-1 downto 0);
        TX_EOF        : out std_logic_vector(OUTPUT_PORTS*REGIONS-1 downto 0);
        TX_SRC_RDY    : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
        TX_DST_RDY    : in std_logic_vector(OUTPUT_PORTS-1 downto 0)
    );
end entity;



architecture ARCH of MFB_FORK is

    constant DATA_WIDTH    : integer := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant SOF_POS_WIDTH : integer := REGIONS*max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH : integer := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));

    signal in_data    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal in_meta    : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal in_sof_pos : std_logic_vector(SOF_POS_WIDTH-1 downto 0);
    signal in_eof_pos : std_logic_vector(EOF_POS_WIDTH-1 downto 0);
    signal in_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal in_eof     : std_logic_vector(REGIONS-1 downto 0);
begin

    -- Control forking
    no_dst_rdy_gen: if not USE_DST_RDY generate
        RX_DST_RDY <= '1';
        TX_SRC_RDY <= (others => RX_SRC_RDY);
        in_data    <= RX_DATA;
        in_meta    <= RX_META;
        in_sof_pos <= RX_SOF_POS;
        in_eof_pos <= RX_EOF_POS;
        in_sof     <= RX_SOF;
        in_eof     <= RX_EOF;
    end generate;

    logic_fork_gen: if USE_DST_RDY and VERSION = "logic" generate
        RX_DST_RDY <= and_reduce(TX_DST_RDY);
        port_gen: for i in 0 to OUTPUT_PORTS-1 generate
            signal ready_base : std_logic_vector(OUTPUT_PORTS-1 downto 0);
        begin
            process (RX_SRC_RDY,TX_DST_RDY)
            begin
                ready_base    <= TX_DST_RDY;
                ready_base(i) <= RX_SRC_RDY; -- do not care about this TX port's DST_RDY to prevent logic loops, but care about SRC_RDY from RX
            end process;
            TX_SRC_RDY(i) <= and_reduce(ready_base);
        end generate;

        in_data    <= RX_DATA;
        in_meta    <= RX_META;
        in_sof_pos <= RX_SOF_POS;
        in_eof_pos <= RX_EOF_POS;
        in_sof     <= RX_SOF;
        in_eof     <= RX_EOF;
    end generate;

    register_fork_generate: if USE_DST_RDY and VERSION = "register" generate
        signal in_src_rdy : std_logic;
        signal in_accept  : std_logic;
        signal send_reg   : std_logic_vector(OUTPUT_PORTS-1 downto 0);
    begin
        RX_DST_RDY <= in_accept;

        in_accept <= '1' when in_src_rdy = '0' or and_reduce(TX_DST_RDY or send_reg) = '1' else '0';
        in_reg : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (in_accept = '1') then
                    in_data    <= RX_DATA;
                    in_meta    <= RX_META;
                    in_sof_pos <= RX_SOF_POS;
                    in_eof_pos <= RX_EOF_POS;
                    in_sof     <= RX_SOF;
                    in_eof     <= RX_EOF;
                    send_reg   <= (others => '0');
                else
                    send_reg <= send_reg or TX_DST_RDY;
                end if;
            end if;
        end process;

        in_src_rdy_reg : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    in_src_rdy <= '0';
                elsif (in_accept = '1') then
                    in_src_rdy <= RX_SRC_RDY;
                end if;
            end if;
        end process;

        TX_SRC_RDY <= (OUTPUT_PORTS-1 downto 0 => in_src_rdy) and not send_reg;
    end generate;

    simple_fork_gen: if USE_DST_RDY and VERSION = "simple" generate
        signal fork_ready : std_logic;
    begin
        fork_ready <= RX_SRC_RDY and and_reduce(TX_DST_RDY);
        RX_DST_RDY <= fork_ready;
        TX_SRC_RDY <= (others => fork_ready);
        in_data    <= RX_DATA;
        in_meta    <= RX_META;
        in_sof_pos <= RX_SOF_POS;
        in_eof_pos <= RX_EOF_POS;
        in_sof     <= RX_SOF;
        in_eof     <= RX_EOF;
    end generate;

    -- Data forking
    base_fork_gen: for i in 1 to OUTPUT_PORTS generate
        TX_DATA(i*DATA_WIDTH-1 downto (i-1)*DATA_WIDTH)                 <= in_data;
        TX_META(i*REGIONS*META_WIDTH-1 downto (i-1)*REGIONS*META_WIDTH) <= in_meta;
        TX_SOF_POS(i*SOF_POS_WIDTH-1 downto (i-1)*SOF_POS_WIDTH)        <= in_sof_pos;
        TX_EOF_POS(i*EOF_POS_WIDTH-1 downto (i-1)*EOF_POS_WIDTH)        <= in_eof_pos;
        TX_SOF(i*REGIONS-1 downto (i-1)*REGIONS)                        <= in_sof;
        TX_EOF(i*REGIONS-1 downto (i-1)*REGIONS)                        <= in_eof;
    end generate;

end architecture;
