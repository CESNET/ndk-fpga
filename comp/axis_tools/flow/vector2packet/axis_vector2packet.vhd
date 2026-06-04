-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity AXIS_VECTOR2PACKET is
    generic (
        -- width of RX Logic vector data signal in bits
        RX_TDATA_WIDTH   : natural := 64;
        -- width of TX AXI-Stream data signal in bits - supported are only powers of 2
        TX_TDATA_WIDTH   : natural := 64;
        -- width of TX AXI-Stream user signal in bits
        TUSER_WIDTH      : natural := 64
    );
    port (
        -- =========================================================================
        -- Clock and reset signals
        -- =========================================================================
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =========================================================================
        -- RX Logic vector interface (CLK)
        -- =========================================================================
        RX_TDATA        : in  std_logic_vector(RX_TDATA_WIDTH-1 downto 0);
        RX_TUSER        : in  std_logic_vector(TUSER_WIDTH-1 downto 0);
        RX_TVALID       : in  std_logic;
        RX_TREADY       : out std_logic;

        -- =========================================================================
        -- TX AXI-Stream interface (CLK)
        -- =========================================================================
        TX_TDATA       : out std_logic_vector(TX_TDATA_WIDTH-1 downto 0);
        TX_TUSER       : out std_logic_vector(TUSER_WIDTH-1 downto 0);
        TX_TKEEP       : out std_logic_vector(TX_TDATA_WIDTH/8-1 downto 0);
        TX_TLAST       : out std_logic;
        TX_TVALID      : out std_logic;
        TX_TREADY      : in  std_logic
    );
end entity;

architecture FULL of AXIS_VECTOR2PACKET is

    constant PACKETS_PER_VECTOR : natural := div_roundup(RX_TDATA_WIDTH, TX_TDATA_WIDTH);  -- (RX_TDATA_WIDTH + TX_TDATA_WIDTH - 1) / TX_TDATA_WIDTH;
    constant PADDED_WIDTH       : natural := PACKETS_PER_VECTOR * TX_TDATA_WIDTH;          -- PAD_BITS + RX_TDATA_WIDTH
    constant PAD_BITS           : natural := PADDED_WIDTH - RX_TDATA_WIDTH;                -- count of padding bits

    signal rx_data_padded : std_logic_vector(PADDED_WIDTH-1 downto 0);                     -- PAD_BITS & RX_TDATA_WIDTH

    signal full : std_logic;                                                               -- whether component has unsent data or not
    signal sel  : unsigned(max(1,log2(PACKETS_PER_VECTOR))-1 downto 0) := (others => '0'); -- selects range to send from reg_data as a axis frame

    signal reg_data : std_logic_vector(PADDED_WIDTH-1 downto 0);
    signal reg_user : std_logic_vector(TUSER_WIDTH-1 downto 0);

begin
    -- pad data so that the last frame isnt out of range
    padding_g: if PAD_BITS > 0 generate
        rx_data_padded <= std_logic_vector(to_unsigned(0, PAD_BITS)) & RX_TDATA;
    else generate
        rx_data_padded <= RX_TDATA;
    end generate;

    RX_TREADY <= not full;
    TX_TVALID <= full;

    -- the component is either ready to receive data or transmits valid data
    full_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                full <= '0';
            elsif (full = '0') then -- RX_TREADY = '1'
                if (RX_TVALID = '1') then
                    -- if received valid data, set full (drives RX_TREADY low)
                    full <= '1';
                end if;
            else -- TX_TVALID = '1'
                if (TX_TREADY = '1') then
                    if (sel = PACKETS_PER_VECTOR - 1) then
                        -- if sent last frame, clear full (drives RX_TREADY high)
                        full <= '0';
                    end if;
                end if;
            end if;
        end if;
    end process;

    -- load new data to registers when RX side ready and valid
    regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '0') then
                if (RX_TREADY = '1' and RX_TVALID = '1') then
                    reg_data <= rx_data_padded;
                    reg_user <= RX_TUSER;
                end if;
            end if;
        end if;
    end process;

    -- if tx side ready, increments frame counter (sel) until last
    sel_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                sel <= (others => '0');
            elsif (full = '0') then -- RX_TREADY = '1'
                if (RX_TVALID = '1') then
                    sel <= (others => '0');
                end if;
            else -- TX_TVALID = '1'
                if (TX_TREADY = '1') then
                    if (sel < PACKETS_PER_VECTOR - 1) then
                        sel <= sel + 1;
                    end if;
                end if;
            end if;
        end if;
    end process;

    -- select range to send from reg_data as a axis frame
    mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => TX_TDATA_WIDTH,
        MUX_WIDTH  => PACKETS_PER_VECTOR
    ) port map (
        DATA_IN  => reg_data,
        SEL      => std_logic_vector(sel),
        DATA_OUT => TX_TDATA
    );

    TX_TUSER <= reg_user;
    TX_TLAST <= '1' when (sel = PACKETS_PER_VECTOR - 1) else '0';

    tx_tkeep_p : process (sel)
    begin
        TX_TKEEP <= (others => '1');
        -- if last frame, mark fully padded bytes (as keep = 0)
        if (sel = PACKETS_PER_VECTOR - 1 and PAD_BITS >= 8) then
            TX_TKEEP(TX_TDATA_WIDTH / 8 - 1 downto (TX_TDATA_WIDTH - PAD_BITS - 1) / 8 + 1) <= (others => '0');
        end if;
    end process;
end architecture;
