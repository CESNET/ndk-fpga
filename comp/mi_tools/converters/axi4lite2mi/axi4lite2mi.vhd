-- axi4lite2mi.vhd : AXI4-Lite to MI interface converter
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2025
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- Description:
-- Bridges an AXI4-Lite master (e.g. a processor or a vendor IP) to the MI bus
-- of NDK components. The component acts as an AXI4-Lite slave on one side and
-- as an MI master on the other; both sides share one clock domain.
--
-- Transactions are processed strictly one at a time by a single FSM: an AXI
-- read (AR + R channels) is translated to one MI read request (MI_RD) and an
-- AXI write (AW + W + B channels) to one MI write request (MI_WR). Address,
-- write data and byte strobes are registered before being presented on MI, and
-- read data are registered before being returned on the R channel. When AR and
-- AW requests arrive simultaneously, the read is served first. Both addresses
-- are masked by the ADDR_MASK generic. Responses are always OKAY ("00"), as MI
-- has no means of signalling errors.

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- This component converts AXI4-Lite interface (slave) to MI interface (master).
entity AXI4LITE2MI is
    generic (
        -- Data word width in bits, must be 32
        DATA_WIDTH  : natural := 32;
        -- Address word width in bits
        ADDR_WIDTH  : natural := 32;
        -- Address mask vector
        ADDR_MASK   : std_logic_vector(ADDR_WIDTH-1 downto 0) := (others => '1');
        -- Target device
        DEVICE      : string  := "AGILEX"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         : in  std_logic;
        RESET       : in  std_logic;

        -- =====================================================================
        -- AXI4-Lite interface (slave)
        -- =====================================================================
        AXI_AWADDR      : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        AXI_AWVALID     : in  std_logic;
        AXI_AWREADY     : out std_logic;

        AXI_WDATA       : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
        AXI_WSTRB       : in  std_logic_vector(DATA_WIDTH / 8 - 1 downto 0);
        AXI_WVALID      : in  std_logic;
        AXI_WREADY      : out std_logic;

        AXI_BRESP       : out std_logic_vector(1 downto 0);
        AXI_BVALID      : out std_logic;
        AXI_BREADY      : in  std_logic;

        AXI_ARADDR      : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        AXI_ARVALID     : in  std_logic;
        AXI_ARREADY     : out std_logic;

        AXI_RDATA       : out std_logic_vector(DATA_WIDTH - 1 downto 0);
        AXI_RRESP       : out std_logic_vector(1 downto 0);
        AXI_RVALID      : out std_logic;
        AXI_RREADY      : in  std_logic;

        -- =====================================================================
        -- MI interface (master)
        -- =====================================================================
        MI_DWR      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        MI_ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        MI_RD       : out std_logic;
        MI_WR       : out std_logic;
        MI_BE       : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);
        MI_DRD      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        MI_ARDY     : in  std_logic;
        MI_DRDY     : in  std_logic
    );
end entity;

architecture FULL of AXI4LITE2MI is

    -- =========================================================================
    -- FSM states
    -- =========================================================================
    -- ST_IDLE       : No transaction in progress, waiting for a new AXI request.
    --                 AXI_ARVALID is accepted immediately (AXI_ARREADY = '1'),
    --                 the masked read address is registered and the byte
    --                 enables are set to all ones -> ST_READ.
    --                 Otherwise AXI_AWVALID is accepted (AXI_AWREADY = '1') and
    --                 the masked write address is registered -> ST_WRITE.
    --                 Reads have priority over writes.
    -- ST_READ       : MI read request is issued (MI_RD = '1', MI_ADDR = read
    --                 address, MI_BE = all ones) and held until the MI slave
    --                 accepts it with MI_ARDY. If MI_DRDY comes together with
    --                 MI_ARDY, MI_DRD is registered -> ST_READ_RESP; otherwise
    --                 -> ST_READ_ARDY.
    -- ST_READ_ARDY  : MI read request has been accepted (MI_RD is deasserted),
    --                 waiting for the read data. When MI_DRDY = '1', MI_DRD is
    --                 registered -> ST_READ_RESP.
    -- ST_READ_RESP  : Registered read data are presented on the AXI R channel
    --                 (AXI_RVALID = '1', AXI_RRESP = OKAY) until the master
    --                 accepts them with AXI_RREADY -> ST_IDLE.
    -- ST_WRITE      : Write address has been accepted. AXI_WREADY is asserted;
    --                 when AXI_WVALID = '1', AXI_WDATA and AXI_WSTRB are
    --                 registered -> ST_WRITE_DATA.
    -- ST_WRITE_DATA : MI write request is issued (MI_WR = '1', MI_ADDR = write
    --                 address, MI_DWR/MI_BE = registered data/strobes) and held
    --                 until the MI slave accepts it with MI_ARDY
    --                 -> ST_WRITE_RESP.
    -- ST_WRITE_RESP : Write response is presented on the AXI B channel
    --                 (AXI_BVALID = '1', AXI_BRESP = OKAY) until the master
    --                 accepts it with AXI_BREADY -> ST_IDLE.
    type fsm_states is (ST_IDLE, ST_READ, ST_READ_ARDY, ST_READ_RESP, ST_WRITE, ST_WRITE_DATA, ST_WRITE_RESP);

    signal current_state  : fsm_states;
    signal next_state     : fsm_states;

    signal reg_raddr    : std_logic_vector(ADDR_WIDTH - 1 downto 0);
    signal reg_raddr_we : std_logic;

    signal reg_rdata    : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal reg_rdata_we : std_logic;

    signal reg_waddr    : std_logic_vector(ADDR_WIDTH - 1 downto 0);
    signal reg_waddr_we : std_logic;

    signal reg_wdata    : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal reg_wdata_we : std_logic;

    signal reg_strb     : std_logic_vector(DATA_WIDTH / 8 - 1 downto 0);
    signal reg_strb_we  : std_logic;
    signal reg_strb_set : std_logic;

    signal rd_wr        : std_logic;

begin

    reg_raddr_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (reg_raddr_we = '1') then
                reg_raddr <= AXI_ARADDR and ADDR_MASK;
            end if;
        end if;
    end process;

    reg_rdata_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (reg_rdata_we = '1') then
                reg_rdata <= MI_DRD;
            end if;
        end if;
    end process;

    reg_waddr_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (reg_waddr_we = '1') then
                reg_waddr <= AXI_AWADDR and ADDR_MASK;
            end if;
        end if;
    end process;

    reg_wdata_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (reg_wdata_we = '1') then
                reg_wdata <= AXI_WDATA;
            end if;
        end if;
    end process;

    reg_strbp : process (CLK)
    begin
        if rising_edge(CLK) then
            if (reg_strb_we = '1') then
                reg_strb <= AXI_WSTRB;
            elsif (reg_strb_set = '1') then
                -- MI reads always access the whole word
                reg_strb <= (others => '1');
            end if;
        end if;
    end process;

    fsm_state : process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                current_state <= ST_IDLE;
            else
                current_state <= next_state;
            end if;
        end if;
    end process;

    fsm_next : process (all)
    begin
        next_state <= current_state;

        case current_state is
            -- Wait for a new AXI request, read has priority over write
            when ST_IDLE =>
                if (AXI_ARVALID = '1') then
                    next_state <= ST_READ;
                else
                    if (AXI_AWVALID = '1') then
                        next_state <= ST_WRITE;
                    end if;
                end if;

            -- Issue MI read, wait for MI_ARDY (and possibly MI_DRDY)
            when ST_READ =>
                if (MI_ARDY = '1') then
                    if (MI_DRDY = '1') then
                        next_state <= ST_READ_RESP;
                    else
                        next_state <= ST_READ_ARDY;
                    end if;
                end if;

            -- MI read accepted, wait for MI_DRDY
            when ST_READ_ARDY =>
                if (MI_DRDY = '1') then
                    next_state <= ST_READ_RESP;
                end if;

            -- Return read data on AXI R channel, wait for AXI_RREADY
            when ST_READ_RESP =>
                if (AXI_RREADY = '1') then
                    next_state <= ST_IDLE;
                end if;

            -- Write address accepted, wait for write data (AXI_WVALID)
            when ST_WRITE =>
                if (AXI_WVALID = '1') then
                    next_state <= ST_WRITE_DATA;
                end if;

            -- Issue MI write, wait for MI_ARDY
            when ST_WRITE_DATA =>
                if (MI_ARDY = '1') then
                    next_state <= ST_WRITE_RESP;
                end if;

            -- Return write response on AXI B channel, wait for AXI_BREADY
            when ST_WRITE_RESP =>
                if (AXI_BREADY = '1') then
                    next_state  <= ST_IDLE;
                end if;

            -- Unreachable (all states are covered above), hold current state
            when others =>
        end case;
    end process;

    fsm_output : process (all)
    begin
        AXI_ARREADY    <= '0';
        AXI_RVALID     <= '0';
        AXI_AWREADY    <= '0';
        AXI_WREADY     <= '0';
        AXI_BVALID     <= '0';
        reg_raddr_we   <= '0';
        reg_rdata_we   <= '0';
        reg_waddr_we   <= '0';
        reg_wdata_we   <= '0';
        reg_strb_we    <= '0';
        reg_strb_set   <= '0';
        rd_wr          <= '0';
        MI_RD          <= '0';
        MI_WR          <= '0';

        case current_state is
            when ST_IDLE =>
                if (AXI_ARVALID = '1') then
                    AXI_ARREADY  <= '1';
                    reg_raddr_we <= '1';
                    reg_strb_set <= '1';
                else
                    if (AXI_AWVALID = '1') then
                        AXI_AWREADY   <= '1';
                        reg_waddr_we  <= '1';
                    end if;
                end if;

            when ST_READ =>
                if (MI_ARDY = '1') then
                    if (MI_DRDY = '1') then
                        reg_rdata_we <= '1';
                    end if;
                end if;
                MI_RD <= '1';

            when ST_READ_ARDY =>
                if (MI_DRDY = '1') then
                    reg_rdata_we <= '1';
                end if;

            when ST_READ_RESP =>
                AXI_RVALID <= '1';

            when ST_WRITE =>
                AXI_WREADY   <= '1';
                reg_wdata_we <= AXI_WVALID;
                reg_strb_we  <= AXI_WVALID;

            when ST_WRITE_DATA =>
                rd_wr      <= '1';
                MI_WR      <= '1';

            when ST_WRITE_RESP =>
                AXI_BVALID <= '1';

            when others =>
        end case;
    end process;

    MI_ADDR <= reg_raddr when rd_wr = '0' else reg_waddr;
    MI_BE   <= reg_strb;
    MI_DWR  <= reg_wdata;

    AXI_RDATA <= reg_rdata;
    AXI_BRESP <= "00";
    AXI_RRESP <= "00";
end architecture;
