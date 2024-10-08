-- mi2axi4.vhd : MI to AXI4 interface converter
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- This component converts MI interface (slave) to AXI4 interface (master).
entity MI2AXI4 is
    generic(
        -- MI data word width in bits, must be 32
        MI_DATA_WIDTH  : natural  := 32;
        -- AXI data word width in bits, 32 or 64
        AXI_DATA_WIDTH : natural := 64;
        -- Address word width in bits
        ADDR_WIDTH     : natural := 32;
        -- Address mask vector
        ADDR_MASK      : std_logic_vector(ADDR_WIDTH-1 downto 0) := (others => '1');
        -- Target device
        DEVICE         : string  := "AGILEX"
    );
    port(
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         : in  std_logic;
        RESET       : in  std_logic;

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR      : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        MI_RD       : in  std_logic;
        MI_WR       : in  std_logic;
        MI_BE       : in  std_logic_vector((MI_DATA_WIDTH/8)-1 downto 0);
        MI_DRD      : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
        MI_ARDY     : out std_logic;
        MI_DRDY     : out std_logic;

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    : out std_logic_vector(8-1 downto 0);
        AXI_AWADDR  : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        AXI_AWPROT  : out std_logic_vector(3-1 downto 0);
        AXI_AWVALID : out std_logic;
        AXI_AWREADY : in  std_logic;
        AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB   : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_WVALID  : out std_logic;
        AXI_WREADY  : in  std_logic;
        AXI_BID     : in  std_logic_vector(8-1 downto 0);
        AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        AXI_BVALID  : in  std_logic;
        AXI_BREADY  : out std_logic;
        AXI_ARID    : out std_logic_vector(8-1 downto 0);
        AXI_ARADDR  : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        AXI_ARLEN   : out std_logic_vector(8-1 downto 0);
        AXI_ARSIZE  : out std_logic_vector(3-1 downto 0);
        AXI_ARBURST : out std_logic_vector(2-1 downto 0);
        AXI_ARPROT  : out std_logic_vector(3-1 downto 0);
        AXI_ARVALID : out std_logic;
        AXI_ARREADY : in  std_logic;
        AXI_RID     : in  std_logic_vector(8-1 downto 0);
        AXI_RDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_RRESP   : in  std_logic_vector(2-1 downto 0);
        AXI_RLAST   : in  std_logic;
        AXI_RVALID  : in  std_logic;
        AXI_RREADY  : out std_logic
    );

end entity;

architecture FULL of MI2AXI4 is

    type fsm_states is (st_idle, st_read, st_read_resp, st_write, st_write_data, st_write_resp);

    signal fsm_pstate  : fsm_states;
    signal fsm_nstate  : fsm_states;
    signal mi_valid    : std_logic;
    signal mi_wr_valid : std_logic;
    signal mi_mask     : std_logic_vector(ADDR_WIDTH-1 downto 0);

begin

    AXI_AWID    <= (others => '0');
    AXI_ARID    <= (others => '0');
    AXI_AWLEN   <= (others => '0');
    AXI_ARLEN   <= (others => '0');
    AXI_AWSIZE  <= "010"; -- 4 byte
    AXI_ARSIZE  <= "010"; -- 4 byte
    AXI_AWPROT  <= (others => '0');
    AXI_ARPROT  <= (others => '0');
    AXI_AWBURST <= (others => '0');
    AXI_ARBURST <= (others => '0');
    AXI_BREADY  <= '1';
    AXI_RREADY  <= '1';

    mi_drd_axi64_g: if AXI_DATA_WIDTH=64 generate
        MI_DRD <= AXI_RDATA(2*MI_DATA_WIDTH-1 downto MI_DATA_WIDTH) when (AXI_ARADDR(2) = '1') else
                  AXI_RDATA(MI_DATA_WIDTH-1 downto 0);
    end generate;

    mi_drd_axi32_g: if AXI_DATA_WIDTH=32 generate
        MI_DRD <= AXI_RDATA(MI_DATA_WIDTH-1 downto 0);
    end generate;

    mi_valid    <= (MI_RD or MI_WR) and MI_ARDY;
    mi_wr_valid <= MI_WR and MI_ARDY;
    mi_mask     <= not (std_logic_vector(to_unsigned((AXI_DATA_WIDTH/8-1), ADDR_WIDTH)));

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (mi_valid = '1') then
                AXI_AWADDR <= MI_ADDR and mi_mask and ADDR_MASK;
                AXI_ARADDR <= MI_ADDR and mi_mask and ADDR_MASK;
            end if;
            if (mi_wr_valid = '1') then
                AXI_WSTRB <= (others => '0');
                AXI_WDATA <= (others => '0');
                if (MI_ADDR(2) = '1' and AXI_DATA_WIDTH=64) then
                    AXI_WSTRB(2*(MI_DATA_WIDTH/8)-1 downto (MI_DATA_WIDTH/8)) <= MI_BE;
                    AXI_WDATA(2*MI_DATA_WIDTH-1 downto MI_DATA_WIDTH)         <= MI_DWR;
                else
                    AXI_WSTRB((MI_DATA_WIDTH/8)-1 downto 0) <= MI_BE;
                    AXI_WDATA(MI_DATA_WIDTH-1 downto 0)     <= MI_DWR;
                end if;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                fsm_pstate <= st_idle;
            else
                fsm_pstate <= fsm_nstate;
            end if;
        end if;
    end process;

    process (all)
    begin
        fsm_nstate  <= fsm_pstate;
        MI_ARDY     <= '0';
        MI_DRDY     <= '0';
        AXI_AWVALID <= '0';
        AXI_WVALID  <= '0';
        AXI_ARVALID <= '0';

        case (fsm_pstate) is
            when st_idle =>
                MI_ARDY <= '1';
                if (MI_WR = '1') then
                    fsm_nstate <= st_write;
                elsif (MI_RD = '1') then
                    fsm_nstate <= st_read;
                end if;

            when st_write =>
                AXI_AWVALID <= '1';
                if (AXI_AWREADY = '1') then
                    fsm_nstate <= st_write_data;
                end if;

            when st_write_data =>
                AXI_WVALID <= '1';
                if (AXI_WREADY = '1') then
                    fsm_nstate <= st_write_resp;
                end if;

            when st_write_resp =>
                if (AXI_BVALID = '1') then
                    fsm_nstate <= st_idle;
                end if;

            when st_read =>
                AXI_ARVALID <= '1';
                if (AXI_ARREADY = '1') then
                    fsm_nstate <= st_read_resp;
                end if;

            when st_read_resp =>
                if (AXI_RVALID = '1') then
                    MI_DRDY    <= '1';
                    fsm_nstate <= st_idle;
                end if;

            when others =>
                fsm_nstate <= st_idle;

        end case;
    end process;

end architecture;
