-- mi_splitter_plus_gen.vhd: Splitter for MI with generically configurable number of output ports
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.ab_init_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- This is another splitter for the MI bus. MI transactions are routed out
-- of a certain port, depending on how the splitter is set and on the
-- transaction's address.
--
-- The most significant advantage of this splitter is the possibility for
-- the user to choose the number of output ports, and for each output port
-- a range (or ranges) of addresses that are routed to (and out of)
-- this port. These address ranges are specified by Address Bases (ABs),
-- which are contained in generic ADDR_BASE.
--
-- There can be more ABs than there is output ports, which means that more
-- than one AB can be assigned to a single output port. It doesn't work the
-- other way around though.
entity MI_SPLITTER_PLUS_GEN is
    generic(
        -- Width of MI address.
        ADDR_WIDTH    : integer := 32;
        -- Width of MI data.
        DATA_WIDTH    : integer := 32;
        -- Width of MI meta.
        META_WIDTH    : integer := 2;
        -- Number of output ports.
        PORTS         : integer := 8;
        -- Output pipeline.
        PIPE_OUT      : b_array_t(PORTS-1 downto 0) := (others => true);
        -- Output pipelines type (see entity of PIPE).
        PIPE_TYPE     : string := "SHREG";
        -- Output pipelines output register enable.
        -- Only for PIPE_TYPE = "SHREG"!
        PIPE_OUTREG   : boolean := false;
        -- Number of considered address bases (might be higher or equal to PORTS).
        ADDR_BASES    : integer := PORTS;
        -- Bases of address spaces (base 0 is 0x00000000).
        -- Default: Random Bases.
        -- CAUTION: ModelSim doesn't likes directly specified value for slv_array_t generics. Assign predefined constant to this generic.
        ADDR_BASE     : slv_array_t(ADDR_BASES-1 downto 0)(ADDR_WIDTH-1 downto 0) := init_addr_base_downto(ADDR_BASES, ADDR_WIDTH);
        -- Bits of address that are needed to determine output port.
        -- The chain of '1's must be continuous -> no '0's in-between!
        -- Default: OR combination of all Address Bases with any '0's between the '1's replaced by '1's.
        ADDR_MASK     : std_logic_vector(ADDR_WIDTH-1 downto 0) := init_addr_mask_downto(ADDR_BASE, ADDR_WIDTH);
        -- How Address Bases are mapped to ports.
        -- Constains target port index for each Address Base.
        -- Multiple Address Bases might target the same port.
        -- Default: Each Address Base is mapped to the Port on the same index (expects ADDR_BASES = PORTS).
        PORT_MAPPING  : i_array_t(ADDR_BASES-1 downto 0) := init_port_mapping_downto(ADDR_BASES, PORTS);
        -- Target FPGA.
        DEVICE        : string  := "STRATIX10"
    );
    port(
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================

        CLK     : in std_logic;
        RESET   : in std_logic;

        -- =====================================================================
        -- Input MI interface
        -- =====================================================================

        RX_DWR  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_MWR  : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
        RX_ADDR : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        RX_BE   : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
        RX_RD   : in  std_logic;
        RX_WR   : in  std_logic;
        RX_ARDY : out std_logic;
        RX_DRD  : out std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_DRDY : out std_logic;

        -- =====================================================================
        -- Output MI interfaces
        -- =====================================================================

        TX_DWR  : out slv_array_t     (PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_MWR  : out slv_array_t     (PORTS-1 downto 0)(META_WIDTH-1 downto 0);
        TX_ADDR : out slv_array_t     (PORTS-1 downto 0)(ADDR_WIDTH-1 downto 0);
        TX_BE   : out slv_array_t     (PORTS-1 downto 0)(DATA_WIDTH/8-1 downto 0);
        TX_RD   : out std_logic_vector(PORTS-1 downto 0);
        TX_WR   : out std_logic_vector(PORTS-1 downto 0);
        TX_ARDY : in  std_logic_vector(PORTS-1 downto 0);
        TX_DRD  : in  slv_array_t     (PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_DRDY : in  std_logic_vector(PORTS-1 downto 0)
    );
end entity;

architecture FULL of MI_SPLITTER_PLUS_GEN is

    -- ========================================================================
    --                                FUNCTIONS
    -- ========================================================================
    function port_resolution(address : std_logic_vector) return natural is
        variable p : natural := 0;
    begin
        for i in 0 to ADDR_BASES-1 loop
            if ((address and ADDR_MASK) >= (ADDR_BASE(i) and ADDR_MASK)) then
                p := PORT_MAPPING(i);
            end if;
        end loop;
        return p;
    end function;

    function ab_in_order return boolean is
    begin
        for i in ADDR_BASES-1 downto 1 loop
            if ((ADDR_BASE(i) and ADDR_MASK) <= (ADDR_BASE(i-1) and ADDR_MASK)) then
                return false;
            end if;
        end loop;
        return true;
    end function;

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================
    signal current_port      : natural;
    -- MI signals in pipe
    signal dwr_in_pipe       : slv_array_t(PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal mwr_in_pipe       : slv_array_t(PORTS-1 downto 0)(META_WIDTH-1 downto 0);
    signal addr_in_pipe      : slv_array_t(PORTS-1 downto 0)(ADDR_WIDTH-1 downto 0);
    signal be_in_pipe        : slv_array_t(PORTS-1 downto 0)(DATA_WIDTH/8-1 downto 0);
    signal wr_in_pipe        : std_logic_vector(PORTS-1 downto 0);
    signal rd_in_pipe        : std_logic_vector(PORTS-1 downto 0);
    signal ardy_in_pipe      : std_logic_vector(PORTS-1 downto 0);
    signal drd_in_pipe       : slv_array_t(PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal drdy_in_pipe      : std_logic_vector(PORTS-1 downto 0);
    -- state signals for FSM
    type state is (run, hold);
    signal present_st        : state := run;
    signal next_st           : state := run;
    -- control logic signals
    signal rd_resp_immediate : std_logic; -- immediate response to read request
    signal rd_resp_overdue   : std_logic; -- overdue response to read request
    signal ardy_rd           : std_logic;
    signal ardy_wr           : std_logic;
    signal ardy_in_pipe_dly  : std_logic;

begin

    assert ((or ADDR_BASE(0)) = '0') report "The lowest base address must be 0."    severity failure;
    assert (ab_in_order = true)      report "Portbases must be in ascending order!" severity failure;

    -- assigning the port number to a signal for easier usage and debugging
    current_port <= port_resolution(RX_ADDR);

    -- ========================================================================
    -- routing transactions
    -- ========================================================================
    address_resolution_p : process (all)
    begin
        wr_in_pipe   <= (others => '0');
        dwr_in_pipe  <= (others => (others => '0'));
        mwr_in_pipe  <= (others => (others => '0'));
        addr_in_pipe <= (others => (others => '0'));
        be_in_pipe   <= (others => (others => '0'));

        dwr_in_pipe(current_port)  <= RX_DWR;
        mwr_in_pipe(current_port)  <= RX_MWR;
        addr_in_pipe(current_port) <= RX_ADDR;
        be_in_pipe(current_port)   <= RX_BE;
        wr_in_pipe(current_port)   <= RX_WR;

        RX_DRD  <= drd_in_pipe(current_port);
        RX_DRDY <= drdy_in_pipe(current_port);

    end process;

    -- ========================================================================
    -- FSM for rd_in_pipe
    -- ========================================================================
    -- present state
    present_state_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            present_st <= next_st;
            if (RESET = '1') then
                present_st <= run;
            end if;
        end if;
    end process;

    -- next state
    next_state_p : process (all)
    begin
        case present_st is

            when run =>
                if ((RX_RD = '1') and (ardy_in_pipe(current_port) = '1') and (drdy_in_pipe(current_port) = '0')) then
                    next_st <= hold;
                else
                    next_st <= run;
                end if;

            when hold =>
                if ((RX_RD = '1') and (ardy_in_pipe(current_port) = '0') and (drdy_in_pipe(current_port) = '1')) then
                    next_st <= run;
                else
                    next_st <= hold;
                end if;

            when others =>
                next_st <= run;

        end case;
    end process;

    output_logic_p : process (all)
    begin
        -- default values of FSM
        rd_in_pipe <= (others => '0');

        case present_st is
            when run =>
                rd_in_pipe(current_port) <= RX_RD;
            when hold =>
                rd_in_pipe(current_port) <= '0';
        end case;
    end process;

    -- ========================================================================
    -- ARDY
    -- ========================================================================
    rd_resp_immediate <= '1' when ((ardy_in_pipe(current_port) = '1') and (drdy_in_pipe(current_port) = '1')) else '0';
    rd_resp_overdue   <= '1' when ((ardy_in_pipe_dly = '1')           and (drdy_in_pipe(current_port) = '1')) else '0';

    ardy_rd <= '1' when ((RX_RD = '1') and ((rd_resp_immediate = '1') or (rd_resp_overdue = '1'))) else '0';
    ardy_wr <= '1' when ((RX_WR = '1') and (ardy_in_pipe(current_port) = '1'))                     else '0';

    RX_ARDY <= '1' when (ardy_wr = '1') or (ardy_rd = '1') else '0';

    ardy_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((RX_RD = '1') and (ardy_in_pipe(current_port) = '1') and (drdy_in_pipe(current_port) = '0')) then
                ardy_in_pipe_dly <= ardy_in_pipe(current_port);
            end if;
            if ((RESET = '1') or ((RX_RD = '1') and (RX_ARDY = '1') and (RX_DRDY = '1'))) then
                ardy_in_pipe_dly <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Output pipes
    -- ========================================================================
    output_pipes_g : for i in PORTS-1 downto 0 generate
        pipe_i: entity work.MI_PIPE
        generic map(
            DATA_WIDTH => DATA_WIDTH,
            ADDR_WIDTH => ADDR_WIDTH,
            META_WIDTH => META_WIDTH,
            PIPE_TYPE  => PIPE_TYPE,
            USE_OUTREG => PIPE_OUTREG,
            FAKE_PIPE  => not PIPE_OUT(i),
            DEVICE     => DEVICE
        )
        port map(
            CLK       => CLK,
            RESET     => RESET,

            IN_DWR    => dwr_in_pipe(i),
            IN_MWR    => mwr_in_pipe(i),
            IN_ADDR   => addr_in_pipe(i),
            IN_BE     => be_in_pipe(i),
            IN_WR     => wr_in_pipe(i),
            IN_RD     => rd_in_pipe(i),
            IN_ARDY   => ardy_in_pipe(i),
            IN_DRD    => drd_in_pipe(i),
            IN_DRDY   => drdy_in_pipe(i),

            OUT_DWR   => TX_DWR(i),
            OUT_MWR   => TX_MWR(i),
            OUT_ADDR  => TX_ADDR(i),
            OUT_BE    => TX_BE(i),
            OUT_WR    => TX_WR(i),
            OUT_RD    => TX_RD(i),
            OUT_ARDY  => TX_ARDY(i),
            OUT_DRD   => TX_DRD(i),
            OUT_DRDY  => TX_DRDY(i)
        );
    end generate;

end architecture;
