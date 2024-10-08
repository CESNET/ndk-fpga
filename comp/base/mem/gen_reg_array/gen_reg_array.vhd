-- gen_reg_array.vhd: Universal register array
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity GEN_REG_ARRAY is
    generic(
        -- Width of word (item) in bits. Only low width (1 to 8) is effective!!!
        -- If you need a larger data width, this component is not suitable.
        DATA_WIDTH         : natural := 1;
        -- Number of items.
        ITEMS              : natural := 256;
        -- Number of write ports. The first active port from LSB has priority.
        WR_PORTS           : natural := 2;
        -- Number of read ports.
        RD_PORTS           : natural := 4;
        -- Read latency in clock cycles.
        RD_LATENCY         : natural := 1;
        -- Enable of output register, active increases read latency by 1.
        OUTPUT_REG         : boolean := False;
        -- This parameter is not currently used.
        DEVICE             : string  := "ULTRASCALE"
    );
    port(
        CLK     : in  std_logic;
        -- If you do not need to reset the registry array, connect to '0'!
        RESET   : in  std_logic;
        WR_EN   : in  std_logic_vector(WR_PORTS-1 downto 0);
        WR_ADDR : in  std_logic_vector(WR_PORTS*log2(ITEMS)-1 downto 0);
        WR_DATA : in  std_logic_vector(WR_PORTS*DATA_WIDTH-1 downto 0);
        RD_ADDR : in  std_logic_vector(RD_PORTS*log2(ITEMS)-1 downto 0);
        RD_DATA : out std_logic_vector(RD_PORTS*DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of GEN_REG_ARRAY is

    constant ADDR_WIDTH : natural := log2(ITEMS);

    signal item_we_per_port       : slv_array_t(WR_PORTS-1 downto 0)(ITEMS-1 downto 0);
    signal port_we_per_item       : slv_array_t(ITEMS-1 downto 0)(WR_PORTS-1 downto 0);
    signal port_we_first_per_item : slv_array_t(ITEMS-1 downto 0)(WR_PORTS-1 downto 0);
    signal port_we_sel_per_item   : slv_array_t(ITEMS-1 downto 0)(log2(WR_PORTS)-1 downto 0);
    signal reg_mem_we             : std_logic_vector(ITEMS-1 downto 0);
    signal reg_mem_in             : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal reg_mem                : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0) := (others => (others => '0'));

begin

    wr_port_g : for i in 0 to WR_PORTS-1 generate
        item_we_per_port_i : entity work.DEC1FN_ENABLE
        generic map (
            ITEMS => ITEMS
        )
        port map (
            ENABLE => WR_EN(i),
            ADDR   => WR_ADDR((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH),
            DO     => item_we_per_port(i)
        );

        port_we_per_item_g : for j in 0 to ITEMS-1 generate
            port_we_per_item(j)(i) <= item_we_per_port(i)(j);
        end generate;
    end generate;

    reg_mem_g : for i in 0 to ITEMS-1 generate
        port_we_first_per_item_i : entity work.FIRST_ONE
        generic map (
            DATA_WIDTH => WR_PORTS
        )
        port map (
            DI => port_we_per_item(i),
            DO => port_we_first_per_item(i)
        );

        port_we_sel_per_item_i : entity work.DEC1FN2B
        generic map (
            ITEMS => WR_PORTS
        )
        port map (
            DI     => port_we_first_per_item(i),
            ENABLE => '1',
            ADDR   => port_we_sel_per_item(i)
        );

        reg_mem_in_mux_i : entity work.GEN_MUX_PIPED
        generic map(
            DATA_WIDTH     => DATA_WIDTH,
            MUX_WIDTH      => WR_PORTS,
            MUX_LATENCY    => 0,
            INPUT_REG      => False,
            OUTPUT_REG     => False
        )
        port map(
            CLK     => CLK,
            RESET   => '0',
            RX_DATA => WR_DATA,
            RX_SEL  => port_we_sel_per_item(i),
            TX_DATA => reg_mem_in(i)
        );

        reg_mem_we(i) <= or port_we_per_item(i);

        reg_mem_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    reg_mem(i) <= (others => '0');
                elsif (reg_mem_we(i) = '1') then
                    reg_mem(i) <= reg_mem_in(i);
                end if;
            end if;
        end process;
    end generate;

    rd_ports_g : for i in 0 to RD_PORTS-1 generate
        rd_port_mux_i : entity work.GEN_MUX_PIPED
        generic map(
            DATA_WIDTH     => DATA_WIDTH,
            MUX_WIDTH      => ITEMS,
            MUX_LATENCY    => RD_LATENCY,
            INPUT_REG      => False,
            OUTPUT_REG     => OUTPUT_REG
        )
        port map(
            CLK     => CLK,
            RESET   => '0',
            RX_DATA => slv_array_ser(reg_mem, ITEMS, DATA_WIDTH),
            RX_SEL  => RD_ADDR((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH),
            TX_DATA => RD_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
        );
    end generate;

end architecture;
