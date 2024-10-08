-- gen_lutram.vhd: Universal LUT-RAM memory
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- README:
-- This component implements universal parameterizable LUTRAM memory.
-- The following table contains some Xilinx distmem modes and corresponding
-- generics settings. Please read all the comments in the entity!

-- +----------------------+--------------------------------------+
-- | Xilinx distmem modes | corresponding generics settings      |
-- +----------------------+--------------------------------------+
-- | Single Port RAM      | RD_PORTS=1, WRITE_USE_RD_ADDR0=True  |
-- | Dual Port RAM        | RD_PORTS=2, WRITE_USE_RD_ADDR0=True  |
-- | Quad Port RAM        | RD_PORTS=4, WRITE_USE_RD_ADDR0=True  |
-- | Octa Port RAM        | RD_PORTS=8, WRITE_USE_RD_ADDR0=True  |
-- | Simple Dual Port RAM | RD_PORTS=1, WRITE_USE_RD_ADDR0=False |
-- +----------------------+--------------------------------------+

entity GEN_LUTRAM is
    generic(
        -- Data word width in bits. Multiples of 20 bits are effective on
        -- Intel FPGAs with MLAB cells.
        DATA_WIDTH         : natural := 16;
        -- LUTRAM depth in words. The effective and recommended values for
        -- the selected FPGAs:
            -- Xilinx Ultrascale(+) = 32, 64
            -- Intel Stratix 10     = 32
        ITEMS              : natural := 32;
        -- Total number of read ports. Minimum value is 1.
        RD_PORTS           : natural := 1;
        -- Read latency in clock cycles. Allowed values are 0 or 1.
        RD_LATENCY         : natural := 1;
        -- If the write port and the first read port can share the address set
        -- to TRUE else set to FALSE. If TRUE, RD_ADDR(log2(ITEMS)-1 downto 0)
        -- is used for writing and some resources can be saved on Xilinx.
        WRITE_USE_RD_ADDR0 : boolean := False;
        -- If you need to read and write to the same address at the same time
        -- set TRUE, if not set FALSE. When is set FALSE, Quartus doesn't
        -- analyze the timing between write and read operation => better timing.
        -- But writing and reading at the same address at the same time can
        -- cause metastability issues! Only for MLAB devices elsewhere,
        -- the parameter is ignored.
        MLAB_CONSTR_RDW_DC : boolean := True;
        -- This parameter allows the correct selection of the LUTRAM
        -- implementation according to the FPGA used. Supported values are:
        -- "7SERIES", "ULTRASCALE", "STRATIX10", "ARRIA10", "AGILEX"
        DEVICE             : string  := "AGILEX"
    );
    port(
        CLK     : in  std_logic;
        WR_EN   : in  std_logic;
        WR_ADDR : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        WR_DATA : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RD_ADDR : in  std_logic_vector(RD_PORTS*log2(ITEMS)-1 downto 0);
        RD_DATA : out std_logic_vector(RD_PORTS*DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of GEN_LUTRAM is

    constant ADDR_WIDTH       : natural := log2(ITEMS);
    constant MLAB_OUTPUT_REG  : boolean := (RD_LATENCY = 1);

    signal lutram_wr_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal lutram_wr_addr     : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal lutram_rd_addr_arr : slv_array_t(RD_PORTS-1 downto 0)(ADDR_WIDTH-1 downto 0);
    signal lutram_out_arr     : slv_array_t(RD_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal lutram_out         : std_logic_vector(RD_PORTS*DATA_WIDTH-1 downto 0);
    signal distmem            : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0) := (others => (others => '0'));

    -- Vivado ramstyle attribute
    attribute ram_style : string;
    attribute ram_style of distmem : signal is "distributed";

    -- Intel ramstyle attribute (for better backward compatibility only)
    attribute ramstyle : string;
    attribute ramstyle of distmem : signal is "MLAB, no_rw_check";

    -- Synplify ramstyle attribute
    attribute syn_ramstyle : string;
    attribute syn_ramstyle of distmem : signal is "select_ram";

begin

    assert RD_LATENCY < 2 report "GEN_LUTRAM doesn't support RD_LATENCY > 1!" severity failure;

    -- deserialization read address vector
    lutram_rd_addr_arr <= slv_array_downto_deser(RD_ADDR,RD_PORTS,ADDR_WIDTH);

    -- select a write address
    lutram_wr_addr_g : if WRITE_USE_RD_ADDR0 generate
        lutram_wr_addr <= lutram_rd_addr_arr(0);
    else generate
        lutram_wr_addr <= WR_ADDR;
    end generate;

    device_g : if ((DEVICE = "ARRIA10" or DEVICE = "STRATIX10" or DEVICE = "AGILEX") and DATA_WIDTH > 0) generate
        mlab_async_g : for i in 0 to RD_PORTS-1 generate
            -- Macro set as async MLAB with/without output register
            sdp_mlab_i : entity work.ALTDPRAM_WRAP
            generic map (
                DATA_WIDTH      => DATA_WIDTH,
                ADDR_WIDTH      => ADDR_WIDTH,
                RAM_TYPE        => "MLAB",
                RDW_CONSTRAINED => MLAB_CONSTR_RDW_DC,
                OUTPUT_REG      => MLAB_OUTPUT_REG,
                DEVICE          => DEVICE
            )
            PORT MAP (
                DATA           => WR_DATA,
                INCLOCK        => CLK,
                RDADDRESS      => lutram_rd_addr_arr(i),
                WRADDRESS      => lutram_wr_addr,
                WREN           => WR_EN,
                Q              => lutram_out_arr(i)
            );

            lutram_out <= slv_array_ser(lutram_out_arr,RD_PORTS,DATA_WIDTH);
            RD_DATA    <= lutram_out;
        end generate;

    else generate
        -- behavioral implementation for all Xilinx devices and others

        distmem_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (WR_EN = '1') then
                    distmem(to_integer(unsigned(lutram_wr_addr))) <= WR_DATA;
                end if;
            end if;
        end process;

        rd_ports_g : for i in 0 to RD_PORTS-1 generate
            lutram_out_arr(i) <= distmem(to_integer(unsigned(lutram_rd_addr_arr(i))));
        end generate;

        lutram_out <= slv_array_ser(lutram_out_arr,RD_PORTS,DATA_WIDTH);

        output_reg_g : if RD_LATENCY > 0 generate
            output_reg_p : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    RD_DATA <= lutram_out;
                end if;
            end process;
        else generate
            RD_DATA <= lutram_out;
        end generate;
    end generate;

end architecture;
