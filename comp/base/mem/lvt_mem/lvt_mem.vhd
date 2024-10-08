-- lvt_mem.vhd: Multi-ported memory using LVT
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Multiported memory implementation inspired by https://dl.acm.org/doi/abs/10.1145/2629629
-- This approach is suitable for shallow memories since it implements smaller
-- true multiported memories using registers. Thus underlying memories are
-- implemented using LUTs (distmem for Xilinx). Also this memory supports read-during write
-- NEW_DATA behaviour. Writes to same address from multiple ports in the same clock cycle
-- result in undefined behaviour.
entity LVT_MEM is
    generic (
        -- Stored data width
        DATA_WIDTH  : natural := 16;
        -- Depth of memory
        ITEMS       : natural := 64;
        -- Amount of read ports
        READ_PORTS  : natural := 2;
        -- Amount of write ports
        WRITE_PORTS : natural := 2;
        -- Read latency - 0 or 1
        RD_LATENCY  : natural := 1;
        -- Read during write behaviour: "NEW_DATA" or "DONT_CARE".
        RDW_BEHAV   : string  := "NEW_DATA";
        -- Underlying memory type: "BRAM" or "LUT".
        -- When using BRAM, RD_LATENCY must be set to 1.
        MEM_TYPE    : string  := "BRAM";
        DEVICE      : string  := "AGILEX"
    );
    port (
        CLK         : in std_logic;
        RESET       : in std_logic;

        WR_EN       : in    std_logic_vector(WRITE_PORTS-1 downto 0);
        WR_ADDR     : in    slv_array_t(WRITE_PORTS-1 downto 0)(log2(ITEMS)-1 downto 0);
        WR_DATA     : in    slv_array_t(WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);

        RD_ADDR     : in    slv_array_t(READ_PORTS-1 downto 0)(log2(ITEMS)-1 downto 0);
        RD_DATA     : out   slv_array_t(READ_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of LVT_MEM is

    constant WR_PORT_IND_W : natural := log2(WRITE_PORTS);
    constant ADDR_W        : natural := log2(ITEMS);

    -- Result of this function is static and is here to improve
    -- readability.
    function wrport_indexes return slv_array_t is
        variable ret    : slv_array_t(WRITE_PORTS-1 downto 0)(WR_PORT_IND_W-1 downto 0);
    begin
        for i in 0 to WRITE_PORTS-1 loop
            ret(i) := std_logic_vector(to_unsigned(i, WR_PORT_IND_W));
        end loop;
        return ret;
    end function;

    constant lvt_wr_data    : slv_array_t(WRITE_PORTS-1 downto 0)(WR_PORT_IND_W-1 downto 0) := wrport_indexes;
    signal lvt_rd_data_arr  : slv_array_t(WRITE_PORTS-1 downto 0)(WR_PORT_IND_W-1 downto 0);
    signal lvt_rd_data      : std_logic_vector(WRITE_PORTS*WR_PORT_IND_W-1 downto 0);

    signal lut_rd_data_arr  : slv_array_2d_t(WRITE_PORTS-1 downto 0)(READ_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
begin

    assert not (MEM_TYPE = "BRAM") or RD_LATENCY = 1
        report "[LVT MEM]: When using BRAM in LVT MEM, one must use read latency of 1!"
        severity error;

    lvt_i: entity work.GEN_REG_ARRAY
    generic map (
        DATA_WIDTH  => WR_PORT_IND_W,
        ITEMS       => ITEMS,
        WR_PORTS    => WRITE_PORTS,
        RD_PORTS    => READ_PORTS,
        RD_LATENCY  => RD_LATENCY,
        OUTPUT_REG  => false,
        DEVICE      => DEVICE
    ) port map (
        CLK         => CLK,
        RESET       => RESET,
        WR_EN       => WR_EN,
        WR_ADDR     => slv_array_ser(WR_ADDR),
        WR_DATA     => slv_array_ser(lvt_wr_data),
        RD_ADDR     => slv_array_ser(RD_ADDR),
        RD_DATA     => lvt_rd_data
    );
    lvt_rd_data_arr <= slv_array_deser(lvt_rd_data, WRITE_PORTS);

    wr_lutram_g : for wr_i in 0 to WRITE_PORTS-1 generate
        signal lut_rd_data  : std_logic_vector(READ_PORTS*DATA_WIDTH-1 downto 0);
    begin
        lut_g : if MEM_TYPE = "LUT" generate
            lut_i : entity work.GEN_LUTRAM
            generic map (
                DATA_WIDTH          => DATA_WIDTH,
                ITEMS               => ITEMS,
                RD_PORTS            => READ_PORTS,
                RD_LATENCY          => RD_LATENCY,
                WRITE_USE_RD_ADDR0  => false,
                MLAB_CONSTR_RDW_DC  => false,
                DEVICE              => DEVICE
            ) port map (
                CLK                 => CLK,
                WR_EN               => WR_EN(wr_i),
                WR_ADDR             => WR_ADDR(wr_i),
                WR_DATA             => WR_DATA(wr_i),
                RD_ADDR             => slv_array_ser(RD_ADDR),
                RD_DATA             => lut_rd_data
            );
            lut_rd_data_arr(wr_i) <= slv_array_deser(lut_rd_data, READ_PORTS);

        else generate
            bram_g : for rd_i in 0 to READ_PORTS-1 generate
                bram_i : entity work.SDP_BRAM
                generic map (
                    DATA_WIDTH      => DATA_WIDTH,
                    ITEMS           => ITEMS,
                    BLOCK_ENABLE    => false,
                    BLOCK_WIDTH     => 8,
                    COMMON_CLOCK    => true,
                    OUTPUT_REG      => false,
                    METADATA_WIDTH  => 0,
                    DEVICE          => DEVICE
                ) port map (
                    WR_CLK          => CLK,
                    WR_RST          => RESET,
                    WR_EN           => WR_EN(wr_i),
                    WR_BE           => (others => '1'),
                    WR_ADDR         => WR_ADDR(wr_i),
                    WR_DATA         => WR_DATA(wr_i),

                    RD_CLK          => CLK,
                    RD_RST          => RESET,
                    RD_EN           => '1',
                    RD_PIPE_EN      => '1',
                    RD_META_IN      => (others => '0'),
                    RD_ADDR         => RD_ADDR(rd_i),
                    RD_DATA         => lut_rd_data_arr(wr_i)(rd_i),
                    RD_META_OUT     => open,
                    RD_DATA_VLD     => open
                );
            end generate;
        end generate;
    end generate;

    rd_mux_g : for rd_i in 0 to READ_PORTS-1 generate
        signal wr_ports_data_arr    : slv_array_t(WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
    begin
        process (all)
        begin
            for wr_i in 0 to WRITE_PORTS-1 loop
                wr_ports_data_arr(wr_i) <= lut_rd_data_arr(wr_i)(rd_i);
            end loop;
        end process;

        rdw_g : if RDW_BEHAV = "NEW_DATA" generate
            signal addr_match_vec   : std_logic_vector(WRITE_PORTS-1 downto 0);
            signal addr_match       : std_logic;

            signal rdw_reg_mvec     : std_logic_vector(WRITE_PORTS-1 downto 0);
            signal rdw_reg_m        : std_logic;
            signal rdw_wr_data      : slv_array_t(WRITE_PORTS-1 downto 0)(DATA_WIDTH-1 downto 0);
            signal rdw_dout         : std_logic_vector(DATA_WIDTH-1 downto 0);
        begin
            -- Check for read during write
            addr_match_g : for wr_i in 0 to WRITE_PORTS-1 generate
                addr_match_vec(wr_i) <= WR_EN(wr_i) when WR_ADDR(wr_i) = RD_ADDR(rd_i) else '0';
            end generate;
            addr_match <= or (addr_match_vec);

            -- Add registers for read port when rd latency is one
            rdw_reg_g : if RD_LATENCY=1 generate
                process (CLK)
                begin
                    if rising_edge(CLK) then
                        rdw_wr_data     <= WR_DATA;
                        rdw_reg_mvec    <= addr_match_vec;
                        rdw_reg_m       <= addr_match;
                    end if;
                end process;
            else generate
                rdw_wr_data     <= WR_DATA;
                rdw_reg_mvec    <= addr_match_vec;
                rdw_reg_m       <= addr_match;
            end generate;

            -- Select matching data
            mux_i : entity work.GEN_MUX_ONEHOT
            generic map (
                DATA_WIDTH  => DATA_WIDTH,
                MUX_WIDTH   => WRITE_PORTS,
                DEVICE      => DEVICE
            ) port map (
                DATA_IN     => slv_array_ser(rdw_wr_data),
                SEL         => rdw_reg_mvec,
                DATA_OUT    => rdw_dout
            );

            -- Select memory with "live" value when no port is writing to the same address,
            -- otherwise select forwarded value
            RD_DATA(rd_i) <= wr_ports_data_arr(to_integer(unsigned(lvt_rd_data_arr(rd_i)))) when rdw_reg_m = '0' else rdw_dout;
        else generate
            RD_DATA(rd_i) <= wr_ports_data_arr(to_integer(unsigned(lvt_rd_data_arr(rd_i))));
        end generate;
    end generate;


end architecture;
