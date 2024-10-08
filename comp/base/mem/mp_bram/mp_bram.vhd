-- mp_bram.vhd: Multi-ported BRAM
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Multi-port BRAM. Currently supports only one write port. This will change in future.
-- Amount of read ports is not restricted.
entity MP_BRAM is
    generic (
        -- Data word width in bits. If BLOCK_ENABLE is True then DATA_WIDTH must
        -- be N*BLOCK_WIDTH.
        DATA_WIDTH     : integer := 1;
        -- [1, inf] -> block width
        BLOCK_WIDTH    : integer := 8;
        BLOCK_ENABLE   : boolean := False;
        -- Depth of BRAM in number of the data words.
        ITEMS          : integer := 4096;
        -- Output directly from BRAM or throw register (better timing).
        OUTPUT_REG     : boolean := True;
        -- Amount of write ports, currently supports just 1 write port.
        WRITE_PORTS    : natural := 1;

        -- Amount of read ports. For each read port, BRAM is replicated to provide one
        -- read port.
        READ_PORTS     : natural := 2;

        -- metadata is data which is send with read request
        METADATA_WIDTH : natural := 0;

        -- when this generic is disabled then two port can write to same address in one clock cycle.
        -- Result are going to be undefined. This mean user have to secure there is no write to same
        -- address in same clock.
        -- Port wit lower id is prioritised and write data.
        -- If this generic is true then this architecture desnt support write to same address
        -- in same clock cycle from two ports
        UNDEF_BEHAW_WHEN_WR_TO_SAME_ADDRESS : boolean := True;

        -- If This generic is set to true then Write delay is shorter by bypassing
        -- Normal write delay is two clock cycles. If this generic is set  to true tehn write delay is one clock.
        ONE_CLK_WRITE : boolean := False;

        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        --
        -- * "7SERIES"
        -- * "ULTRASCALE"
        -- * "STRATIX10"
        -- * "ARRIA10"
        -- * "AGILEX"
        DEVICE      : string := "AGILEX"
    );
    port (
        CLK         : in    std_logic;
        RESET       : in    std_logic;

        -- =====================================================================
        --  WRITE PORTS
        -- =====================================================================
        -- Enable of write port.
        WR_EN       : in  std_logic_vector(WRITE_PORTS - 1 downto 0);
        -- Write address.
        WR_ADDR     : in  slv_array_t(WRITE_PORTS - 1 downto 0)(log2(ITEMS)-1 downto 0);
        -- Write data input.
        WR_DATA     : in  slv_array_t(WRITE_PORTS - 1 downto 0)(DATA_WIDTH-1 downto 0);
        -- ENABLE block. you can write only part of data into memory ("0011") => write only down 16 bits
        -- Use work around when  BOCK_WIDTH is zero then width of signal is NULL. (DATA_WIDTH/(DATA_WIDTH +1) == 0)
        WR_BE       : in  slv_array_t(WRITE_PORTS - 1 downto 0)(DATA_WIDTH/tsel(BLOCK_ENABLE, BLOCK_WIDTH, DATA_WIDTH+1)-1 downto 0) := (WRITE_PORTS - 1 downto 0 => (others => '1'));

        -- =====================================================================
        -- READ PORTS
        -- =====================================================================
        -- Read enable signal, it is only used to generate RD_DATA_VLD.
        RD_EN       : in  std_logic_vector(READ_PORTS - 1 downto 0);
        RD_ADDR     : in  slv_array_t(READ_PORTS - 1 downto 0)(log2(ITEMS)-1 downto 0);
        RD_META_IN  : in  slv_array_t(READ_PORTS - 1 downto 0)(METADATA_WIDTH-1 downto 0);
        -- Read data output.
        RD_DATA_VLD : out  std_logic_vector(READ_PORTS - 1 downto 0);
        RD_DATA     : out slv_array_t(READ_PORTS - 1 downto 0)(DATA_WIDTH-1 downto 0);
        RD_META_OUT : out  slv_array_t(READ_PORTS - 1 downto 0)(METADATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of MP_BRAM is

    constant BLOCKS        : natural := DATA_WIDTH/tsel(BLOCK_ENABLE, BLOCK_WIDTH, DATA_WIDTH+1);
    constant ADDR_WIDTH    : natural := log2(ITEMS);

    signal rd_bram_rd_data     : slv_array_2d_t(WRITE_PORTS - 1 downto 0)(READ_PORTS - 1 downto 0)(DATA_WIDTH - 1 downto 0);
    signal wr_bram_rd_data     : slv_array_2d_t(WRITE_PORTS - 1 downto 0)(WRITE_PORTS - 1 downto 0)(DATA_WIDTH - 1 downto 0);
    signal wr_bram_be          : slv_array_t   (WRITE_PORTS - 1 downto 0)(BLOCKS-1 downto 0);

    signal wr_bram_addr    : slv_array_t   (WRITE_PORTS - 1 downto 0)(ADDR_WIDTH - 1 downto 0);
    signal wr_bram_en      : std_logic_vector(WRITE_PORTS - 1 downto 0);
begin

    assert (not (BLOCK_ENABLE and  ONE_CLK_WRITE)) report "this generic cobination should work but it is not TESTED" severity failure;
    assert (not (BLOCK_ENABLE and BLOCK_WIDTH = 0)) report "If BLOCK_ENABLE is set then BLOCK_WIDTH have to be differant from zero" severity failure;

    ports_g : for it in 0 to WRITE_PORTS - 1 generate
        signal wr_bram_rd_en   : std_logic;

        signal port_wr_en           : std_logic;
        signal port_wr_addr         : std_logic_vector(ADDR_WIDTH - 1 downto 0);
        signal port_wr_data         : std_logic_vector(DATA_WIDTH - 1 downto 0);
    begin


        -- =====================================================================
        -- SHOULD WRITE TO SAME ADDRESS HAVE UNDEFINED BEHAVIORAL
        -- =====================================================================
        write_to_same_addr_g : if (not UNDEF_BEHAW_WHEN_WR_TO_SAME_ADDRESS) generate
            process(all)
                variable wr_to_same_addr_from_lower_port : std_logic;
            begin
                wr_to_same_addr_from_lower_port := '0';
                    -- Check if lower port doesnt write to same address
                for jt in 0 to it-1 loop
                    if (wr_bram_addr(it) = wr_bram_addr(jt)) then
                        wr_to_same_addr_from_lower_port := '1';
                    end if;
                end loop;

                 port_wr_en <= wr_bram_en(it) and not wr_to_same_addr_from_lower_port;
            end process;
        else generate
            port_wr_en <= wr_bram_en(it);
        end generate;
        port_wr_addr <= wr_bram_addr(it);

        -- =====================================================================
        -- WRITE BRAMS
        -- =====================================================================
        write_g : for jt in 0 to WRITE_PORTS - 1 generate
            data_g : if (jt /= it) generate
                signal port_wr_be : std_logic_vector(max(BLOCKS, 1) -1 downto 0);
            begin
                port_wr_be <= wr_bram_be(it) when (BLOCK_ENABLE) else (others => '1');
                bram_i : entity work.SDP_BRAM
                generic map (
                    DATA_WIDTH     => DATA_WIDTH,
                    ITEMS          => ITEMS,
                    BLOCK_ENABLE   => BLOCK_ENABLE,
                    BLOCK_WIDTH    => tsel(BLOCK_ENABLE, BLOCK_WIDTH, DATA_WIDTH+1),
                    COMMON_CLOCK   => False,
                    OUTPUT_REG     => False,
                    DEVICE         => DEVICE
                )
                port map (
                    WR_CLK      => CLK,
                    WR_RST      => RESET,
                    WR_EN       => port_wr_en,
                    WR_BE       => port_wr_be,
                    WR_ADDR     => port_wr_addr,
                    WR_DATA     => port_wr_data,

                    RD_CLK      => CLK,
                    RD_RST      => RESET,
                    RD_PIPE_EN  => '1',
                    RD_EN       => '1',
                    RD_ADDR     => WR_ADDR(jt),
                    RD_DATA     => wr_bram_rd_data(it)(jt),
                    RD_META_OUT => open,
                    RD_DATA_VLD => open
                );
            else generate
                process(CLK)
                begin
                    if (rising_edge(CLK)) then
                        wr_bram_rd_data(it)(jt)     <= WR_DATA(it);
                    end if;
                end process;
            end generate;
        end generate;

        process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    wr_bram_en(it)   <= '0';
                else
                    wr_bram_en(it)   <= WR_EN(it);
                end if;
                wr_bram_addr(it) <= WR_ADDR(it);
                wr_bram_be(it)   <= WR_BE(it);
            end if;
        end process;


        xor_p : process(all)
            variable tmp : std_logic_vector(DATA_WIDTH-1 downto 0);
        begin
            tmp := wr_bram_rd_data(0)(it);
            for jt in 1 to WRITE_PORTS-1 loop
                tmp := tmp xor wr_bram_rd_data(jt)(it);
            end loop;

            port_wr_data <= tmp;
        end process;

        -- =====================================================================
        -- READ BRAMS
        -- =====================================================================
        read_g : for jt in 0 to READ_PORTS-1 generate
                signal port_wr_be : std_logic_vector(max(BLOCKS, 1) -1 downto 0);
            begin

            port_wr_be <= wr_bram_be(it) when (BLOCK_ENABLE) else (others => '1');
            bram_i : entity work.SDP_BRAM
            generic map (
                DATA_WIDTH     => DATA_WIDTH,
                ITEMS          => ITEMS,
                BLOCK_ENABLE   => BLOCK_ENABLE,
                BLOCK_WIDTH    => tsel(BLOCK_ENABLE, BLOCK_WIDTH, DATA_WIDTH+1),
                COMMON_CLOCK   => False,
                OUTPUT_REG     => False,
                DEVICE         => DEVICE
            )
            port map (
                WR_CLK      => CLK,
                WR_RST      => RESET,
                WR_EN       => port_wr_en,
                WR_BE       => port_wr_be,
                WR_ADDR     => port_wr_addr,
                WR_DATA     => port_wr_data,

                RD_CLK      => CLK,
                RD_RST      => RESET,
                RD_PIPE_EN  => '1',
                RD_EN       => '1',
                RD_ADDR     => RD_ADDR(jt),
                RD_DATA     => rd_bram_rd_data(it)(jt),
                RD_META_OUT => open,
                RD_DATA_VLD => open
            );
        end generate;
    end generate;


    outpu_read_g : for it in 0 to READ_PORTS-1 generate
        signal output     : std_logic_vector(DATA_WIDTH-1 downto 0);
        signal output_xor : std_logic_vector(DATA_WIDTH-1 downto 0);
        signal write_bypass_data : std_logic_vector(DATA_WIDTH-1 downto 0);
        signal write_bypass_en   : std_logic;
        signal metadata_bypass   : std_logic_vector(METADATA_WIDTH-1 downto 0);
        signal vld_bypass        : std_logic;
    begin

        -- Create output by xor operation
        xor_read : process(all)
            variable tmp : std_logic_vector(DATA_WIDTH-1 downto 0);
        begin
            tmp := rd_bram_rd_data(0)(it);
            for jt in 1 to WRITE_PORTS-1 loop
                tmp := tmp xor rd_bram_rd_data(jt)(it);
            end loop;
            output <= tmp;
        end process;


        --bypassing if ONE_CLK_WRITE is set
        bypass_g : if (ONE_CLK_WRITE) generate
            process(CLK)
                variable be   : std_logic_vector(BLOCKS-1 downto 0);
                variable data : std_logic_vector(DATA_WIDTH-1 downto 0);
                variable en   : std_logic;
            begin
                if (rising_edge(CLK)) then
                    data := (others => '0');
                    en   := '0';
                    be   := (others => '0');

                    for jt in 0 to WRITE_PORTS-1 loop
                        if (wr_bram_en(jt) = '1' and wr_bram_addr(jt) = RD_ADDR(it)) then
                            --Don't worry in that index is original data.
                            data := wr_bram_rd_data(jt)(jt);
                            be   := wr_bram_be(jt);
                            en   := '1';
                        end if;
                    end loop;

                    --if block_width is enabled then pic old data for BE set to zero
                    if (BLOCK_ENABLE) then
                        for jt in 0 to BLOCKS-1 loop
                            if (be(jt) = '1') then
                                write_bypass_data((jt+1)*BLOCK_WIDTH-1 downto jt*BLOCK_WIDTH) <= data((jt+1)*BLOCK_WIDTH-1 downto jt*BLOCK_WIDTH);
                            else
                                write_bypass_data((jt+1)*BLOCK_WIDTH-1 downto jt*BLOCK_WIDTH) <= output((jt+1)*BLOCK_WIDTH-1 downto jt*BLOCK_WIDTH);
                            end if;
                        end loop;
                    else
                        write_bypass_data <= data;
                    end if;
                    write_bypass_en   <= en;
                end if;
            end process;
        else generate
            write_bypass_data <= (others => '0');
            write_bypass_en   <= '0';
        end generate;

        -- Metadata pipeline
        meta_process : process(CLK)
        begin
            if (rising_edge(CLK)) then
                metadata_bypass <= RD_META_IN(it);
            end if;
        end process;

        -- vld pipeline
        vld_process : process(CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    vld_bypass <= '0';
                else
                    vld_bypass <= RD_EN(it);
                end if;
            end if;
        end process;


        -- Create output register if there is set
        output_reg_g : if (OUTPUT_REG) generate
            process(CLK)
            begin
                if (rising_edge(CLK)) then
                    if (write_bypass_en = '1') then
                        RD_DATA(it) <= write_bypass_data;
                    else
                        RD_DATA(it) <= output;
                    end if;
                    RD_META_OUT(it) <= metadata_bypass;

                    if (RESET = '1') then
                        RD_DATA_VLD(it)      <= '0';
                    else
                        RD_DATA_VLD(it)      <= vld_bypass;
                    end if;
                end if;
            end process;
        else generate
            RD_DATA(it) <= output when write_bypass_en = '0' else write_bypass_data;
            RD_META_OUT(it) <= metadata_bypass;
            RD_DATA_VLD(it)      <= vld_bypass;
        end generate;
    end generate;
end architecture;

