-- sdp_bram.vhd: Simple Dual Port Block RAM
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity SDP_BRAM is
    Generic (
        -- Data word width in bits. If BLOCK_ENABLE is True then DATA_WIDTH must
        -- be N*BLOCK_WIDTH.
        DATA_WIDTH     : integer := 64;
        -- Depth of BRAM in number of the data words.
        ITEMS          : integer := 512;
        -- Enable masking of WR_DATA signal per BLOCK_WIDTH.
        BLOCK_ENABLE   : boolean := False;
        -- Width of one data block. Allowed values are 8 or 9. The parameter is
        -- ignored when BLOCK_ENABLE=False.
        BLOCK_WIDTH    : natural := 8;
        -- Designate whether read port and write port are clocked with a common
        -- clock or with independent clocks. Possible values:
        --
        -- * True = clock write port and read port with WR_CLK
        -- * False = clock write port with WR_CLK and read port with RD_CLK
        COMMON_CLOCK   : boolean := True;
        -- Output directly from BRAM or throw register (better timing).
        OUTPUT_REG     : boolean := True;
        -- Width of read metadata signal
        METADATA_WIDTH : integer := 0;
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        --
        -- * "7SERIES"
        -- * "ULTRASCALE"
        -- * "STRATIX10"
        -- * "ARRIA10"
        -- * "AGILEX"
        DEVICE         : string := "ULTRASCALE"
    );
    Port (
        -- =====================================================================
        --  WRITE PORT
        -- =====================================================================
        -- Clock signal for write port. Also clock signal for read port when
        -- parameter COMMON_CLOCK = True.
        WR_CLK      : in  std_logic;
        -- Reset signal synchronous with WR_CLK. Used only when parameter
        -- COMMON_CLOCK = True for resetting valid bit of read data.
        WR_RST      : in  std_logic;
        -- Enable of write port.
        WR_EN       : in  std_logic;
        -- Block enable of written data, used only when BLOCK_ENABLE = True.
        WR_BE       : in  std_logic_vector(max((DATA_WIDTH/BLOCK_WIDTH),1)-1 downto 0);
        -- Write address.
        WR_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        -- Write data input.
        WR_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);

        -- =====================================================================
        -- READ PORT
        -- =====================================================================
        -- Clock signal for read port when parameter COMMON_CLOCK = False.
        -- Unused when COMMON_CLOCK = True.
        RD_CLK      : in  std_logic;
        -- Reset signal synchronous with RD_CLK. Used only when parameter
        -- COMMON_CLOCK = False for resetting valid bit of read data.
        RD_RST      : in  std_logic;
        -- Read enable signal, it is only used to generate RD_DATA_VLD.
        RD_EN       : in  std_logic;
        -- Clock enable of read port.
        RD_PIPE_EN  : in  std_logic;
        -- Metadata propagated when RD_PIPE_EN=='1' (valid on RD_EN)
        RD_META_IN  : in  std_logic_vector(METADATA_WIDTH-1 downto 0) := (others => '0');
        -- Read address.
        RD_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        -- Read data output.
        RD_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Metadata propagated when RD_PIPE_EN=='1' (valid on RD_DATA_VLD)
        RD_META_OUT : out std_logic_vector(METADATA_WIDTH-1 downto 0);
        -- Valid bit of output read data.
        RD_DATA_VLD : out std_logic
    );
end entity;

architecture FULL of SDP_BRAM is

    constant ADDR_WIDTH : natural := log2(ITEMS);

    signal rd_en_reg           : std_logic;
    signal rd_meta_reg         : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal rd_clk_internal     : std_logic;
    signal rd_rst_internal     : std_logic;
    signal rd_en_internal      : std_logic;
    signal rd_pipe_en_internal : std_logic;
    signal rd_meta_internal    : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal rd_addr_internal    : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal rd_data_internal    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal wr_clk_internal     : std_logic;
    signal wr_en_internal      : std_logic;
    signal wr_be_internal      : std_logic_vector(DATA_WIDTH/BLOCK_WIDTH-1 downto 0);
    signal wr_addr_internal    : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal wr_data_internal    : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

    assert ((DEVICE = "STRATIX10") or (DEVICE = "ARRIA10") or (DEVICE = "AGILEX") or (DEVICE = "7SERIES") or (DEVICE = "ULTRASCALE") or (DEVICE = "SIM"))
        report "SDP_BRAM: Illegal value of parameter DEVICE '" & DEVICE & "'; allowed devices are: SIM, 7SERIES, ULTRASCALE, STRATIX10, ARRIA10, AGILEX!"
        severity failure;

        assert (not  BLOCK_ENABLE or (BLOCK_ENABLE and ((BLOCK_WIDTH = 8) or (BLOCK_WIDTH = 9))))
        report "SDP_BRAM: Illegal value of BLOCK_WIDTH parameter, allowed values are: 8, 9!"
        severity failure;

    assert (not BLOCK_ENABLE or (BLOCK_ENABLE and (DATA_WIDTH mod BLOCK_WIDTH = 0)))
        report "SDP_BRAM: Illegal value of DATA_WIDTH parameter, when BLOCK_ENABLE is True, DATA_WIDTH parameter must be N*BLOCK_WIDTH!"
        severity failure;

    intel_g : if (DEVICE = "STRATIX10") or (DEVICE = "ARRIA10") or (DEVICE = "AGILEX") generate
        core_i : entity work.SDP_BRAM_INTEL
        generic map (
            DATA_WIDTH     => DATA_WIDTH,
            ITEMS          => ITEMS,
            BLOCK_ENABLE   => BLOCK_ENABLE,
            BLOCK_WIDTH    => BLOCK_WIDTH,
            COMMON_CLOCK   => COMMON_CLOCK,
            OUTPUT_REG     => OUTPUT_REG,
            DEVICE         => DEVICE
        )
        port map (
            WR_CLK      => WR_CLK,
            WR_RST      => WR_RST,
            WR_EN       => WR_EN,
            WR_BE       => WR_BE,
            WR_ADDR     => WR_ADDR,
            WR_DATA     => WR_DATA,
            RD_CLK      => RD_CLK,
            RD_RST      => RD_RST,
            RD_PIPE_EN  => RD_PIPE_EN,
            RD_ADDR     => RD_ADDR,
            RD_DATA     => RD_DATA
        );
    end generate;

    xilinx_g : if (DEVICE = "7SERIES") or (DEVICE = "ULTRASCALE") generate
        core_i : entity work.SDP_BRAM_XILINX2
        generic map (
            DATA_WIDTH     => DATA_WIDTH,
            ITEMS          => ITEMS,
            BLOCK_ENABLE   => BLOCK_ENABLE,
            BLOCK_WIDTH    => BLOCK_WIDTH,
            COMMON_CLOCK   => COMMON_CLOCK,
            OUTPUT_REG     => OUTPUT_REG,
            DEVICE         => DEVICE
        )
        port map (
            WR_CLK      => WR_CLK,
            WR_RST      => WR_RST,
            WR_EN       => WR_EN,
            WR_BE       => WR_BE,
            WR_ADDR     => WR_ADDR,
            WR_DATA     => WR_DATA,
            RD_CLK      => RD_CLK,
            RD_RST      => RD_RST,
            RD_PIPE_EN  => RD_PIPE_EN,
            RD_ADDR     => RD_ADDR,
            RD_DATA     => RD_DATA
        );
    end generate;

    ----------------------------------------------------------------------------
    -- CLOCKS AND SIGNALS
    ----------------------------------------------------------------------------

    rd_clk_internal_g : if COMMON_CLOCK generate
        rd_clk_internal <= WR_CLK;
        rd_rst_internal <= WR_RST;
    else generate
        rd_clk_internal <= RD_CLK;
        rd_rst_internal <= RD_RST;
    end generate;
    wr_clk_internal <= WR_CLK;

    -- needed to synchronise signal assign delay with clocks in ModelSim
    rd_en_internal      <= RD_EN;
    rd_pipe_en_internal <= RD_PIPE_EN;
    rd_meta_internal    <= RD_META_IN;
    rd_addr_internal    <= RD_ADDR;
    wr_en_internal      <= WR_EN;
    wr_addr_internal    <= WR_ADDR;
    wr_data_internal    <= WR_DATA;

    be_g : if BLOCK_ENABLE generate
        wr_be_internal <= WR_BE;
    else generate
        wr_be_internal <= (others => '1');
    end generate;


    ----------------------------------------------------------------------------
    -- SIM MODEL
    ----------------------------------------------------------------------------

    behav_g : if (DEVICE = "SIM") generate
        be_g : if BLOCK_ENABLE generate
            signal wr_data_arr_internal: slv_array_t(DATA_WIDTH/BLOCK_WIDTH-1 downto 0)(BLOCK_WIDTH-1 downto 0);
            signal data_internal : slv_array_2d_t(ITEMS-1 downto 0)(DATA_WIDTH/BLOCK_WIDTH-1 downto 0)(BLOCK_WIDTH-1 downto 0);
        begin
            wr_data_arr_internal <= slv_array_deser(wr_data_internal,DATA_WIDTH/BLOCK_WIDTH);

            wr_p : process (wr_clk_internal)
            begin
                if (rising_edge(wr_clk_internal)) then
                    if (wr_en_internal='1') then
                        for i in 0 to DATA_WIDTH/BLOCK_WIDTH-1 loop
                            if (wr_be_internal(i)='1') then
                                data_internal(to_integer(unsigned(wr_addr_internal)))(i) <= wr_data_arr_internal(i);
                            end if;
                        end loop;
                    end if;
                end if;
            end process;

            rd_p : process (rd_clk_internal)
            begin
                if (rising_edge(rd_clk_internal)) then
                    if (rd_pipe_en_internal = '1') then
                        rd_data_internal <= slv_array_ser(data_internal(to_integer(unsigned(rd_addr_internal))));
                    end if;
                end if;
            end process;

            rd_out_reg_on_g : if (OUTPUT_REG = True) generate
                process (rd_clk_internal)
                begin
                    if (rising_edge(rd_clk_internal)) then
                        if (rd_pipe_en_internal = '1') then
                            RD_DATA <= rd_data_internal;
                        end if;
                    end if;
                end process;
            else generate
                RD_DATA <= rd_data_internal;
            end generate;
        else generate
            signal data_internal : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0);
        begin
            wr_p : process (wr_clk_internal)
            begin
                if (rising_edge(wr_clk_internal)) then
                    if (wr_en_internal='1') then
                        data_internal(to_integer(unsigned(wr_addr_internal))) <= wr_data_internal;
                    end if;
                end if;
            end process;

            rd_p : process (rd_clk_internal)
            begin
                if (rising_edge(rd_clk_internal)) then
                    if (rd_pipe_en_internal = '1') then
                        rd_data_internal <= data_internal(to_integer(unsigned(rd_addr_internal)));
                    end if;
                end if;
            end process;

            rd_out_reg_on_g : if (OUTPUT_REG = True) generate
                process (rd_clk_internal)
                begin
                    if (rising_edge(rd_clk_internal)) then
                        if (rd_pipe_en_internal = '1') then
                            RD_DATA <= rd_data_internal;
                        end if;
                    end if;
                end process;
            else generate
                RD_DATA <= rd_data_internal;
            end generate;
        end generate;
    end generate;

    ----------------------------------------------------------------------------
    -- VALID ANd META REGISTERS
    ----------------------------------------------------------------------------

    rd_en_reg_p : process (rd_clk_internal)
    begin
        if (rising_edge(rd_clk_internal)) then
            if (rd_pipe_en_internal = '1') then
                rd_en_reg   <= rd_en_internal;
                rd_meta_reg <= rd_meta_internal;
            end if;

            if (rd_rst_internal = '1') then
                rd_en_reg <= '0';
            end if;
        end if;
    end process;

    out_reg_on_g : if (OUTPUT_REG = True) generate
        process (rd_clk_internal)
        begin
            if (rising_edge(rd_clk_internal)) then
                if (rd_pipe_en_internal = '1') then
                    RD_DATA_VLD <= rd_en_reg;
                    RD_META_OUT <= rd_meta_reg;
                end if;

                if (rd_rst_internal = '1') then
                    RD_DATA_VLD <= '0';
                end if;
            end if;
        end process;
    end generate;

    out_reg_off_g : if (OUTPUT_REG = False) generate
        RD_DATA_VLD <= rd_en_reg;
        RD_META_OUT <= rd_meta_reg;
    end generate;

end architecture;
