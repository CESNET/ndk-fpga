-- versal_fpga_id.vhd : Get Versal DNA from PS and distribute it as FPGA ID
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity VERSAL_FPGA_ID is
    generic (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH : natural := 32;
        -- Address word width in bits 32 or 64
        AXI_ADDR_WIDTH : natural := 32;
        -- Target device
        DEVICE         : string  := "VERSAL"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         : in  std_logic;
        RESET       : in  std_logic;

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    : out std_logic_vector(8-1 downto 0);
        AXI_AWADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        AXI_AWPROT  : out std_logic_vector(3-1 downto 0);
        AXI_AWVALID : out std_logic;
        AXI_AWREADY : in  std_logic;
        AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB   : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_WLAST   : out std_logic;
        AXI_WVALID  : out std_logic;
        AXI_WREADY  : in  std_logic;
        AXI_BID     : in  std_logic_vector(8-1 downto 0);
        AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        AXI_BVALID  : in  std_logic;
        AXI_BREADY  : out std_logic;
        AXI_ARID    : out std_logic_vector(8-1 downto 0);
        AXI_ARADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
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
        AXI_RREADY  : out std_logic;

        -- =====================================================================
        -- FPGA_ID interface
        -- =====================================================================
        FPGA_ID     : out std_logic_vector(127 downto 0);
        FPGA_ID_VLD : out std_logic
    );

end entity;

architecture FULL of VERSAL_FPGA_ID is
    constant DNA_ADDR_BASE : unsigned(31 downto 0) := X"F1250020";

    type fsm_t is (ST_REQ, ST_RESP, ST_DONE);

    signal fsm_pst         : fsm_t;
    signal fsm_nst         : fsm_t;

    signal mi_addr         : std_logic_vector(31 downto 0);
    signal mi_rd           : std_logic;
    signal mi_drd          : std_logic_vector(31 downto 0);
    signal mi_ardy         : std_logic;
    signal mi_drdy         : std_logic;

    signal axi_awaddr_ext  : std_logic_vector(32-1 downto 0);
    signal axi_araddr_ext  : std_logic_vector(32-1 downto 0);

    signal word_cnt        : unsigned(1 downto 0);
    signal word_we         : std_logic;

    signal fpga_id_reg     : std_logic_vector(127 downto 0);
    signal fpga_id_vld_reg : std_logic;
begin
    assert AXI_DATA_WIDTH = 32
        report "VERSAL_FPGA_ID: AXI_DATA_WIDTH generic must be 32. Actual value is: " & natural'image(AXI_DATA_WIDTH)
        severity failure;
    assert AXI_ADDR_WIDTH = 32 or AXI_ADDR_WIDTH = 64
        report "VERSAL_FPGA_ID: AXI_ADDR_WIDTH generic must be 32 or 64. Actual value is: " & natural'image(AXI_ADDR_WIDTH)
        severity failure;

    mi2axi4_i: entity work.MI2AXI4
    generic map (
        -- MI data word width in bits, must be 32
        MI_DATA_WIDTH  => 32,
        -- AXI data word width in bits, 32 or 64
        AXI_DATA_WIDTH => 32,
        -- Address word width in bits
        ADDR_WIDTH     => 32,
        -- Address mask vector
        ADDR_MASK      => (others => '1'),
        -- Target device
        DEVICE         => DEVICE
    )
    port map (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         => CLK,
        RESET       => RESET,

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR     => (others => '0'),
        MI_ADDR    => mi_addr,
        MI_RD      => mi_rd,
        MI_WR      => '0',
        MI_BE      => (others => '1'),
        MI_DRD     => mi_drd,
        MI_ARDY    => mi_ardy,
        MI_DRDY    => mi_drdy,

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    => AXI_AWID,
        AXI_AWADDR  => axi_awaddr_ext,
        AXI_AWLEN   => AXI_AWLEN,
        AXI_AWSIZE  => AXI_AWSIZE,
        AXI_AWBURST => open,
        AXI_AWPROT  => AXI_AWPROT,
        AXI_AWVALID => AXI_AWVALID,
        AXI_AWREADY => AXI_AWREADY,
        AXI_WDATA   => AXI_WDATA,
        AXI_WSTRB   => AXI_WSTRB,
        AXI_WVALID  => AXI_WVALID,
        AXI_WREADY  => AXI_WREADY,
        AXI_BID     => AXI_BID,
        AXI_BRESP   => AXI_BRESP,
        AXI_BVALID  => AXI_BVALID,
        AXI_BREADY  => AXI_BREADY,
        AXI_ARID    => AXI_ARID,
        AXI_ARADDR  => axi_araddr_ext,
        AXI_ARLEN   => AXI_ARLEN,
        AXI_ARSIZE  => AXI_ARSIZE,
        AXI_ARBURST => open,
        AXI_ARPROT  => AXI_ARPROT,
        AXI_ARVALID => AXI_ARVALID,
        AXI_ARREADY => AXI_ARREADY,
        AXI_RID     => AXI_RID,
        AXI_RDATA   => AXI_RDATA,
        AXI_RRESP   => AXI_RRESP,
        AXI_RLAST   => AXI_RLAST,
        AXI_RVALID  => AXI_RVALID,
        AXI_RREADY  => AXI_RREADY
    );

    gen_addr_g: if AXI_ADDR_WIDTH = 64 generate
        AXI_AWADDR <= X"00000000" & axi_awaddr_ext;
        AXI_ARADDR <= X"00000000" & axi_araddr_ext;
    else generate
        AXI_AWADDR <= axi_awaddr_ext;
        AXI_ARADDR <= axi_araddr_ext;
    end generate;

    AXI_AWBURST <= "01";
    AXI_ARBURST <= "01";

    fsm_pst_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                fsm_pst <= ST_REQ;
            else
                fsm_pst <= fsm_nst;
            end if;
        end if;
    end process;

    fsm_nst_p : process (all)
    begin
        fsm_nst <= fsm_pst;

        case fsm_pst is
            when ST_REQ =>
                if (mi_ardy = '1') then
                    if (mi_drdy = '1') then
                        if (word_cnt = 3) then
                            fsm_nst <= ST_DONE;
                        end if;
                    else
                        fsm_nst <= ST_RESP;
                    end if;
                end if;
            when ST_RESP =>
                if (mi_drdy = '1') then
                    if (word_cnt = 3) then
                        fsm_nst <= ST_DONE;
                    else
                        fsm_nst <= ST_REQ;
                    end if;
                end if;
            when ST_DONE =>
        end case;
    end process;

    fsm_out_p : process (all)
    begin
        mi_rd   <= '0';
        word_we <= '0';

        case fsm_pst is
            when ST_REQ =>
                mi_rd   <= '1';
                word_we <= mi_ardy and mi_drdy;
            when ST_RESP =>
                word_we <= mi_drdy;
            when ST_DONE =>
        end case;
    end process;

    mi_addr <= std_logic_vector(DNA_ADDR_BASE + shift_left(resize(word_cnt, DNA_ADDR_BASE'length), 2));

    word_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                word_cnt <= (others => '0');
            elsif (word_we = '1') then
                word_cnt <= word_cnt + 1;
            end if;
        end if;
    end process;

    fpga_id_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                fpga_id_reg     <= (others => '0');
                fpga_id_vld_reg <= '0';
            elsif (word_we = '1') then
                fpga_id_reg(32*to_integer(word_cnt)+31 downto 32*to_integer(word_cnt)) <= mi_drd;
                if (word_cnt = 3) then
                    fpga_id_vld_reg <= '1';
                end if;
            end if;
        end if;
    end process;

    FPGA_ID     <= fpga_id_reg;
    FPGA_ID_VLD <= fpga_id_vld_reg;

    AXI_WLAST <= '1';
end architecture;
