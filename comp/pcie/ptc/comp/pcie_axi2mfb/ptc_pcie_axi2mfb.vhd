-- ptc_pcie_axi2mfb.vhd: PCIe AXI to MFB interface convertor
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------
--
--

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity PTC_PCIE_AXI2MFB is
    generic (
        -- =======================================================================
        -- Target device specification
        -- =======================================================================
        -- Supported devices: "7SERIES", "ULTRASCALE"
        DEVICE           : string  := "ULTRASCALE";
        -- =======================================================================
        -- MFB BUS CONFIGURATION:
        -- =======================================================================
        -- Supported configuration is MFB(4,1,4,32) for PCIe on UltraScale+
        -- Supported configuration is MFB(2,1,4,32) for PCIe on Virtex 7 Series
        MFB_REGIONS      : natural := 4;
        MFB_REG_SIZE     : natural := 1;
        MFB_BLOCK_SIZE   : natural := 4;
        MFB_ITEM_WIDTH   : natural := 32;
        -- =======================================================================
        -- AXI BUS CONFIGURATION:
        -- =======================================================================
        -- DATA=512, RC=161 for Gen3x16 PCIe (Virtex UltraScale+) - with straddling!
        -- DATA=256, RC=70  for Gen3x16 PCIe (Virtex 7 Series) - with straddling!
        AXI_DATA_WIDTH   : natural := 512;
        AXI_RCUSER_WIDTH : natural := 161

    -- UltraScale+ RC user:
    -- (
    -- MFB_REGOINS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH/8   -- parity (don't care)
    -- 1                                                          -- disctontinue (error) (don't care)
    -- log2(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE)*MFB_REGIONS  -- EOP_POS
    -- MFB_REGIONS                                                -- EOP
    -- log2(MFB_REGIONS*MFB_REG_SIZE)*MFB_REGIONS                 -- SOP_POS
    -- MFB_REGIONS                                                -- SOP
    -- (MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8 -- Byte Enable
    -- -1 downto 0)

    -- Virtex 7 Series RC user:
    -- (
    -- MFB_REGOINS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH/8      -- parity (don't care)
    -- 1                                                             -- discontinue (error) (don't care)
    -- (log2(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE)+1)*MFB_REGIONS -- (EOP_POS & EOP) * MFB_REGIONS
    -- MFB_REGIONS                                                   -- SOP
    -- (MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8    -- Byte Enable
    -- -1 downto 0)
    );
    port (
        ---------------------------------------------------------------------------
        -- Common interfaces
        ---------------------------------------------------------------------------
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        ---------------------------------------------------------------------------
        -- RX AXI interface from PCIe Endpoint
        ---------------------------------------------------------------------------

        RX_AXI_TDATA     : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_AXI_TUSER     : in  std_logic_vector(AXI_RCUSER_WIDTH-1 downto 0);
        RX_AXI_TVALID    : in  std_logic; -- SRC_RDY
        RX_AXI_TREADY    : out std_logic; -- always '1'

        ---------------------------------------------------------------------------
        -- TX MFB interface
        ---------------------------------------------------------------------------

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture FULL of PTC_PCIE_AXI2MFB is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    constant SOP_POS_WIDTH     : integer := log2(MFB_REGIONS*MFB_REG_SIZE);
    constant EOP_POS_WIDTH     : integer := log2(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE);
    constant BE_WIDTH          : integer := (MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8;

    constant SOF_POS_WIDTH     : integer := log2(MFB_REG_SIZE);
    constant EOF_POS_WIDTH     : integer := log2(MFB_REG_SIZE*MFB_BLOCK_SIZE);

    constant SOF_POS_TRUE_WIDTH     : integer := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_TRUE_WIDTH     : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    -- RX AXI TUSER division
    signal rx_axi_sop_pos : slv_array_t(MFB_REGIONS-1 downto 0)(SOP_POS_WIDTH-1 downto 0);
    signal rx_axi_eop_pos : slv_array_t(MFB_REGIONS-1 downto 0)(EOP_POS_WIDTH-1 downto 0);
    signal rx_axi_sop     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_axi_eop     : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal rx_axi_sop_pos_top : slv_array_t(MFB_REGIONS-1 downto 0)(SOP_POS_WIDTH-SOF_POS_WIDTH-1 downto 0);
    signal rx_axi_sop_pos_bot : slv_array_t(MFB_REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);

    signal rx_axi_eop_pos_top : slv_array_t(MFB_REGIONS-1 downto 0)(EOP_POS_WIDTH-EOF_POS_WIDTH-1 downto 0);
    signal rx_axi_eop_pos_bot : slv_array_t(MFB_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    signal continue_reg : std_logic;
    ---------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- input TUSER division
    -- -------------------------------------------------------------------------

    tuser_div_gen : for i in 0 to MFB_REGIONS-1 generate
        rx_axi_sop(i) <= RX_AXI_TUSER(i+BE_WIDTH);

        rx_axi_eop_pos_top(i) <= rx_axi_eop_pos(i)(EOP_POS_WIDTH-1 downto EOF_POS_WIDTH);
        rx_axi_eop_pos_bot(i) <= rx_axi_eop_pos(i)(EOF_POS_WIDTH-1 downto 0);
    end generate;

    ultrascale_pos_gen : if DEVICE = "ULTRASCALE" generate
        tuser_div_gen : for i in 0 to MFB_REGIONS-1 generate
            rx_axi_eop(i)     <= RX_AXI_TUSER(i+SOP_POS_WIDTH*MFB_REGIONS+MFB_REGIONS+BE_WIDTH);
            rx_axi_eop_pos(i) <= RX_AXI_TUSER(EOP_POS_WIDTH*(i+1)+MFB_REGIONS+SOP_POS_WIDTH*MFB_REGIONS+MFB_REGIONS+BE_WIDTH-1 downto EOP_POS_WIDTH*i+MFB_REGIONS+SOP_POS_WIDTH*MFB_REGIONS+MFB_REGIONS+BE_WIDTH);

            rx_axi_sop_pos(i) <= RX_AXI_TUSER(SOP_POS_WIDTH*(i+1)+MFB_REGIONS+BE_WIDTH-1 downto SOP_POS_WIDTH*i+MFB_REGIONS+BE_WIDTH);

            rx_axi_sop_pos_top(i) <= rx_axi_sop_pos(i)(SOP_POS_WIDTH-1 downto SOF_POS_WIDTH);
            rx_axi_sop_pos_bot(i) <= rx_axi_sop_pos(i)(SOF_POS_WIDTH-1 downto 0);
        end generate;
    end generate;

    virtex7series_pos_gen : if DEVICE = "7SERIES" generate
        tuser_div_gen : for i in 0 to MFB_REGIONS-1 generate
            rx_axi_eop(i)     <= RX_AXI_TUSER(MFB_REGIONS+BE_WIDTH+(EOP_POS_WIDTH+1)*i);
            rx_axi_eop_pos(i) <= RX_AXI_TUSER(MFB_REGIONS+BE_WIDTH+(EOP_POS_WIDTH+1)*(i+1)-1 downto MFB_REGIONS+BE_WIDTH+(EOP_POS_WIDTH+1)*i+1);
        end generate;

        cont_reg_ptr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RX_AXI_TVALID = '1') then
                    continue_reg <= continue_reg xor (xor rx_axi_eop) xor (xor rx_axi_sop); -- negate continue_reg value when the sum of EOPs and SOPs is odd (correct sequence of SOPs and EOPs is expected)
                end if;

                if (RESET = '1') then
                    continue_reg <= '0';
                end if;
            end if;
        end process;

        -- non-generic assign (fit only for MFB configuration (2,1,4,32))
        rx_axi_sop_pos_top(0)(0) <= '0' when continue_reg = '0' else '1';
        rx_axi_sop_pos_top(1)(0) <= '1';
        rx_axi_sop_pos_bot       <= (others => (others => '0'));
    end generate;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- interface conversion
    -- -------------------------------------------------------------------------

    TX_MFB_DATA    <= RX_AXI_TDATA;
    TX_MFB_SRC_RDY <= RX_AXI_TVALID;
    RX_AXI_TREADY  <= TX_MFB_DST_RDY;

    -- conversion process
    sop_eop_sof_eof_conv_pr : process (rx_axi_sop_pos_top,rx_axi_sop_pos_bot,rx_axi_sop,rx_axi_eop_pos_top,rx_axi_eop_pos_bot,rx_axi_eop)
        variable ptr : integer;
    begin
        -- default values
        TX_MFB_SOF_POS <= (others => '0');
        TX_MFB_EOF_POS <= (others => '0');
        TX_MFB_SOF     <= (others => '0');
        TX_MFB_EOF     <= (others => '0');

        -- for each input region
        for i in 0 to MFB_REGIONS-1 loop
            if (rx_axi_sop(i) = '1') then
                ptr                                                                        := to_integer(unsigned(rx_axi_sop_pos_top(i)));
                TX_MFB_SOF    (ptr)                                                        <= '1';
                TX_MFB_SOF_POS(SOF_POS_TRUE_WIDTH*(ptr+1)-1 downto SOF_POS_TRUE_WIDTH*ptr) <= std_logic_vector(resize(unsigned(rx_axi_sop_pos_bot(i)),SOF_POS_TRUE_WIDTH));
            end if;

            if (rx_axi_eop(i) = '1') then
                ptr                                                                        := to_integer(unsigned(rx_axi_eop_pos_top(i)));
                TX_MFB_EOF    (ptr)                                                        <= '1';
                TX_MFB_EOF_POS(EOF_POS_TRUE_WIDTH*(ptr+1)-1 downto EOF_POS_TRUE_WIDTH*ptr) <= std_logic_vector(resize(unsigned(rx_axi_eop_pos_bot(i)),EOF_POS_TRUE_WIDTH));
            end if;
        end loop;
    end process;

    -- -------------------------------------------------------------------------

end architecture;
