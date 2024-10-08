-- ptc_dma2pcie_hdr_transform_ent.vhd: DMA to PCIe header transform for PTC component - entity
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
--                             Entity
-- ----------------------------------------------------------------------------

entity PTC_DMA2PCIE_HDR_TRANSFORM is
   generic (
      -- Number of MVB headers
      MVB_ITEMS        : integer := 2;

      -- Width of one PCIe UP header (defined in PCIe specification) (minimum is 4*4*8)
      PCIE_UPHDR_WIDTH : integer := 4*4*8;

      -- Width of Tag field in PCIe header (maximum 8 defined in PCIe specification)
      PCIE_TAG_WIDTH      : integer := 8;

      -- Width of PCIe transaction size signal. Set Log2 of maximum supported
      -- PCIe transaction size (HDR + payload) in dwords
      TRANS_SIZE_WIDTH : natural := 8;

      -- Target device
      -- "VIRTEX6", "7SERIES", "ULTRASCALE"
      DEVICE           : string  := "ULTRASCALE"
   );
   port(
      ---------------------------------------------------------------------------
      -- Common interface
      ---------------------------------------------------------------------------

      CLK                 : in  std_logic;
      RESET               : in  std_logic;

      ---------------------------------------------------------------------------
      -- RX DMA MVB interface
      ---------------------------------------------------------------------------

      -- Upstream headers
      RX_MVB_DATA     : in  std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
      -- Valid bit for each UP header
      RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS                -1 downto 0);
      -- Source ready entire UP stream
      RX_MVB_SRC_RDY  : in  std_logic;
      -- Destination ready entire UP stream
      RX_MVB_DST_RDY  : out std_logic;

      ---------------------------------------------------------------------------
      -- Interface to Tag manager for checking of receiving buffer space
      ---------------------------------------------------------------------------

      -- IN - inserting headers to Tag manager
      -- Upstream headers
      TAGM_MVB_IN          : out std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
      -- Valid bit for each UP header
      TAGM_MVB_IN_VLD      : out std_logic_vector(MVB_ITEMS                -1 downto 0);
      -- Source ready for entire UP stream
      TAGM_MVB_IN_SRC_RDY  : out std_logic;
      -- Destination ready for entire UP stream
      TAGM_MVB_IN_DST_RDY  : in  std_logic;

      -- OUT - getting headers back from Tag manager after enough buffer space (credits) has been checked
      -- Upstream headers
      TAGM_MVB_OUT          : in  std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
      -- Tag is separated from rest of the header, since it can be different width from the input Tag
      TAGM_MVB_OUT_TAG      : in  std_logic_vector(MVB_ITEMS*PCIE_TAG_WIDTH -1 downto 0);
      -- Valid bit for each UP header
      TAGM_MVB_OUT_VLD      : in  std_logic_vector(MVB_ITEMS                -1 downto 0);
      -- Source ready for entire UP stream
      TAGM_MVB_OUT_SRC_RDY  : in  std_logic;
      -- Destination ready for entire UP stream
      TAGM_MVB_OUT_DST_RDY  : out std_logic;

      ---------------------------------------------------------------------------
      -- TX PCIe MVB interface
      ---------------------------------------------------------------------------

      -- Upstream headers
      TX_MVB_DATA         : out std_logic_vector(MVB_ITEMS*PCIE_UPHDR_WIDTH-1 downto 0);
      -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
      TX_MVB_BE           : out std_logic_vector(MVB_ITEMS*8               -1 downto 0);
      -- Is PCIe transaction with payload
      TX_MVB_PAYLOAD      : out std_logic_vector(MVB_ITEMS                 -1 downto 0);
      -- Size of transaction payload (valid when TX_MVB_PAYLOAD(i)='1')
      TX_MVB_PAYLOAD_SIZE : out std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
      -- PCIe heade size type (Intel only) ('0' -> 96-bit type, '1' -> 128-bit type)
      TX_MVB_TYPE         : out std_logic_vector(MVB_ITEMS                 -1 downto 0);
      -- Valid bit for each UP header
      TX_MVB_VLD          : out std_logic_vector(MVB_ITEMS                 -1 downto 0);
      -- Source ready entire UP stream
      TX_MVB_SRC_RDY      : out std_logic;
      -- Destination ready entire UP stream
      TX_MVB_DST_RDY      : in  std_logic
   );
end entity PTC_DMA2PCIE_HDR_TRANSFORM;
