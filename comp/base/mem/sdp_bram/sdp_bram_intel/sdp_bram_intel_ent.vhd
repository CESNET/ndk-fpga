-- sdp_bram_intel_ent.vhd: sdp_bram_intel
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity SDP_BRAM_INTEL is
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
        -- True = clock write port and read port with WR_CLK
        -- False = clock write port with WR_CLK and read port with RD_CLK
        COMMON_CLOCK   : boolean := True;
        -- Output directly from BRAM or throw register (better timing).
        OUTPUT_REG     : boolean := True;
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        -- "7SERIES", "ULTRASCALE", "STRATIX10", "ARRIA10", "AGILEX"
        DEVICE         : string := "STRATIX10"
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
        -- Clock enable of read port.
        RD_PIPE_EN  : in  std_logic;
        -- Read address.
        RD_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        -- Read data output.
        RD_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;
