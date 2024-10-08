-- pcie_core_empty.vhd: PCIe module
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture EMPTY of PCIE_CORE is

begin

    PCIE_TX_P           <= (others => '0');
    PCIE_TX_N           <= (others => '1');

    PCIE_LINK_UP        <= (others => '0');
    PCIE_MPS            <= (others => (others => '0'));
    PCIE_MRRS           <= (others => (others => '0'));
    PCIE_EXT_TAG_EN     <= (others => '0');
    PCIE_10B_TAG_REQ_EN <= (others => '0');
    PCIE_RCB_SIZE       <= (others => '0');
 
    PCIE_USER_CLK       <= (others => '0');
    PCIE_USER_RESET     <= (others => (others => '0'));

    CQ_MFB_DATA         <= (others => (others => '0'));
    CQ_MFB_META         <= (others => (others => '0'));
    CQ_MFB_SOF          <= (others => (others => '0'));
    CQ_MFB_EOF          <= (others => (others => '0'));
    CQ_MFB_EOF_POS      <= (others => (others => '0'));
    CQ_MFB_SRC_RDY      <= (others => '0');

    RC_MFB_DATA         <= (others => (others => '0'));
    RC_MFB_META         <= (others => (others => '0'));
    RC_MFB_SOF          <= (others => (others => '0'));
    RC_MFB_EOF          <= (others => (others => '0'));
    RC_MFB_EOF_POS      <= (others => (others => '0'));
    RC_MFB_SRC_RDY      <= (others => '0');

    CC_MFB_DST_RDY      <= (others => '0');

    RQ_MFB_DST_RDY      <= (others => '0');

    TAG_ASSIGN          <= (others => (others => '0'));
    TAG_ASSIGN_VLD      <= (others => (others => '0'));

end architecture;
