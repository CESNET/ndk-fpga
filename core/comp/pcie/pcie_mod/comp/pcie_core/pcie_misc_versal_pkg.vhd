-- pcie_misc_versal_pkg.vhd: Package for connecting PCIE signals via misc
--                  signals for Versal FPGAs
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2025
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- General template package to connect PCIE via misc signals on Versal chips
--
-- The order of the record fields is the layout of the MISC signals (the first
-- field is at the MSB). When adding, removing or reordering a field, keep the
-- same order and widths in:
--   - the records t_misc_pcie_out and t_misc_pcie_in,
--   - the functions pack, widths_out, widths_in and unpack below,
--   - the packed structs misc_pcie_out_t and misc_pcie_in_t in the PCIE_MOD
--     UVM testbench (core/comp/pcie/pcie_mod/uvm/tbench/testbench_xilinx_versal.sv).
-- PCIE_CORE (VERSAL) checks only the total width of the MISC signals. It does
-- not detect two fields of the same width in a different order.
package pcie_misc_versal_template is
    generic (
        AXI_DATA_WIDTH   : integer;
        AXI_CQUSER_WIDTH   : integer;
        AXI_CCUSER_WIDTH : integer;
        AXI_RQUSER_WIDTH : integer;
        AXI_RCUSER_WIDTH  : integer
    );
    -- AXI requests
    type t_misc_pcie_out is record
        USER_CLK                               : std_logic;
        USER_RESET                             : std_logic;
        USER_LNK_UP                            : std_logic;
        S_AXIS_RQ_TREADY                       : std_logic;
        M_AXIS_RC_TDATA                        : std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        M_AXIS_RC_TKEEP                        : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        M_AXIS_RC_TLAST                        : std_logic;
        M_AXIS_RC_TUSER                        : std_logic_vector(AXI_RCUSER_WIDTH-1  downto 0);
        M_AXIS_RC_TVALID                       : std_logic;
        M_AXIS_CQ_TDATA                        : std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        M_AXIS_CQ_TKEEP                        : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        M_AXIS_CQ_TLAST                        : std_logic;
        M_AXIS_CQ_TUSER                        : std_logic_vector(AXI_CQUSER_WIDTH-1  downto 0);
        M_AXIS_CQ_TVALID                       : std_logic;
        S_AXIS_CC_TREADY                       : std_logic;
        CFG_STATUS_RQ_TAG0                     : std_logic_vector(9     downto  0);
        CFG_STATUS_RQ_TAG1                     : std_logic_vector(9     downto  0);
        CFG_STATUS_RQ_TAG2                     : std_logic_vector(9     downto  0);
        CFG_STATUS_RQ_TAG3                     : std_logic_vector(9     downto  0);
        CFG_STATUS_RQ_TAG_VLD0                 : std_logic;
        CFG_STATUS_RQ_TAG_VLD1                 : std_logic;
        CFG_STATUS_RQ_TAG_VLD2                 : std_logic;
        CFG_STATUS_RQ_TAG_VLD3                 : std_logic;
        CFG_STATUS_PHY_LINK_DOWN               : std_logic;
        CFG_STATUS_PHY_LINK_STATUS             : std_logic_vector(1     downto  0);
        CFG_STATUS_NEGOTIATED_WIDTH            : std_logic_vector(2     downto  0);
        CFG_STATUS_CURRENT_SPEED               : std_logic_vector(2     downto  0);
        CFG_STATUS_MAX_PAYLOAD                 : std_logic_vector(1     downto  0);
        CFG_STATUS_MAX_READ_REQ                : std_logic_vector(2     downto  0);
        CFG_STATUS_FUNCTION_STATUS             : std_logic_vector(3     downto  0);
        CFG_STATUS_FUNCTION_POWER_STATE        : std_logic_vector(2     downto  0);
        CFG_STATUS_LINK_POWER_STATE            : std_logic_vector(1     downto  0);
        CFG_STATUS_LOCAL_ERROR_VALID           : std_logic;
        CFG_STATUS_LOCAL_ERROR_OUT             : std_logic_vector(4     downto  0);
        CFG_STATUS_LTSSM_STATE                 : std_logic_vector(5     downto  0);
        CFG_STATUS_RX_PM_STATE                 : std_logic_vector(1     downto  0);
        CFG_STATUS_TX_PM_STATE                 : std_logic_vector(1     downto  0);
        CFG_STATUS_RCB_STATUS                  : std_logic;
        CFG_FC_PH                              : std_logic_vector(7    downto  0);
        CFG_FC_PD                              : std_logic_vector(11   downto  0);
        CFG_FC_NPH                             : std_logic_vector(7    downto  0);
        CFG_FC_NPD                             : std_logic_vector(11   downto  0);
        CFG_EXT_READ_RECEIVED                  : std_logic;
        CFG_EXT_WRITE_RECEIVED                 : std_logic;
        CFG_EXT_REGISTER_NUMBER                : std_logic_vector(9     downto  0);
        CFG_EXT_FUNCTION_NUMBER                : std_logic_vector(15    downto  0);
        CFG_EXT_WRITE_DATA                     : std_logic_vector(31    downto  0);
        CFG_EXT_WRITE_BYTE_ENABLE              : std_logic_vector(3     downto  0);
    end record;

    type t_misc_pcie_in is record
        S_AXIS_RQ_TDATA                        : std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        S_AXIS_RQ_TKEEP                        : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        S_AXIS_RQ_TLAST                        : std_logic;
        S_AXIS_RQ_TUSER                        : std_logic_vector(AXI_RQUSER_WIDTH-1  downto 0);
        S_AXIS_RQ_TVALID                       : std_logic;
        M_AXIS_RC_TREADY                       : std_logic;
        M_AXIS_CQ_TREADY                       : std_logic;
        S_AXIS_CC_TDATA                        : std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        S_AXIS_CC_TKEEP                        : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        S_AXIS_CC_TLAST                        : std_logic;
        S_AXIS_CC_TUSER                        : std_logic_vector(AXI_CCUSER_WIDTH-1  downto 0);
        S_AXIS_CC_TVALID                       : std_logic;
        CFG_EXT_READ_DATA                      : std_logic_vector(31    downto  0);
        CFG_EXT_READ_DATA_VALID                : std_logic;
    end record;

    function width_out return natural;
    function width_in return natural;

    function pack (r : t_misc_pcie_out) return std_logic_vector;
    function pack (r : t_misc_pcie_in) return std_logic_vector;

    function unpack (t : t_misc_pcie_out; v : std_logic_vector) return t_misc_pcie_out;
    function unpack (t : t_misc_pcie_in; v : std_logic_vector) return t_misc_pcie_in;
end package;

package body pcie_misc_versal_template is
    type natural_vector is array (natural range <>) of natural;

    function prefix_sum (a : natural_vector) return natural_vector is
        variable s : natural;
        variable r : natural_vector(a'LENGTH downto 0);
    begin
        s := 0;
        for i in 0 to a'LENGTH-1 loop
            r(i) := s;
            s    := s + a(i);
        end loop;
        r(a'LENGTH) := s;
        return r;
    end function;

    function vector_sum (a : natural_vector) return natural is
        variable s : natural;
    begin
        s := 0;
        for i in 0 to a'LENGTH-1 loop
            s := s + a(i);
        end loop;
        return s;
    end function;

    function pack (r : t_misc_pcie_out) return std_logic_vector is
        variable v : std_logic_vector(width_out-1 downto 0);
    begin
        v := r.USER_CLK
             & r.USER_RESET
             & r.USER_LNK_UP
             & r.S_AXIS_RQ_TREADY
             & r.M_AXIS_RC_TDATA
             & r.M_AXIS_RC_TKEEP
             & r.M_AXIS_RC_TLAST
             & r.M_AXIS_RC_TUSER
             & r.M_AXIS_RC_TVALID
             & r.M_AXIS_CQ_TDATA
             & r.M_AXIS_CQ_TKEEP
             & r.M_AXIS_CQ_TLAST
             & r.M_AXIS_CQ_TUSER
             & r.M_AXIS_CQ_TVALID
             & r.S_AXIS_CC_TREADY
             & r.CFG_STATUS_RQ_TAG0
             & r.CFG_STATUS_RQ_TAG1
             & r.CFG_STATUS_RQ_TAG2
             & r.CFG_STATUS_RQ_TAG3
             & r.CFG_STATUS_RQ_TAG_VLD0
             & r.CFG_STATUS_RQ_TAG_VLD1
             & r.CFG_STATUS_RQ_TAG_VLD2
             & r.CFG_STATUS_RQ_TAG_VLD3
             & r.CFG_STATUS_PHY_LINK_DOWN
             & r.CFG_STATUS_PHY_LINK_STATUS
             & r.CFG_STATUS_NEGOTIATED_WIDTH
             & r.CFG_STATUS_CURRENT_SPEED
             & r.CFG_STATUS_MAX_PAYLOAD
             & r.CFG_STATUS_MAX_READ_REQ
             & r.CFG_STATUS_FUNCTION_STATUS
             & r.CFG_STATUS_FUNCTION_POWER_STATE
             & r.CFG_STATUS_LINK_POWER_STATE
             & r.CFG_STATUS_LOCAL_ERROR_VALID
             & r.CFG_STATUS_LOCAL_ERROR_OUT
             & r.CFG_STATUS_LTSSM_STATE
             & r.CFG_STATUS_RX_PM_STATE
             & r.CFG_STATUS_TX_PM_STATE
             & r.CFG_STATUS_RCB_STATUS
             & r.CFG_FC_PH
             & r.CFG_FC_PD
             & r.CFG_FC_NPH
             & r.CFG_FC_NPD
             & r.CFG_EXT_READ_RECEIVED
             & r.CFG_EXT_WRITE_RECEIVED
             & r.CFG_EXT_REGISTER_NUMBER
             & r.CFG_EXT_FUNCTION_NUMBER
             & r.CFG_EXT_WRITE_DATA
             & r.CFG_EXT_WRITE_BYTE_ENABLE;
        return v;
    end function;

    function pack (r : t_misc_pcie_in) return std_logic_vector is
        variable v : std_logic_vector(width_in-1 downto 0);
    begin
        v := r.S_AXIS_RQ_TDATA
             & r.S_AXIS_RQ_TKEEP
             & r.S_AXIS_RQ_TLAST
             & r.S_AXIS_RQ_TUSER
             & r.S_AXIS_RQ_TVALID
             & r.M_AXIS_RC_TREADY
             & r.M_AXIS_CQ_TREADY
             & r.S_AXIS_CC_TDATA
             & r.S_AXIS_CC_TKEEP
             & r.S_AXIS_CC_TLAST
             & r.S_AXIS_CC_TUSER
             & r.S_AXIS_CC_TVALID
             & r.CFG_EXT_READ_DATA
             & r.CFG_EXT_READ_DATA_VALID;
        return v;
    end function;

    function widths_out return natural_vector is
        constant C : natural_vector(48 - 1 downto 0) := (
            1, 1, 1, 1,
            AXI_DATA_WIDTH, AXI_DATA_WIDTH/32, 1, AXI_RCUSER_WIDTH, 1,
            AXI_DATA_WIDTH, AXI_DATA_WIDTH/32, 1, AXI_CQUSER_WIDTH, 1,
            1,
            10, 10, 10, 10,
            1, 1, 1, 1,
            1, 2, 3, 3, 2, 3, 4, 3, 2, 1, 5, 6, 2, 2, 1,
            8, 12, 8, 12,
            1, 1, 10, 16, 32, 4
        );
    begin
        return C;
    end function;

    function widths_in return natural_vector is
        constant C : natural_vector(14 - 1 downto 0) := (
            AXI_DATA_WIDTH, AXI_DATA_WIDTH/32, 1, AXI_RQUSER_WIDTH, 1,
            1, 1,
            AXI_DATA_WIDTH, AXI_DATA_WIDTH/32, 1, AXI_CCUSER_WIDTH, 1,
            32, 1
        );
    begin
        return C;
    end function;

    function width_out return natural is
    begin
        return vector_sum(widths_out);
    end function;

    function width_in return natural is
    begin
        return vector_sum(widths_in);
    end function;

    function unpack (t : t_misc_pcie_out; v : std_logic_vector) return t_misc_pcie_out is
        constant O : natural_vector := prefix_sum(widths_out);
        variable r : t_misc_pcie_out;
    begin
        r.USER_CLK                        := v(O(47));
        r.USER_RESET                      := v(O(46));
        r.USER_LNK_UP                     := v(O(45));
        r.S_AXIS_RQ_TREADY                := v(O(44));
        r.M_AXIS_RC_TDATA                 := v(O(44) - 1 downto O(43));
        r.M_AXIS_RC_TKEEP                 := v(O(43) - 1 downto O(42));
        r.M_AXIS_RC_TLAST                 := v(O(41));
        r.M_AXIS_RC_TUSER                 := v(O(41) - 1 downto O(40));
        r.M_AXIS_RC_TVALID                := v(O(39));
        r.M_AXIS_CQ_TDATA                 := v(O(39) - 1 downto O(38));
        r.M_AXIS_CQ_TKEEP                 := v(O(38) - 1 downto O(37));
        r.M_AXIS_CQ_TLAST                 := v(O(36));
        r.M_AXIS_CQ_TUSER                 := v(O(36) - 1 downto O(35));
        r.M_AXIS_CQ_TVALID                := v(O(34));
        r.S_AXIS_CC_TREADY                := v(O(33));
        r.CFG_STATUS_RQ_TAG0              := v(O(33) - 1 downto O(32));
        r.CFG_STATUS_RQ_TAG1              := v(O(32) - 1 downto O(31));
        r.CFG_STATUS_RQ_TAG2              := v(O(31) - 1 downto O(30));
        r.CFG_STATUS_RQ_TAG3              := v(O(30) - 1 downto O(29));
        r.CFG_STATUS_RQ_TAG_VLD0          := v(O(28));
        r.CFG_STATUS_RQ_TAG_VLD1          := v(O(27));
        r.CFG_STATUS_RQ_TAG_VLD2          := v(O(26));
        r.CFG_STATUS_RQ_TAG_VLD3          := v(O(25));
        r.CFG_STATUS_PHY_LINK_DOWN        := v(O(24));
        r.CFG_STATUS_PHY_LINK_STATUS      := v(O(24) - 1 downto O(23));
        r.CFG_STATUS_NEGOTIATED_WIDTH     := v(O(23) - 1 downto O(22));
        r.CFG_STATUS_CURRENT_SPEED        := v(O(22) - 1 downto O(21));
        r.CFG_STATUS_MAX_PAYLOAD          := v(O(21) - 1 downto O(20));
        r.CFG_STATUS_MAX_READ_REQ         := v(O(20) - 1 downto O(19));
        r.CFG_STATUS_FUNCTION_STATUS      := v(O(19) - 1 downto O(18));
        r.CFG_STATUS_FUNCTION_POWER_STATE := v(O(18) - 1 downto O(17));
        r.CFG_STATUS_LINK_POWER_STATE     := v(O(17) - 1 downto O(16));
        r.CFG_STATUS_LOCAL_ERROR_VALID    := v(O(15));
        r.CFG_STATUS_LOCAL_ERROR_OUT      := v(O(15) - 1 downto O(14));
        r.CFG_STATUS_LTSSM_STATE          := v(O(14) - 1 downto O(13));
        r.CFG_STATUS_RX_PM_STATE          := v(O(13) - 1 downto O(12));
        r.CFG_STATUS_TX_PM_STATE          := v(O(12) - 1 downto O(11));
        r.CFG_STATUS_RCB_STATUS           := v(O(10));
        r.CFG_FC_PH                       := v(O(10) - 1 downto O( 9));
        r.CFG_FC_PD                       := v(O( 9) - 1 downto O( 8));
        r.CFG_FC_NPH                      := v(O( 8) - 1 downto O( 7));
        r.CFG_FC_NPD                      := v(O( 7) - 1 downto O( 6));
        r.CFG_EXT_READ_RECEIVED           := v(O( 5));
        r.CFG_EXT_WRITE_RECEIVED          := v(O( 4));
        r.CFG_EXT_REGISTER_NUMBER         := v(O( 4) - 1 downto O( 3));
        r.CFG_EXT_FUNCTION_NUMBER         := v(O( 3) - 1 downto O( 2));
        r.CFG_EXT_WRITE_DATA              := v(O( 2) - 1 downto O( 1));
        r.CFG_EXT_WRITE_BYTE_ENABLE       := v(O( 1) - 1 downto O( 0));

        return r;
    end function;

    function unpack (t : t_misc_pcie_in; v : std_logic_vector) return t_misc_pcie_in is
        constant O : natural_vector := prefix_sum(widths_in);
        variable r : t_misc_pcie_in;
    begin
        r.S_AXIS_RQ_TDATA         := v(O(14) - 1 downto O(13));
        r.S_AXIS_RQ_TKEEP         := v(O(13) - 1 downto O(12));
        r.S_AXIS_RQ_TLAST         := v(O(11));
        r.S_AXIS_RQ_TUSER         := v(O(11) - 1 downto O(10));
        r.S_AXIS_RQ_TVALID        := v(O(9));
        r.M_AXIS_RC_TREADY        := v(O(8));
        r.M_AXIS_CQ_TREADY        := v(O(7));
        r.S_AXIS_CC_TDATA         := v(O(7) - 1 downto O(6));
        r.S_AXIS_CC_TKEEP         := v(O(6) - 1 downto O(5));
        r.S_AXIS_CC_TLAST         := v(O(4));
        r.S_AXIS_CC_TUSER         := v(O(4) - 1 downto O(3));
        r.S_AXIS_CC_TVALID        := v(O(2));
        r.CFG_EXT_READ_DATA       := v(O(2) - 1 downto O(1));
        r.CFG_EXT_READ_DATA_VALID := v(O(0));

        return r;
    end function;
end package body;
