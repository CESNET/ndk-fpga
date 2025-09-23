library IEEE;
use IEEE.std_logic_1164.all;

package pcie_hdr_fields_pkg is
    -- =============================================================================================
    -- AMD's Requester Request (RQ) interface header
    -- =============================================================================================
    constant A_RQ_HDR_AT_W           : natural := 2;
    constant A_RQ_HDR_ADDR_W         : natural := 62;
    constant A_RQ_HDR_DWORD_CNT_W    : natural := 11;
    constant A_RQ_HDR_REQ_TYPE_W     : natural := 4;
    constant A_RQ_HDR_POISONED_W     : natural := 1;
    constant A_RQ_HDR_REQUESTER_ID_W : natural := 16;
    constant A_RQ_HDR_TAG_W          : natural := 8;
    constant A_RQ_HDR_COMPLETER_ID_W : natural := 16;
    constant A_RQ_HDR_REQ_ID_EN_W    : natural := 1;
    constant A_RQ_HDR_TR_CLASS_W     : natural := 3;
    constant A_RQ_HDR_NO_SNOOP_W     : natural := 1;
    constant A_RQ_HDR_RLX_ORD_W      : natural := 1;
    constant A_RQ_HDR_ID_ORD_W       : natural := 1;
    constant A_RQ_HDR_FORCE_ECRC_W   : natural := 1;

    constant A_RQ_HDR_AT_O           : natural := 0;
    constant A_RQ_HDR_ADDR_O         : natural := A_RQ_HDR_AT_O             + A_RQ_HDR_AT_W;
    constant A_RQ_HDR_DWORD_CNT_O    : natural := A_RQ_HDR_ADDR_O           + A_RQ_HDR_ADDR_W;
    constant A_RQ_HDR_REQ_TYPE_O     : natural := A_RQ_HDR_DWORD_CNT_O      + A_RQ_HDR_DWORD_CNT_W;
    constant A_RQ_HDR_POISONED_O     : natural := A_RQ_HDR_REQ_TYPE_O       + A_RQ_HDR_REQ_TYPE_W;
    constant A_RQ_HDR_REQUESTER_ID_O : natural := A_RQ_HDR_POISONED_O       + A_RQ_HDR_POISONED_W;
    constant A_RQ_HDR_TAG_O          : natural := A_RQ_HDR_REQUESTER_ID_O   + A_RQ_HDR_REQUESTER_ID_W;
    constant A_RQ_HDR_COMPLETER_ID_O : natural := A_RQ_HDR_TAG_O            + A_RQ_HDR_TAG_W;
    constant A_RQ_HDR_REQ_ID_EN_O    : natural := A_RQ_HDR_COMPLETER_ID_O   + A_RQ_HDR_COMPLETER_ID_W;
    constant A_RQ_HDR_TR_CLASS_O     : natural := A_RQ_HDR_REQ_ID_EN_O      + A_RQ_HDR_REQ_ID_EN_W;
    constant A_RQ_HDR_NO_SNOOP_O     : natural := A_RQ_HDR_TR_CLASS_O       + A_RQ_HDR_TR_CLASS_W;
    constant A_RQ_HDR_RLX_ORD_O      : natural := A_RQ_HDR_NO_SNOOP_O       + A_RQ_HDR_NO_SNOOP_W;
    constant A_RQ_HDR_ID_ORD_O       : natural := A_RQ_HDR_RLX_ORD_O        + A_RQ_HDR_RLX_ORD_W;
    constant A_RQ_HDR_FORCE_ECRC_O   : natural := A_RQ_HDR_ID_ORD_O         + A_RQ_HDR_ID_ORD_W;

    subtype A_RQ_HDR_AT           is natural range A_RQ_HDR_AT_O            + A_RQ_HDR_AT_W             - 1 downto A_RQ_HDR_AT_O;
    subtype A_RQ_HDR_ADDR         is natural range A_RQ_HDR_ADDR_O          + A_RQ_HDR_ADDR_W           - 1 downto A_RQ_HDR_ADDR_O;
    subtype A_RQ_HDR_DWORD_CNT    is natural range A_RQ_HDR_DWORD_CNT_O     + A_RQ_HDR_DWORD_CNT_W      - 1 downto A_RQ_HDR_DWORD_CNT_O;
    subtype A_RQ_HDR_REQ_TYPE     is natural range A_RQ_HDR_REQ_TYPE_O      + A_RQ_HDR_REQ_TYPE_W       - 1 downto A_RQ_HDR_REQ_TYPE_O;
    subtype A_RQ_HDR_POISONED     is natural range A_RQ_HDR_POISONED_O      + A_RQ_HDR_POISONED_W       - 1 downto A_RQ_HDR_POISONED_O;
    subtype A_RQ_HDR_REQUESTER_ID is natural range A_RQ_HDR_REQUESTER_ID_O  + A_RQ_HDR_REQUESTER_ID_W   - 1 downto A_RQ_HDR_REQUESTER_ID_O;
    subtype A_RQ_HDR_TAG          is natural range A_RQ_HDR_TAG_O           + A_RQ_HDR_TAG_W            - 1 downto A_RQ_HDR_TAG_O;
    subtype A_RQ_HDR_COMPLETER_ID is natural range A_RQ_HDR_COMPLETER_ID_O  + A_RQ_HDR_COMPLETER_ID_W   - 1 downto A_RQ_HDR_COMPLETER_ID_O;
    subtype A_RQ_HDR_REQ_ID_EN    is natural range A_RQ_HDR_REQ_ID_EN_O     + A_RQ_HDR_REQ_ID_EN_W      - 1 downto A_RQ_HDR_REQ_ID_EN_O;
    subtype A_RQ_HDR_TR_CLASS     is natural range A_RQ_HDR_TR_CLASS_O      + A_RQ_HDR_TR_CLASS_W       - 1 downto A_RQ_HDR_TR_CLASS_O;
    subtype A_RQ_HDR_NO_SNOOP     is natural range A_RQ_HDR_NO_SNOOP_O      + A_RQ_HDR_NO_SNOOP_W       - 1 downto A_RQ_HDR_NO_SNOOP_O;
    subtype A_RQ_HDR_RLX_ORD      is natural range A_RQ_HDR_RLX_ORD_O       + A_RQ_HDR_RLX_ORD_W        - 1 downto A_RQ_HDR_RLX_ORD_O;
    subtype A_RQ_HDR_ID_ORD       is natural range A_RQ_HDR_ID_ORD_O        + A_RQ_HDR_ID_ORD_W         - 1 downto A_RQ_HDR_ID_ORD_O;
    subtype A_RQ_HDR_FORCE_ECRC   is natural range A_RQ_HDR_FORCE_ECRC_O    + A_RQ_HDR_FORCE_ECRC_W     - 1 downto A_RQ_HDR_FORCE_ECRC_O;

    -- =============================================================================================
    -- AMD's Requester Completion (RC) Header
    -- =============================================================================================
    constant A_RC_HDR_ADDR_W         : natural := 12;
    constant A_RC_HDR_ERR_CODE_W     : natural := 4;
    constant A_RC_HDR_BYTE_CNT_W     : natural := 13;
    constant A_RC_HDR_LCK_RD_W       : natural := 1;
    constant A_RC_HDR_REQ_CPL_W      : natural := 1;
    constant A_RC_HDR_RSV0_W         : natural := 1;
    constant A_RC_HDR_DWORD_CNT_W    : natural := 11;
    constant A_RC_HDR_CPL_STATUS_W   : natural := 3;
    constant A_RC_HDR_POISONED_W     : natural := 1;
    constant A_RC_HDR_RSV1_W         : natural := 1;
    constant A_RC_HDR_REQUESTER_ID_W : natural := 16;
    constant A_RC_HDR_TAG_W          : natural := 8;
    constant A_RC_HDR_COMPLETER_ID_W : natural := 16;
    constant A_RC_HDR_RSV2_W         : natural := 1;
    constant A_RC_HDR_TC_W           : natural := 3;
    constant A_RC_HDR_NO_SNOOP_W     : natural := 1;
    constant A_RC_HDR_RLX_ORD_W      : natural := 1;
    constant A_RC_HDR_RSV3_W         : natural := 2;

    constant A_RC_HDR_ADDR_O          : natural := 0;
    constant A_RC_HDR_ERR_CODE_O      : natural := A_RC_HDR_ADDR_O         + A_RC_HDR_ADDR_W;
    constant A_RC_HDR_BYTE_CNT_O      : natural := A_RC_HDR_ERR_CODE_O     + A_RC_HDR_ERR_CODE_W;
    constant A_RC_HDR_LCK_RD_O        : natural := A_RC_HDR_BYTE_CNT_O     + A_RC_HDR_BYTE_CNT_W;
    constant A_RC_HDR_REQ_CPL_O       : natural := A_RC_HDR_LCK_RD_O       + A_RC_HDR_LCK_RD_W;
    constant A_RC_HDR_RSV0_O          : natural := A_RC_HDR_REQ_CPL_O      + A_RC_HDR_REQ_CPL_W;
    constant A_RC_HDR_DWORD_CNT_O     : natural := A_RC_HDR_RSV0_O         + A_RC_HDR_RSV0_W;
    constant A_RC_HDR_CPL_STATUS_O    : natural := A_RC_HDR_DWORD_CNT_O    + A_RC_HDR_DWORD_CNT_W;
    constant A_RC_HDR_POISONED_O      : natural := A_RC_HDR_CPL_STATUS_O   + A_RC_HDR_CPL_STATUS_W;
    constant A_RC_HDR_RSV1_O          : natural := A_RC_HDR_POISONED_O     + A_RC_HDR_POISONED_W;
    constant A_RC_HDR_REQUESTER_ID_O  : natural := A_RC_HDR_RSV1_O         + A_RC_HDR_RSV1_W;
    constant A_RC_HDR_TAG_O           : natural := A_RC_HDR_REQUESTER_ID_O + A_RC_HDR_REQUESTER_ID_W;
    constant A_RC_HDR_COMPLETER_ID_O  : natural := A_RC_HDR_TAG_O          + A_RC_HDR_TAG_W;
    constant A_RC_HDR_RSV2_O          : natural := A_RC_HDR_COMPLETER_ID_O + A_RC_HDR_COMPLETER_ID_W;
    constant A_RC_HDR_TC_O            : natural := A_RC_HDR_RSV2_O         + A_RC_HDR_RSV2_W;
    constant A_RC_HDR_NO_SNOOP_O      : natural := A_RC_HDR_TC_O           + A_RC_HDR_TC_W;
    constant A_RC_HDR_RLX_ORD_O       : natural := A_RC_HDR_NO_SNOOP_O     + A_RC_HDR_NO_SNOOP_W;
    constant A_RC_HDR_RSV3_O          : natural := A_RC_HDR_RLX_ORD_O      + A_RC_HDR_RLX_ORD_W;

    subtype A_RC_HDR_ADDR          is natural range A_RC_HDR_ADDR_O          + A_RC_HDR_ADDR_W          - 1 downto A_RC_HDR_ADDR_O;
    subtype A_RC_HDR_ERR_CODE      is natural range A_RC_HDR_ERR_CODE_O      + A_RC_HDR_ERR_CODE_W      - 1 downto A_RC_HDR_ERR_CODE_O;
    subtype A_RC_HDR_BYTE_CNT      is natural range A_RC_HDR_BYTE_CNT_O      + A_RC_HDR_BYTE_CNT_W      - 1 downto A_RC_HDR_BYTE_CNT_O;
    subtype A_RC_HDR_LCK_RD        is natural range A_RC_HDR_LCK_RD_O        + A_RC_HDR_LCK_RD_W        - 1 downto A_RC_HDR_LCK_RD_O;
    subtype A_RC_HDR_REQ_CPL       is natural range A_RC_HDR_REQ_CPL_O       + A_RC_HDR_REQ_CPL_W       - 1 downto A_RC_HDR_REQ_CPL_O;
    subtype A_RC_HDR_RSV0          is natural range A_RC_HDR_RSV0_O          + A_RC_HDR_RSV0_W          - 1 downto A_RC_HDR_RSV0_O;
    subtype A_RC_HDR_DWORD_CNT     is natural range A_RC_HDR_DWORD_CNT_O     + A_RC_HDR_DWORD_CNT_W     - 1 downto A_RC_HDR_DWORD_CNT_O;
    subtype A_RC_HDR_CPL_STATUS    is natural range A_RC_HDR_CPL_STATUS_O    + A_RC_HDR_CPL_STATUS_W    - 1 downto A_RC_HDR_CPL_STATUS_O;
    subtype A_RC_HDR_POISONED      is natural range A_RC_HDR_POISONED_O      + A_RC_HDR_POISONED_W      - 1 downto A_RC_HDR_POISONED_O;
    subtype A_RC_HDR_RSV1          is natural range A_RC_HDR_RSV1_O          + A_RC_HDR_RSV1_W          - 1 downto A_RC_HDR_RSV1_O;
    subtype A_RC_HDR_REQUESTER_ID  is natural range A_RC_HDR_REQUESTER_ID_O  + A_RC_HDR_REQUESTER_ID_W  - 1 downto A_RC_HDR_REQUESTER_ID_O;
    subtype A_RC_HDR_TAG           is natural range A_RC_HDR_TAG_O           + A_RC_HDR_TAG_W           - 1 downto A_RC_HDR_TAG_O;
    subtype A_RC_HDR_COMPLETER_ID  is natural range A_RC_HDR_COMPLETER_ID_O  + A_RC_HDR_COMPLETER_ID_W  - 1 downto A_RC_HDR_COMPLETER_ID_O;
    subtype A_RC_HDR_RSV2          is natural range A_RC_HDR_RSV2_O          + A_RC_HDR_RSV2_W          - 1 downto A_RC_HDR_RSV2_O;
    subtype A_RC_HDR_TC            is natural range A_RC_HDR_TC_O            + A_RC_HDR_TC_W            - 1 downto A_RC_HDR_TC_O;
    subtype A_RC_HDR_NO_SNOOP      is natural range A_RC_HDR_NO_SNOOP_O      + A_RC_HDR_NO_SNOOP_W      - 1 downto A_RC_HDR_NO_SNOOP_O;
    subtype A_RC_HDR_RLX_ORD       is natural range A_RC_HDR_RLX_ORD_O       + A_RC_HDR_RLX_ORD_W       - 1 downto A_RC_HDR_RLX_ORD_O;
    subtype A_RC_HDR_RSV3          is natural range A_RC_HDR_RSV3_O          + A_RC_HDR_RSV3_W          - 1 downto A_RC_HDR_RSV3_O;

    -- =============================================================================================
    -- AMD's Completer Request (CQ) header
    -- =============================================================================================
    constant A_CQ_HDR_AT_W           : natural := 2;
    constant A_CQ_HDR_ADDR_W         : natural := 62;
    constant A_CQ_HDR_DWORD_CNT_W    : natural := 11;
    constant A_CQ_HDR_REQ_TYPE_W     : natural := 4;
    constant A_CQ_HDR_RSV0_W         : natural := 1;
    constant A_CQ_HDR_REQUESTER_ID_W : natural := 16;
    constant A_CQ_HDR_TAG_W          : natural := 8;
    constant A_CQ_HDR_TGT_FUNC_W     : natural := 8;
    constant A_CQ_HDR_BAR_ID_W       : natural := 3;
    constant A_CQ_HDR_BAR_APPER_W    : natural := 6;
    constant A_CQ_HDR_TR_CLASS_W     : natural := 3;
    constant A_CQ_HDR_NO_SNOOP_W     : natural := 1;
    constant A_CQ_HDR_RLX_ORD_W      : natural := 1;
    constant A_CQ_HDR_ID_ORD_W       : natural := 1;
    constant A_CQ_HDR_RSV1_W         : natural := 1;

    constant A_CQ_HDR_AT_O           : natural := 0;
    constant A_CQ_HDR_ADDR_O         : natural := A_CQ_HDR_AT_O           + A_CQ_HDR_AT_W;
    constant A_CQ_HDR_DWORD_CNT_O    : natural := A_CQ_HDR_ADDR_O         + A_CQ_HDR_ADDR_W;
    constant A_CQ_HDR_REQ_TYPE_O     : natural := A_CQ_HDR_DWORD_CNT_O    + A_CQ_HDR_DWORD_CNT_W;
    constant A_CQ_HDR_RSV0_O         : natural := A_CQ_HDR_REQ_TYPE_O     + A_CQ_HDR_REQ_TYPE_W;
    constant A_CQ_HDR_REQUESTER_ID_O : natural := A_CQ_HDR_RSV0_O         + A_CQ_HDR_RSV0_W;
    constant A_CQ_HDR_TAG_O          : natural := A_CQ_HDR_REQUESTER_ID_O + A_CQ_HDR_REQUESTER_ID_W;
    constant A_CQ_HDR_TGT_FUNC_O     : natural := A_CQ_HDR_TAG_O          + A_CQ_HDR_TAG_W;
    constant A_CQ_HDR_BAR_ID_O       : natural := A_CQ_HDR_TGT_FUNC_O     + A_CQ_HDR_TGT_FUNC_W;
    constant A_CQ_HDR_BAR_APPER_O    : natural := A_CQ_HDR_BAR_ID_O       + A_CQ_HDR_BAR_ID_W;
    constant A_CQ_HDR_TR_CLASS_O     : natural := A_CQ_HDR_BAR_APPER_O    + A_CQ_HDR_BAR_APPER_W;
    constant A_CQ_HDR_NO_SNOOP_O     : natural := A_CQ_HDR_TR_CLASS_O     + A_CQ_HDR_TR_CLASS_W;
    constant A_CQ_HDR_RLX_ORD_O      : natural := A_CQ_HDR_NO_SNOOP_O     + A_CQ_HDR_NO_SNOOP_W;
    constant A_CQ_HDR_ID_ORD_O       : natural := A_CQ_HDR_RLX_ORD_O      + A_CQ_HDR_RLX_ORD_W;
    constant A_CQ_HDR_RSV1_O         : natural := A_CQ_HDR_ID_ORD_O       + A_CQ_HDR_ID_ORD_W;

    subtype A_CQ_HDR_AT           is natural range A_CQ_HDR_AT_O           + A_CQ_HDR_AT_W           - 1 downto A_CQ_HDR_AT_O;
    subtype A_CQ_HDR_ADDR         is natural range A_CQ_HDR_ADDR_O         + A_CQ_HDR_ADDR_W         - 1 downto A_CQ_HDR_ADDR_O;
    subtype A_CQ_HDR_DWORD_CNT    is natural range A_CQ_HDR_DWORD_CNT_O    + A_CQ_HDR_DWORD_CNT_W    - 1 downto A_CQ_HDR_DWORD_CNT_O;
    subtype A_CQ_HDR_REQ_TYPE     is natural range A_CQ_HDR_REQ_TYPE_O     + A_CQ_HDR_REQ_TYPE_W     - 1 downto A_CQ_HDR_REQ_TYPE_O;
    subtype A_CQ_HDR_RSV0         is natural range A_CQ_HDR_RSV0_O         + A_CQ_HDR_RSV0_W         - 1 downto A_CQ_HDR_RSV0_O;
    subtype A_CQ_HDR_REQUESTER_ID is natural range A_CQ_HDR_REQUESTER_ID_O + A_CQ_HDR_REQUESTER_ID_W - 1 downto A_CQ_HDR_REQUESTER_ID_O;
    subtype A_CQ_HDR_TAG          is natural range A_CQ_HDR_TAG_O          + A_CQ_HDR_TAG_W          - 1 downto A_CQ_HDR_TAG_O;
    subtype A_CQ_HDR_TGT_FUNC     is natural range A_CQ_HDR_TGT_FUNC_O     + A_CQ_HDR_TGT_FUNC_W     - 1 downto A_CQ_HDR_TGT_FUNC_O;
    subtype A_CQ_HDR_BAR_ID       is natural range A_CQ_HDR_BAR_ID_O       + A_CQ_HDR_BAR_ID_W       - 1 downto A_CQ_HDR_BAR_ID_O;
    subtype A_CQ_HDR_BAR_APPER    is natural range A_CQ_HDR_BAR_APPER_O    + A_CQ_HDR_BAR_APPER_W    - 1 downto A_CQ_HDR_BAR_APPER_O;
    subtype A_CQ_HDR_TR_CLASS     is natural range A_CQ_HDR_TR_CLASS_O     + A_CQ_HDR_TR_CLASS_W     - 1 downto A_CQ_HDR_TR_CLASS_O;
    subtype A_CQ_HDR_NO_SNOOP     is natural range A_CQ_HDR_NO_SNOOP_O     + A_CQ_HDR_NO_SNOOP_W     - 1 downto A_CQ_HDR_NO_SNOOP_O;
    subtype A_CQ_HDR_RLX_ORD      is natural range A_CQ_HDR_RLX_ORD_O      + A_CQ_HDR_RLX_ORD_W      - 1 downto A_CQ_HDR_RLX_ORD_O;
    subtype A_CQ_HDR_ID_ORD       is natural range A_CQ_HDR_ID_ORD_O       + A_CQ_HDR_ID_ORD_W       - 1 downto A_CQ_HDR_ID_ORD_O;
    subtype A_CQ_HDR_RSV1         is natural range A_CQ_HDR_RSV1_O         + A_CQ_HDR_RSV1_W         - 1 downto A_CQ_HDR_RSV1_O;

    -- =============================================================================================
    -- AMD's Completer Completion (CC) header
    -- =============================================================================================
    constant A_CC_HDR_ADDR_W         : natural := 7;
    constant A_CC_HDR_RSV0_W         : natural := 1;
    constant A_CC_HDR_AT_W           : natural := 2;
    constant A_CC_HDR_RSV1_W         : natural := 6;
    constant A_CC_HDR_BYTE_CNT_W     : natural := 13;
    constant A_CC_HDR_LCK_RD_W       : natural := 1;
    constant A_CC_HDR_RSV2_W         : natural := 2;
    constant A_CC_HDR_DWORD_CNT_W    : natural := 11;
    constant A_CC_HDR_CPL_STATUS_W   : natural := 3;
    constant A_CC_HDR_POISONED_W     : natural := 1;
    constant A_CC_HDR_RSV3_W         : natural := 1;
    constant A_CC_HDR_REQUESTER_ID_W : natural := 16;
    constant A_CC_HDR_TAG_W          : natural := 8;
    constant A_CC_HDR_COMPLETER_ID_W : natural := 16;
    constant A_CC_HDR_CPL_ID_EN_W    : natural := 1;
    constant A_CC_HDR_TC_W           : natural := 3;
    constant A_CC_HDR_NO_SNOOP_W     : natural := 1;
    constant A_CC_HDR_RLX_ORD_W      : natural := 1;
    constant A_CC_HDR_ID_ORD_W       : natural := 1;
    constant A_CC_HDR_FORCE_ECRC_W   : natural := 1;

    constant A_CC_HDR_ADDR_O         : natural := 0;
    constant A_CC_HDR_RSV0_O         : natural := A_CC_HDR_ADDR_O         + A_CC_HDR_ADDR_W;
    constant A_CC_HDR_AT_O           : natural := A_CC_HDR_RSV0_O         + A_CC_HDR_RSV0_W;
    constant A_CC_HDR_RSV1_O         : natural := A_CC_HDR_AT_O           + A_CC_HDR_AT_W;
    constant A_CC_HDR_BYTE_CNT_O     : natural := A_CC_HDR_RSV1_O         + A_CC_HDR_RSV1_W;
    constant A_CC_HDR_LCK_RD_O       : natural := A_CC_HDR_BYTE_CNT_O     + A_CC_HDR_BYTE_CNT_W;
    constant A_CC_HDR_RSV2_O         : natural := A_CC_HDR_LCK_RD_O       + A_CC_HDR_LCK_RD_W;
    constant A_CC_HDR_DWORD_CNT_O    : natural := A_CC_HDR_RSV2_O         + A_CC_HDR_RSV2_W;
    constant A_CC_HDR_CPL_STATUS_O   : natural := A_CC_HDR_DWORD_CNT_O    + A_CC_HDR_DWORD_CNT_W;
    constant A_CC_HDR_POISONED_O     : natural := A_CC_HDR_CPL_STATUS_O   + A_CC_HDR_CPL_STATUS_W;
    constant A_CC_HDR_RSV3_O         : natural := A_CC_HDR_POISONED_O     + A_CC_HDR_POISONED_W;
    constant A_CC_HDR_REQUESTER_ID_O : natural := A_CC_HDR_RSV3_O         + A_CC_HDR_RSV3_W;
    constant A_CC_HDR_TAG_O          : natural := A_CC_HDR_REQUESTER_ID_O + A_CC_HDR_REQUESTER_ID_W;
    constant A_CC_HDR_COMPLETER_ID_O : natural := A_CC_HDR_TAG_O          + A_CC_HDR_TAG_W;
    constant A_CC_HDR_CPL_ID_EN_O    : natural := A_CC_HDR_COMPLETER_ID_O + A_CC_HDR_COMPLETER_ID_W;
    constant A_CC_HDR_TC_O           : natural := A_CC_HDR_CPL_ID_EN_O    + A_CC_HDR_CPL_ID_EN_W;
    constant A_CC_HDR_NO_SNOOP_O     : natural := A_CC_HDR_TC_O           + A_CC_HDR_TC_W;
    constant A_CC_HDR_RLX_ORD_O      : natural := A_CC_HDR_NO_SNOOP_O     + A_CC_HDR_NO_SNOOP_W;
    constant A_CC_HDR_ID_ORD_O       : natural := A_CC_HDR_RLX_ORD_O      + A_CC_HDR_RLX_ORD_W;
    constant A_CC_HDR_FORCE_ECRC_O   : natural := A_CC_HDR_ID_ORD_O       + A_CC_HDR_ID_ORD_W;

    subtype A_CC_HDR_ADDR         is natural range A_CC_HDR_ADDR_O         + A_CC_HDR_ADDR_W         - 1 downto A_CC_HDR_ADDR_O;
    subtype A_CC_HDR_RSV0         is natural range A_CC_HDR_RSV0_O         + A_CC_HDR_RSV0_W         - 1 downto A_CC_HDR_RSV0_O;
    subtype A_CC_HDR_AT           is natural range A_CC_HDR_AT_O           + A_CC_HDR_AT_W           - 1 downto A_CC_HDR_AT_O;
    subtype A_CC_HDR_RSV1         is natural range A_CC_HDR_RSV1_O         + A_CC_HDR_RSV1_W         - 1 downto A_CC_HDR_RSV1_O;
    subtype A_CC_HDR_BYTE_CNT     is natural range A_CC_HDR_BYTE_CNT_O     + A_CC_HDR_BYTE_CNT_W     - 1 downto A_CC_HDR_BYTE_CNT_O;
    subtype A_CC_HDR_LCK_RD       is natural range A_CC_HDR_LCK_RD_O       + A_CC_HDR_LCK_RD_W       - 1 downto A_CC_HDR_LCK_RD_O;
    subtype A_CC_HDR_RSV2         is natural range A_CC_HDR_RSV2_O         + A_CC_HDR_RSV2_W         - 1 downto A_CC_HDR_RSV2_O;
    subtype A_CC_HDR_DWORD_CNT    is natural range A_CC_HDR_DWORD_CNT_O    + A_CC_HDR_DWORD_CNT_W    - 1 downto A_CC_HDR_DWORD_CNT_O;
    subtype A_CC_HDR_CPL_STATUS   is natural range A_CC_HDR_CPL_STATUS_O   + A_CC_HDR_CPL_STATUS_W   - 1 downto A_CC_HDR_CPL_STATUS_O;
    subtype A_CC_HDR_POISONED     is natural range A_CC_HDR_POISONED_O     + A_CC_HDR_POISONED_W     - 1 downto A_CC_HDR_POISONED_O;
    subtype A_CC_HDR_RSV3         is natural range A_CC_HDR_RSV3_O         + A_CC_HDR_RSV3_W         - 1 downto A_CC_HDR_RSV3_O;
    subtype A_CC_HDR_REQUESTER_ID is natural range A_CC_HDR_REQUESTER_ID_O + A_CC_HDR_REQUESTER_ID_W - 1 downto A_CC_HDR_REQUESTER_ID_O;
    subtype A_CC_HDR_TAG          is natural range A_CC_HDR_TAG_O          + A_CC_HDR_TAG_W          - 1 downto A_CC_HDR_TAG_O;
    subtype A_CC_HDR_COMPLETER_ID is natural range A_CC_HDR_COMPLETER_ID_O + A_CC_HDR_COMPLETER_ID_W - 1 downto A_CC_HDR_COMPLETER_ID_O;
    subtype A_CC_HDR_CPL_ID_EN    is natural range A_CC_HDR_CPL_ID_EN_O    + A_CC_HDR_CPL_ID_EN_W    - 1 downto A_CC_HDR_CPL_ID_EN_O;
    subtype A_CC_HDR_TC           is natural range A_CC_HDR_TC_O           + A_CC_HDR_TC_W           - 1 downto A_CC_HDR_TC_O;
    subtype A_CC_HDR_NO_SNOOP     is natural range A_CC_HDR_NO_SNOOP_O     + A_CC_HDR_NO_SNOOP_W     - 1 downto A_CC_HDR_NO_SNOOP_O;
    subtype A_CC_HDR_RLX_ORD      is natural range A_CC_HDR_RLX_ORD_O      + A_CC_HDR_RLX_ORD_W      - 1 downto A_CC_HDR_RLX_ORD_O;
    subtype A_CC_HDR_ID_ORD       is natural range A_CC_HDR_ID_ORD_O       + A_CC_HDR_ID_ORD_W       - 1 downto A_CC_HDR_ID_ORD_O;
    subtype A_CC_HDR_FORCE_ECRC   is natural range A_CC_HDR_FORCE_ECRC_O   + A_CC_HDR_FORCE_ECRC_W   - 1 downto A_CC_HDR_FORCE_ECRC_O;


    -- =============================================================================================
    -- Intel's Requester Request (RQ) header
    -- =============================================================================================
    -- Common fields
    constant I_RQ_HDR_DW_CNT_W       : natural := 10;
    constant I_RQ_HDR_RSV0_W         : natural := 2;
    constant I_RQ_HDR_NO_SNOOP_W     : natural := 1;
    constant I_RQ_HDR_RLX_ORD_W      : natural := 1;
    constant I_RQ_HDR_POISONED_W     : natural := 1;
    constant I_RQ_HDR_ECRC_W         : natural := 1;
    constant I_RQ_HDR_RSV1_W         : natural := 2;
    constant I_RQ_HDR_ID_ORD_W       : natural := 1;
    constant I_RQ_HDR_TAG8_W         : natural := 1;
    constant I_RQ_HDR_TC_W           : natural := 3;
    constant I_RQ_HDR_TAG9_W         : natural := 1;
    constant I_RQ_HDR_RSV2_W         : natural := 5;
    constant I_RQ_HDR_ADDR_LEN_W     : natural := 1;
    constant I_RQ_HDR_REQ_TYPE_W     : natural := 1;
    constant I_RQ_HDR_RSV3_W         : natural := 1;
    constant I_RQ_HDR_FBE_W          : natural := 4;
    constant I_RQ_HDR_LBE_W          : natural := 4;
    constant I_RQ_HDR_TAG_W          : natural := 8;
    constant I_RQ_HDR_REQUESTER_ID_W : natural := 8;
    constant I_RQ_HDR_RSV4_W         : natural := 2;

    -- Short header fields
    constant I_RQ_HDRS_RSV5_W        : natural := 2;
    constant I_RQ_HDRS_ADDR_LOW_W    : natural := 30;
    -- Long header fields
    constant I_RQ_HDRL_ADDR_HIGH_W   : natural := 32;
    constant I_RQ_HDRL_RSV5_W        : natural := 2;
    constant I_RQ_HDRL_ADDR_LOW_W    : natural := 30;

    constant I_RQ_HDR_DW_CNT_O       : natural := 0;
    constant I_RQ_HDR_RSV0_O         : natural := I_RQ_HDR_DW_CNT_O        + I_RQ_HDR_DW_CNT_W;
    constant I_RQ_HDR_NO_SNOOP_O     : natural := I_RQ_HDR_RSV0_O          + I_RQ_HDR_RSV0_W;
    constant I_RQ_HDR_RLX_ORD_O      : natural := I_RQ_HDR_NO_SNOOP_O      + I_RQ_HDR_NO_SNOOP_W;
    constant I_RQ_HDR_POISONED_O     : natural := I_RQ_HDR_RLX_ORD_O       + I_RQ_HDR_RLX_ORD_W;
    constant I_RQ_HDR_ECRC_O         : natural := I_RQ_HDR_POISONED_O      + I_RQ_HDR_POISONED_W;
    constant I_RQ_HDR_RSV1_O         : natural := I_RQ_HDR_ECRC_O          + I_RQ_HDR_ECRC_W;
    constant I_RQ_HDR_ID_ORD_O       : natural := I_RQ_HDR_RSV1_O          + I_RQ_HDR_RSV1_W;
    constant I_RQ_HDR_TAG8_O         : natural := I_RQ_HDR_ID_ORD_O        + I_RQ_HDR_ID_ORD_W;
    constant I_RQ_HDR_TC_O           : natural := I_RQ_HDR_TAG8_O          + I_RQ_HDR_TAG8_W;
    constant I_RQ_HDR_TAG9_O         : natural := I_RQ_HDR_TC_O            + I_RQ_HDR_TC_W;
    constant I_RQ_HDR_RSV2_O         : natural := I_RQ_HDR_TAG9_O          + I_RQ_HDR_TAG9_W;
    constant I_RQ_HDR_ADDR_LEN_O     : natural := I_RQ_HDR_RSV2_O          + I_RQ_HDR_RSV2_W;
    constant I_RQ_HDR_REQ_TYPE_O     : natural := I_RQ_HDR_ADDR_LEN_O      + I_RQ_HDR_ADDR_LEN_W;
    constant I_RQ_HDR_RSV3_O         : natural := I_RQ_HDR_REQ_TYPE_O      + I_RQ_HDR_REQ_TYPE_W;
    constant I_RQ_HDR_FBE_O          : natural := I_RQ_HDR_RSV3_O          + I_RQ_HDR_RSV3_W;
    constant I_RQ_HDR_LBE_O          : natural := I_RQ_HDR_FBE_O           + I_RQ_HDR_FBE_W;
    constant I_RQ_HDR_TAG_O          : natural := I_RQ_HDR_LBE_O           + I_RQ_HDR_LBE_W;
    constant I_RQ_HDR_REQUESTER_ID_O : natural := I_RQ_HDR_TAG_O           + I_RQ_HDR_TAG_W;
    constant I_RQ_HDR_RSV4_O         : natural := I_RQ_HDR_REQUESTER_ID_O  + I_RQ_HDR_REQUESTER_ID_W;

    constant I_RQ_HDRS_RSV5_O        : natural := I_RQ_HDR_RSV4_O          + I_RQ_HDR_RSV4_W;
    constant I_RQ_HDRS_ADDR_LOW_O    : natural := I_RQ_HDRS_RSV5_O         + I_RQ_HDRS_RSV5_W;

    constant I_RQ_HDRL_ADDR_HIGH_O   : natural := I_RQ_HDR_RSV4_O          + I_RQ_HDR_RSV4_W;
    constant I_RQ_HDRL_RSV5_O        : natural := I_RQ_HDRL_ADDR_HIGH_O    + I_RQ_HDRL_ADDR_HIGH_W;
    constant I_RQ_HDRL_ADDR_LOW_O    : natural := I_RQ_HDRL_RSV5_O         + I_RQ_HDRL_RSV5_W;

    subtype I_RQ_HDR_DW_CNT       is natural range I_RQ_HDR_DW_CNT_O        + I_RQ_HDR_DW_CNT_W        - 1 downto I_RQ_HDR_DW_CNT_O;
    subtype I_RQ_HDR_RSV0         is natural range I_RQ_HDR_RSV0_O          + I_RQ_HDR_RSV0_W          - 1 downto I_RQ_HDR_RSV0_O;
    subtype I_RQ_HDR_NO_SNOOP     is natural range I_RQ_HDR_NO_SNOOP_O      + I_RQ_HDR_NO_SNOOP_W      - 1 downto I_RQ_HDR_NO_SNOOP_O;
    subtype I_RQ_HDR_RLX_ORD      is natural range I_RQ_HDR_RLX_ORD_O       + I_RQ_HDR_RLX_ORD_W       - 1 downto I_RQ_HDR_RLX_ORD_O;
    subtype I_RQ_HDR_POISONED     is natural range I_RQ_HDR_POISONED_O      + I_RQ_HDR_POISONED_W      - 1 downto I_RQ_HDR_POISONED_O;
    subtype I_RQ_HDR_ECRC         is natural range I_RQ_HDR_ECRC_O          + I_RQ_HDR_ECRC_W          - 1 downto I_RQ_HDR_ECRC_O;
    subtype I_RQ_HDR_RSV1         is natural range I_RQ_HDR_RSV1_O          + I_RQ_HDR_RSV1_W          - 1 downto I_RQ_HDR_RSV1_O;
    subtype I_RQ_HDR_ID_ORD       is natural range I_RQ_HDR_ID_ORD_O        + I_RQ_HDR_ID_ORD_W        - 1 downto I_RQ_HDR_ID_ORD_O;
    subtype I_RQ_HDR_TAG8         is natural range I_RQ_HDR_TAG8_O          + I_RQ_HDR_TAG8_W          - 1 downto I_RQ_HDR_TAG8_O;
    subtype I_RQ_HDR_TC           is natural range I_RQ_HDR_TC_O            + I_RQ_HDR_TC_W            - 1 downto I_RQ_HDR_TC_O;
    subtype I_RQ_HDR_TAG9         is natural range I_RQ_HDR_TAG9_O          + I_RQ_HDR_TAG9_W          - 1 downto I_RQ_HDR_TAG9_O;
    subtype I_RQ_HDR_RSV2         is natural range I_RQ_HDR_RSV2_O          + I_RQ_HDR_RSV2_W          - 1 downto I_RQ_HDR_RSV2_O;
    subtype I_RQ_HDR_ADDR_LEN     is natural range I_RQ_HDR_ADDR_LEN_O      + I_RQ_HDR_ADDR_LEN_W      - 1 downto I_RQ_HDR_ADDR_LEN_O;
    subtype I_RQ_HDR_REQ_TYPE     is natural range I_RQ_HDR_REQ_TYPE_O      + I_RQ_HDR_REQ_TYPE_W      - 1 downto I_RQ_HDR_REQ_TYPE_O;
    subtype I_RQ_HDR_RSV3         is natural range I_RQ_HDR_RSV3_O          + I_RQ_HDR_RSV3_W          - 1 downto I_RQ_HDR_RSV3_O;
    subtype I_RQ_HDR_FBE          is natural range I_RQ_HDR_FBE_O           + I_RQ_HDR_FBE_W           - 1 downto I_RQ_HDR_FBE_O;
    subtype I_RQ_HDR_LBE          is natural range I_RQ_HDR_LBE_O           + I_RQ_HDR_LBE_W           - 1 downto I_RQ_HDR_LBE_O;
    subtype I_RQ_HDR_TAG          is natural range I_RQ_HDR_TAG_O           + I_RQ_HDR_TAG_W           - 1 downto I_RQ_HDR_TAG_O;
    subtype I_RQ_HDR_REQUESTER_ID is natural range I_RQ_HDR_REQUESTER_ID_O  + I_RQ_HDR_REQUESTER_ID_W  - 1 downto I_RQ_HDR_REQUESTER_ID_O;
    subtype I_RQ_HDR_RSV4         is natural range I_RQ_HDR_RSV4_O          + I_RQ_HDR_RSV4_W          - 1 downto I_RQ_HDR_RSV4_O;

    subtype I_RQ_HDRS_RSV5        is natural range I_RQ_HDRS_RSV5_O         + I_RQ_HDRS_RSV5_W         - 1 downto I_RQ_HDRS_RSV5_O;
    subtype I_RQ_HDRS_ADDR_LOW    is natural range I_RQ_HDRS_ADDR_LOW_O     + I_RQ_HDRS_ADDR_LOW_W     - 1 downto I_RQ_HDRS_ADDR_LOW_O;

    subtype I_RQ_HDRL_ADDR_HIGH   is natural range I_RQ_HDRL_ADDR_HIGH_O    + I_RQ_HDRL_ADDR_HIGH_W    - 1 downto I_RQ_HDRL_ADDR_HIGH_O;
    subtype I_RQ_HDRL_RSV5        is natural range I_RQ_HDRL_RSV5_O         + I_RQ_HDRL_RSV5_W         - 1 downto I_RQ_HDRL_RSV5_O;
    subtype I_RQ_HDRL_ADDR_LOW    is natural range I_RQ_HDRL_ADDR_LOW_O     + I_RQ_HDRL_ADDR_LOW_W     - 1 downto I_RQ_HDRL_ADDR_LOW_O;
end package;

package body pcie_hdr_fields_pkg is
end package body;
