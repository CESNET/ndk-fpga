-- pcie_core_htile.vhd: PCIe module
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Denis Kurka <xkurka05@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture HTILE of PCIE_CORE is

    component htile_pcie_1x16 is
        port (
            REFCLK                    : in  std_logic                      := 'X';
            CORECLKOUT_HIP            : out std_logic;
            NPOR                      : in  std_logic                      := 'X';
            PIN_PERST                 : in  std_logic                      := 'X';
            RESET_STATUS              : out std_logic;
            SERDES_PLL_LOCKED         : out std_logic;
            PLD_CORE_READY            : in  std_logic                      := 'X';
            PLD_CLK_INUSE             : out std_logic;
            TESTIN_ZERO               : out std_logic;
            CLR_ST                    : out std_logic;
            NINIT_DONE                : in  std_logic                      := 'X';
            RX_ST_READY               : in  std_logic                      := 'X';
            RX_ST_SOP                 : out std_logic_vector(1 downto 0);
            RX_ST_EOP                 : out std_logic_vector(1 downto 0);
            RX_ST_DATA                : out std_logic_vector(511 downto 0);
            RX_ST_VALID               : out std_logic_vector(1 downto 0);
            RX_ST_EMPTY               : out std_logic_vector(5 downto 0);
            TX_ST_SOP                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            TX_ST_EOP                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            TX_ST_DATA                : in  std_logic_vector(511 downto 0) := (others => 'X');
            TX_ST_VALID               : in  std_logic_vector(1 downto 0)   := (others => 'X');
            TX_ST_ERR                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            TX_ST_READY               : out std_logic;
            RX_ST_BAR_RANGE           : out std_logic_vector(5 downto 0);
            TX_CDTS_TYPE              : out std_logic_vector(3 downto 0);
            TX_DATA_CDTS_CONSUMED     : out std_logic_vector(1 downto 0);
            TX_HDR_CDTS_CONSUMED      : out std_logic_vector(1 downto 0);
            TX_CDTS_DATA_VALUE        : out std_logic_vector(1 downto 0);
            TX_CPLD_CDTS              : out std_logic_vector(11 downto 0);
            TX_PD_CDTS                : out std_logic_vector(11 downto 0);
            TX_NPD_CDTS               : out std_logic_vector(11 downto 0);
            TX_CPLH_CDTS              : out std_logic_vector(7 downto 0);
            TX_PH_CDTS                : out std_logic_vector(7 downto 0);
            TX_NPH_CDTS               : out std_logic_vector(7 downto 0);
            APP_MSI_REQ               : in  std_logic                      := 'X';
            APP_MSI_ACK               : out std_logic;
            APP_MSI_TC                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            APP_MSI_NUM               : in  std_logic_vector(4 downto 0)   := (others => 'X');
            APP_INT_STS               : in  std_logic_vector(3 downto 0)   := (others => 'X');
            APP_MSI_FUNC_NUM          : in  std_logic_vector(1 downto 0)   := (others => 'X');
            INT_STATUS                : out std_logic_vector(10 downto 0);
            INT_STATUS_COMMON         : out std_logic_vector(2 downto 0);
            DERR_COR_EXT_RPL          : out std_logic;
            DERR_RPL                  : out std_logic;
            DERR_COR_EXT_RCV          : out std_logic;
            DERR_UNCOR_EXT_RCV        : out std_logic;
            RX_PAR_ERR                : out std_logic;
            TX_PAR_ERR                : out std_logic;
            LTSSMSTATE                : out std_logic_vector(5 downto 0);
            LINK_UP                   : out std_logic;
            LANE_ACT                  : out std_logic_vector(4 downto 0);
            -- flr_pf_done               : in  std_logic                      := 'X';             -- flr_pf_done
            -- flr_pf_active             : out std_logic;                                         -- flr_pf_active
            TL_CFG_FUNC               : out std_logic_vector(1 downto 0);
            TL_CFG_ADD                : out std_logic_vector(3 downto 0);
            TL_CFG_CTL                : out std_logic_vector(31 downto 0);
            APP_ERR_VALID             : in  std_logic                      := 'X';
            APP_ERR_HDR               : in  std_logic_vector(31 downto 0)  := (others => 'X');
            APP_ERR_INFO              : in  std_logic_vector(10 downto 0)  := (others => 'X');
            APP_ERR_FUNC_NUM          : in  std_logic_vector(1 downto 0)   := (others => 'X');
            TEST_IN                   : in  std_logic_vector(66 downto 0)  := (others => 'X');
            SIMU_MODE_PIPE            : in  std_logic                      := 'X';
            CURRENTSPEED              : out std_logic_vector(1 downto 0);
            CEB_ACK                   : in  std_logic                      := 'X';
            CEB_DIN                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            CEB_ADDR                  : out std_logic_vector(11 downto 0);
            CEB_REQ                   : out std_logic;
            CEB_DOUT                  : out std_logic_vector(31 downto 0);
            CEB_WR                    : out std_logic_vector(3 downto 0);
            CEB_CDM_CONVERT_DATA      : in  std_logic_vector(31 downto 0)  := (others => 'X');
            CEB_FUNC_NUM              : out std_logic_vector(1 downto 0);
            SIM_PIPE_PCLK_IN          : in  std_logic                      := 'X';
            SIM_PIPE_RATE             : out std_logic_vector(1 downto 0);
            SIM_LTSSMSTATE            : out std_logic_vector(5 downto 0);
            TXDATA0                   : out std_logic_vector(31 downto 0);
            TXDATA1                   : out std_logic_vector(31 downto 0);
            TXDATA2                   : out std_logic_vector(31 downto 0);
            TXDATA3                   : out std_logic_vector(31 downto 0);
            TXDATA4                   : out std_logic_vector(31 downto 0);
            TXDATA5                   : out std_logic_vector(31 downto 0);
            TXDATA6                   : out std_logic_vector(31 downto 0);
            TXDATA7                   : out std_logic_vector(31 downto 0);
            TXDATA8                   : out std_logic_vector(31 downto 0);
            TXDATA9                   : out std_logic_vector(31 downto 0);
            TXDATA10                  : out std_logic_vector(31 downto 0);
            TXDATA11                  : out std_logic_vector(31 downto 0);
            TXDATA12                  : out std_logic_vector(31 downto 0);
            TXDATA13                  : out std_logic_vector(31 downto 0);
            TXDATA14                  : out std_logic_vector(31 downto 0);
            TXDATA15                  : out std_logic_vector(31 downto 0);
            TXDATAK0                  : out std_logic_vector(3 downto 0);
            TXDATAK1                  : out std_logic_vector(3 downto 0);
            TXDATAK2                  : out std_logic_vector(3 downto 0);
            TXDATAK3                  : out std_logic_vector(3 downto 0);
            TXDATAK4                  : out std_logic_vector(3 downto 0);
            TXDATAK5                  : out std_logic_vector(3 downto 0);
            TXDATAK6                  : out std_logic_vector(3 downto 0);
            TXDATAK7                  : out std_logic_vector(3 downto 0);
            TXDATAK8                  : out std_logic_vector(3 downto 0);
            TXDATAK9                  : out std_logic_vector(3 downto 0);
            TXDATAK10                 : out std_logic_vector(3 downto 0);
            TXDATAK11                 : out std_logic_vector(3 downto 0);
            TXDATAK12                 : out std_logic_vector(3 downto 0);
            TXDATAK13                 : out std_logic_vector(3 downto 0);
            TXDATAK14                 : out std_logic_vector(3 downto 0);
            TXDATAK15                 : out std_logic_vector(3 downto 0);
            TXCOMPL0                  : out std_logic;
            TXCOMPL1                  : out std_logic;
            TXCOMPL2                  : out std_logic;
            TXCOMPL3                  : out std_logic;
            TXCOMPL4                  : out std_logic;
            TXCOMPL5                  : out std_logic;
            TXCOMPL6                  : out std_logic;
            TXCOMPL7                  : out std_logic;
            TXCOMPL8                  : out std_logic;
            TXCOMPL9                  : out std_logic;
            TXCOMPL10                 : out std_logic;
            TXCOMPL11                 : out std_logic;
            TXCOMPL12                 : out std_logic;
            TXCOMPL13                 : out std_logic;
            TXCOMPL14                 : out std_logic;
            TXCOMPL15                 : out std_logic;
            TXELECIDLE0               : out std_logic;
            TXELECIDLE1               : out std_logic;
            TXELECIDLE2               : out std_logic;
            TXELECIDLE3               : out std_logic;
            TXELECIDLE4               : out std_logic;
            TXELECIDLE5               : out std_logic;
            TXELECIDLE6               : out std_logic;
            TXELECIDLE7               : out std_logic;
            TXELECIDLE8               : out std_logic;
            TXELECIDLE9               : out std_logic;
            TXELECIDLE10              : out std_logic;
            TXELECIDLE11              : out std_logic;
            TXELECIDLE12              : out std_logic;
            TXELECIDLE13              : out std_logic;
            TXELECIDLE14              : out std_logic;
            TXELECIDLE15              : out std_logic;
            TXDETECTRX0               : out std_logic;
            TXDETECTRX1               : out std_logic;
            TXDETECTRX2               : out std_logic;
            TXDETECTRX3               : out std_logic;
            TXDETECTRX4               : out std_logic;
            TXDETECTRX5               : out std_logic;
            TXDETECTRX6               : out std_logic;
            TXDETECTRX7               : out std_logic;
            TXDETECTRX8               : out std_logic;
            TXDETECTRX9               : out std_logic;
            TXDETECTRX10              : out std_logic;
            TXDETECTRX11              : out std_logic;
            TXDETECTRX12              : out std_logic;
            TXDETECTRX13              : out std_logic;
            TXDETECTRX14              : out std_logic;
            TXDETECTRX15              : out std_logic;
            POWERDOWN0                : out std_logic_vector(1 downto 0);
            POWERDOWN1                : out std_logic_vector(1 downto 0);
            POWERDOWN2                : out std_logic_vector(1 downto 0);
            POWERDOWN3                : out std_logic_vector(1 downto 0);
            POWERDOWN4                : out std_logic_vector(1 downto 0);
            POWERDOWN5                : out std_logic_vector(1 downto 0);
            POWERDOWN6                : out std_logic_vector(1 downto 0);
            POWERDOWN7                : out std_logic_vector(1 downto 0);
            POWERDOWN8                : out std_logic_vector(1 downto 0);
            POWERDOWN9                : out std_logic_vector(1 downto 0);
            POWERDOWN10               : out std_logic_vector(1 downto 0);
            POWERDOWN11               : out std_logic_vector(1 downto 0);
            POWERDOWN12               : out std_logic_vector(1 downto 0);
            POWERDOWN13               : out std_logic_vector(1 downto 0);
            POWERDOWN14               : out std_logic_vector(1 downto 0);
            POWERDOWN15               : out std_logic_vector(1 downto 0);
            TXMARGIN0                 : out std_logic_vector(2 downto 0);
            TXMARGIN1                 : out std_logic_vector(2 downto 0);
            TXMARGIN2                 : out std_logic_vector(2 downto 0);
            TXMARGIN3                 : out std_logic_vector(2 downto 0);
            TXMARGIN4                 : out std_logic_vector(2 downto 0);
            TXMARGIN5                 : out std_logic_vector(2 downto 0);
            TXMARGIN6                 : out std_logic_vector(2 downto 0);
            TXMARGIN7                 : out std_logic_vector(2 downto 0);
            TXMARGIN8                 : out std_logic_vector(2 downto 0);
            TXMARGIN9                 : out std_logic_vector(2 downto 0);
            TXMARGIN10                : out std_logic_vector(2 downto 0);
            TXMARGIN11                : out std_logic_vector(2 downto 0);
            TXMARGIN12                : out std_logic_vector(2 downto 0);
            TXMARGIN13                : out std_logic_vector(2 downto 0);
            TXMARGIN14                : out std_logic_vector(2 downto 0);
            TXMARGIN15                : out std_logic_vector(2 downto 0);
            TXDEEMPH0                 : out std_logic;
            TXDEEMPH1                 : out std_logic;
            TXDEEMPH2                 : out std_logic;
            TXDEEMPH3                 : out std_logic;
            TXDEEMPH4                 : out std_logic;
            TXDEEMPH5                 : out std_logic;
            TXDEEMPH6                 : out std_logic;
            TXDEEMPH7                 : out std_logic;
            TXDEEMPH8                 : out std_logic;
            TXDEEMPH9                 : out std_logic;
            TXDEEMPH10                : out std_logic;
            TXDEEMPH11                : out std_logic;
            TXDEEMPH12                : out std_logic;
            TXDEEMPH13                : out std_logic;
            TXDEEMPH14                : out std_logic;
            TXDEEMPH15                : out std_logic;
            TXSWING0                  : out std_logic;
            TXSWING1                  : out std_logic;
            TXSWING2                  : out std_logic;
            TXSWING3                  : out std_logic;
            TXSWING4                  : out std_logic;
            TXSWING5                  : out std_logic;
            TXSWING6                  : out std_logic;
            TXSWING7                  : out std_logic;
            TXSWING8                  : out std_logic;
            TXSWING9                  : out std_logic;
            TXSWING10                 : out std_logic;
            TXSWING11                 : out std_logic;
            TXSWING12                 : out std_logic;
            TXSWING13                 : out std_logic;
            TXSWING14                 : out std_logic;
            TXSWING15                 : out std_logic;
            TXSYNCHD0                 : out std_logic_vector(1 downto 0);
            TXSYNCHD1                 : out std_logic_vector(1 downto 0);
            TXSYNCHD2                 : out std_logic_vector(1 downto 0);
            TXSYNCHD3                 : out std_logic_vector(1 downto 0);
            TXSYNCHD4                 : out std_logic_vector(1 downto 0);
            TXSYNCHD5                 : out std_logic_vector(1 downto 0);
            TXSYNCHD6                 : out std_logic_vector(1 downto 0);
            TXSYNCHD7                 : out std_logic_vector(1 downto 0);
            TXSYNCHD8                 : out std_logic_vector(1 downto 0);
            TXSYNCHD9                 : out std_logic_vector(1 downto 0);
            TXSYNCHD10                : out std_logic_vector(1 downto 0);
            TXSYNCHD11                : out std_logic_vector(1 downto 0);
            TXSYNCHD12                : out std_logic_vector(1 downto 0);
            TXSYNCHD13                : out std_logic_vector(1 downto 0);
            TXSYNCHD14                : out std_logic_vector(1 downto 0);
            TXSYNCHD15                : out std_logic_vector(1 downto 0);
            TXBLKST0                  : out std_logic;
            TXBLKST1                  : out std_logic;
            TXBLKST2                  : out std_logic;
            TXBLKST3                  : out std_logic;
            TXBLKST4                  : out std_logic;
            TXBLKST5                  : out std_logic;
            TXBLKST6                  : out std_logic;
            TXBLKST7                  : out std_logic;
            TXBLKST8                  : out std_logic;
            TXBLKST9                  : out std_logic;
            TXBLKST10                 : out std_logic;
            TXBLKST11                 : out std_logic;
            TXBLKST12                 : out std_logic;
            TXBLKST13                 : out std_logic;
            TXBLKST14                 : out std_logic;
            TXBLKST15                 : out std_logic;
            TXDATASKIP0               : out std_logic;
            TXDATASKIP1               : out std_logic;
            TXDATASKIP2               : out std_logic;
            TXDATASKIP3               : out std_logic;
            TXDATASKIP4               : out std_logic;
            TXDATASKIP5               : out std_logic;
            TXDATASKIP6               : out std_logic;
            TXDATASKIP7               : out std_logic;
            TXDATASKIP8               : out std_logic;
            TXDATASKIP9               : out std_logic;
            TXDATASKIP10              : out std_logic;
            TXDATASKIP11              : out std_logic;
            TXDATASKIP12              : out std_logic;
            TXDATASKIP13              : out std_logic;
            TXDATASKIP14              : out std_logic;
            TXDATASKIP15              : out std_logic;
            RATE0                     : out std_logic_vector(1 downto 0);
            RATE1                     : out std_logic_vector(1 downto 0);
            RATE2                     : out std_logic_vector(1 downto 0);
            RATE3                     : out std_logic_vector(1 downto 0);
            RATE4                     : out std_logic_vector(1 downto 0);
            RATE5                     : out std_logic_vector(1 downto 0);
            RATE6                     : out std_logic_vector(1 downto 0);
            RATE7                     : out std_logic_vector(1 downto 0);
            RATE8                     : out std_logic_vector(1 downto 0);
            RATE9                     : out std_logic_vector(1 downto 0);
            RATE10                    : out std_logic_vector(1 downto 0);
            RATE11                    : out std_logic_vector(1 downto 0);
            RATE12                    : out std_logic_vector(1 downto 0);
            RATE13                    : out std_logic_vector(1 downto 0);
            RATE14                    : out std_logic_vector(1 downto 0);
            RATE15                    : out std_logic_vector(1 downto 0);
            RXPOLARITY0               : out std_logic;
            RXPOLARITY1               : out std_logic;
            RXPOLARITY2               : out std_logic;
            RXPOLARITY3               : out std_logic;
            RXPOLARITY4               : out std_logic;
            RXPOLARITY5               : out std_logic;
            RXPOLARITY6               : out std_logic;
            RXPOLARITY7               : out std_logic;
            RXPOLARITY8               : out std_logic;
            RXPOLARITY9               : out std_logic;
            RXPOLARITY10              : out std_logic;
            RXPOLARITY11              : out std_logic;
            RXPOLARITY12              : out std_logic;
            RXPOLARITY13              : out std_logic;
            RXPOLARITY14              : out std_logic;
            RXPOLARITY15              : out std_logic;
            CURRENTRXPRESET0          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET1          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET2          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET3          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET4          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET5          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET6          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET7          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET8          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET9          : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET10         : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET11         : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET12         : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET13         : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET14         : out std_logic_vector(2 downto 0);
            CURRENTRXPRESET15         : out std_logic_vector(2 downto 0);
            CURRENTCOEFF0             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF1             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF2             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF3             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF4             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF5             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF6             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF7             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF8             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF9             : out std_logic_vector(17 downto 0);
            CURRENTCOEFF10            : out std_logic_vector(17 downto 0);
            CURRENTCOEFF11            : out std_logic_vector(17 downto 0);
            CURRENTCOEFF12            : out std_logic_vector(17 downto 0);
            CURRENTCOEFF13            : out std_logic_vector(17 downto 0);
            CURRENTCOEFF14            : out std_logic_vector(17 downto 0);
            CURRENTCOEFF15            : out std_logic_vector(17 downto 0);
            RXEQEVAL0                 : out std_logic;
            RXEQEVAL1                 : out std_logic;
            RXEQEVAL2                 : out std_logic;
            RXEQEVAL3                 : out std_logic;
            RXEQEVAL4                 : out std_logic;
            RXEQEVAL5                 : out std_logic;
            RXEQEVAL6                 : out std_logic;
            RXEQEVAL7                 : out std_logic;
            RXEQEVAL8                 : out std_logic;
            RXEQEVAL9                 : out std_logic;
            RXEQEVAL10                : out std_logic;
            RXEQEVAL11                : out std_logic;
            RXEQEVAL12                : out std_logic;
            RXEQEVAL13                : out std_logic;
            RXEQEVAL14                : out std_logic;
            RXEQEVAL15                : out std_logic;
            RXEQINPROGRESS0           : out std_logic;
            RXEQINPROGRESS1           : out std_logic;
            RXEQINPROGRESS2           : out std_logic;
            RXEQINPROGRESS3           : out std_logic;
            RXEQINPROGRESS4           : out std_logic;
            RXEQINPROGRESS5           : out std_logic;
            RXEQINPROGRESS6           : out std_logic;
            RXEQINPROGRESS7           : out std_logic;
            RXEQINPROGRESS8           : out std_logic;
            RXEQINPROGRESS9           : out std_logic;
            RXEQINPROGRESS10          : out std_logic;
            RXEQINPROGRESS11          : out std_logic;
            RXEQINPROGRESS12          : out std_logic;
            RXEQINPROGRESS13          : out std_logic;
            RXEQINPROGRESS14          : out std_logic;
            RXEQINPROGRESS15          : out std_logic;
            INVALIDREQ0               : out std_logic;
            INVALIDREQ1               : out std_logic;
            INVALIDREQ2               : out std_logic;
            INVALIDREQ3               : out std_logic;
            INVALIDREQ4               : out std_logic;
            INVALIDREQ5               : out std_logic;
            INVALIDREQ6               : out std_logic;
            INVALIDREQ7               : out std_logic;
            INVALIDREQ8               : out std_logic;
            INVALIDREQ9               : out std_logic;
            INVALIDREQ10              : out std_logic;
            INVALIDREQ11              : out std_logic;
            INVALIDREQ12              : out std_logic;
            INVALIDREQ13              : out std_logic;
            INVALIDREQ14              : out std_logic;
            INVALIDREQ15              : out std_logic;
            RXDATA0                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA1                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA2                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA3                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA4                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA5                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA6                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA7                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA8                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA9                   : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA10                  : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA11                  : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA12                  : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA13                  : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA14                  : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATA15                  : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RXDATAK0                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK1                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK2                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK3                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK4                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK5                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK6                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK7                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK8                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK9                  : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK10                 : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK11                 : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK12                 : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK13                 : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK14                 : in  std_logic_vector(3 downto 0)   := (others => 'X');
            RXDATAK15                 : in  std_logic_vector(3 downto 0)   := (others => 'X');
            PHYSTATUS0                : in  std_logic                      := 'X';
            PHYSTATUS1                : in  std_logic                      := 'X';
            PHYSTATUS2                : in  std_logic                      := 'X';
            PHYSTATUS3                : in  std_logic                      := 'X';
            PHYSTATUS4                : in  std_logic                      := 'X';
            PHYSTATUS5                : in  std_logic                      := 'X';
            PHYSTATUS6                : in  std_logic                      := 'X';
            PHYSTATUS7                : in  std_logic                      := 'X';
            PHYSTATUS8                : in  std_logic                      := 'X';
            PHYSTATUS9                : in  std_logic                      := 'X';
            PHYSTATUS10               : in  std_logic                      := 'X';
            PHYSTATUS11               : in  std_logic                      := 'X';
            PHYSTATUS12               : in  std_logic                      := 'X';
            PHYSTATUS13               : in  std_logic                      := 'X';
            PHYSTATUS14               : in  std_logic                      := 'X';
            PHYSTATUS15               : in  std_logic                      := 'X';
            RXVALID0                  : in  std_logic                      := 'X';
            RXVALID1                  : in  std_logic                      := 'X';
            RXVALID2                  : in  std_logic                      := 'X';
            RXVALID3                  : in  std_logic                      := 'X';
            RXVALID4                  : in  std_logic                      := 'X';
            RXVALID5                  : in  std_logic                      := 'X';
            RXVALID6                  : in  std_logic                      := 'X';
            RXVALID7                  : in  std_logic                      := 'X';
            RXVALID8                  : in  std_logic                      := 'X';
            RXVALID9                  : in  std_logic                      := 'X';
            RXVALID10                 : in  std_logic                      := 'X';
            RXVALID11                 : in  std_logic                      := 'X';
            RXVALID12                 : in  std_logic                      := 'X';
            RXVALID13                 : in  std_logic                      := 'X';
            RXVALID14                 : in  std_logic                      := 'X';
            RXVALID15                 : in  std_logic                      := 'X';
            RXSTATUS0                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS1                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS2                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS3                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS4                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS5                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS6                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS7                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS8                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS9                 : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS10                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS11                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS12                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS13                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS14                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXSTATUS15                : in  std_logic_vector(2 downto 0)   := (others => 'X');
            RXELECIDLE0               : in  std_logic                      := 'X';
            RXELECIDLE1               : in  std_logic                      := 'X';
            RXELECIDLE2               : in  std_logic                      := 'X';
            RXELECIDLE3               : in  std_logic                      := 'X';
            RXELECIDLE4               : in  std_logic                      := 'X';
            RXELECIDLE5               : in  std_logic                      := 'X';
            RXELECIDLE6               : in  std_logic                      := 'X';
            RXELECIDLE7               : in  std_logic                      := 'X';
            RXELECIDLE8               : in  std_logic                      := 'X';
            RXELECIDLE9               : in  std_logic                      := 'X';
            RXELECIDLE10              : in  std_logic                      := 'X';
            RXELECIDLE11              : in  std_logic                      := 'X';
            RXELECIDLE12              : in  std_logic                      := 'X';
            RXELECIDLE13              : in  std_logic                      := 'X';
            RXELECIDLE14              : in  std_logic                      := 'X';
            RXELECIDLE15              : in  std_logic                      := 'X';
            RXSYNCHD0                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD1                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD2                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD3                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD4                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD5                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD6                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD7                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD8                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD9                 : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD10                : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD11                : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD12                : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD13                : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD14                : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXSYNCHD15                : in  std_logic_vector(1 downto 0)   := (others => 'X');
            RXBLKST0                  : in  std_logic                      := 'X';
            RXBLKST1                  : in  std_logic                      := 'X';
            RXBLKST2                  : in  std_logic                      := 'X';
            RXBLKST3                  : in  std_logic                      := 'X';
            RXBLKST4                  : in  std_logic                      := 'X';
            RXBLKST5                  : in  std_logic                      := 'X';
            RXBLKST6                  : in  std_logic                      := 'X';
            RXBLKST7                  : in  std_logic                      := 'X';
            RXBLKST8                  : in  std_logic                      := 'X';
            RXBLKST9                  : in  std_logic                      := 'X';
            RXBLKST10                 : in  std_logic                      := 'X';
            RXBLKST11                 : in  std_logic                      := 'X';
            RXBLKST12                 : in  std_logic                      := 'X';
            RXBLKST13                 : in  std_logic                      := 'X';
            RXBLKST14                 : in  std_logic                      := 'X';
            RXBLKST15                 : in  std_logic                      := 'X';
            RXDATASKIP0               : in  std_logic                      := 'X';
            RXDATASKIP1               : in  std_logic                      := 'X';
            RXDATASKIP2               : in  std_logic                      := 'X';
            RXDATASKIP3               : in  std_logic                      := 'X';
            RXDATASKIP4               : in  std_logic                      := 'X';
            RXDATASKIP5               : in  std_logic                      := 'X';
            RXDATASKIP6               : in  std_logic                      := 'X';
            RXDATASKIP7               : in  std_logic                      := 'X';
            RXDATASKIP8               : in  std_logic                      := 'X';
            RXDATASKIP9               : in  std_logic                      := 'X';
            RXDATASKIP10              : in  std_logic                      := 'X';
            RXDATASKIP11              : in  std_logic                      := 'X';
            RXDATASKIP12              : in  std_logic                      := 'X';
            RXDATASKIP13              : in  std_logic                      := 'X';
            RXDATASKIP14              : in  std_logic                      := 'X';
            RXDATASKIP15              : in  std_logic                      := 'X';
            DIRFEEDBACK0              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK1              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK2              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK3              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK4              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK5              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK6              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK7              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK8              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK9              : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK10             : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK11             : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK12             : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK13             : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK14             : in  std_logic_vector(5 downto 0)   := (others => 'X');
            DIRFEEDBACK15             : in  std_logic_vector(5 downto 0)   := (others => 'X');
            SIM_PIPE_MASK_TX_PLL_LOCK : in  std_logic                      := 'X';
            RX_IN0                    : in  std_logic                      := 'X';
            RX_IN1                    : in  std_logic                      := 'X';
            RX_IN2                    : in  std_logic                      := 'X';
            RX_IN3                    : in  std_logic                      := 'X';
            RX_IN4                    : in  std_logic                      := 'X';
            RX_IN5                    : in  std_logic                      := 'X';
            RX_IN6                    : in  std_logic                      := 'X';
            RX_IN7                    : in  std_logic                      := 'X';
            RX_IN8                    : in  std_logic                      := 'X';
            RX_IN9                    : in  std_logic                      := 'X';
            RX_IN10                   : in  std_logic                      := 'X';
            RX_IN11                   : in  std_logic                      := 'X';
            RX_IN12                   : in  std_logic                      := 'X';
            RX_IN13                   : in  std_logic                      := 'X';
            RX_IN14                   : in  std_logic                      := 'X';
            RX_IN15                   : in  std_logic                      := 'X';
            TX_OUT0                   : out std_logic;
            TX_OUT1                   : out std_logic;
            TX_OUT2                   : out std_logic;
            TX_OUT3                   : out std_logic;
            TX_OUT4                   : out std_logic;
            TX_OUT5                   : out std_logic;
            TX_OUT6                   : out std_logic;
            TX_OUT7                   : out std_logic;
            TX_OUT8                   : out std_logic;
            TX_OUT9                   : out std_logic;
            TX_OUT10                  : out std_logic;
            TX_OUT11                  : out std_logic;
            TX_OUT12                  : out std_logic;
            TX_OUT13                  : out std_logic;
            TX_OUT14                  : out std_logic;
            TX_OUT15                  : out std_logic;
            PM_LINKST_IN_L1           : out std_logic;
            PM_LINKST_IN_L0S          : out std_logic;
            PM_STATE                  : out std_logic_vector(2 downto 0);
            PM_DSTATE                 : out std_logic_vector(2 downto 0);
            APPS_PM_XMT_PME           : in  std_logic                      := 'X';
            APPS_READY_ENTR_L23       : in  std_logic                      := 'X';
            APPS_PM_XMT_TURNOFF       : in  std_logic                      := 'X';
            APP_INIT_RST              : in  std_logic                      := 'X';
            APP_XFER_PENDING          : in  std_logic                      := 'X'
        -- flr_rcvd_vf               : out std_logic;                                         -- flr_rcvd_vf
        -- flr_rcvd_pf_num           : out std_logic_vector(0 downto 0);                      -- flr_rcvd_pf_num
        -- flr_rcvd_vf_num           : out std_logic_vector(0 downto 0);                      -- flr_rcvd_vf_num
        -- flr_completed_vf          : in  std_logic                      := 'X';             -- flr_completed_vf
        -- flr_completed_pf_num      : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- flr_completed_pf_num
        -- flr_completed_vf_num      : in  std_logic_vector(0 downto 0)   := (others => 'X')  -- flr_completed_vf_num
        );
    end component;

    constant PCIE_HIPS              : natural := tsel(ENDPOINT_MODE = 0,PCIE_ENDPOINTS,PCIE_ENDPOINTS/2);
    constant CQ_FIFO_ITEMS          : natural := 512;
    constant VSEC_BASE_ADDRESS      : integer := 16#D00#;

    signal pcie_ceb_ack  : std_logic;
    signal pcie_ceb_din  : std_logic_vector(31 downto 0);
    signal pcie_ceb_addr : std_logic_vector(12-1 downto 0);
    signal pcie_ceb_req  : std_logic;
    signal pcie_ceb_dout : std_logic_vector(31 downto 0);
    signal pcie_ceb_wr   : std_logic_vector(3 downto 0);

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_reset_status        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_hip_clk             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_init_done_n         : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);

    signal pcie_avst_down_data      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_down_sop       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_eop       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_empty     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_bar_range : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_valid     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_ready     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '1');
    signal pcie_avst_up_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_up_sop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_eop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_error       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_valid       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal pcie_avst_up_ready       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_link_up_comb        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_link_up_reg         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

begin

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_core_i : component htile_pcie_1x16
    port map (
        refclk                    => PCIE_SYSCLK_P(0),                                      --         refclk.clk
        coreclkout_hip            => pcie_hip_clk(0),                                       -- coreclkout_hip.clk
        npor                      => PCIE_SYSRST_N(0),                                      --           npor.npor
        pin_perst                 => PCIE_SYSRST_N(0),                                      --               .pin_perst
        reset_status              => pcie_reset_status(0),                                  --        hip_rst.reset_status
        serdes_pll_locked         => open,                                                  --               .serdes_pll_locked
        pld_core_ready            => '1',                                                   --               .pld_core_ready
        pld_clk_inuse             => open,                                                  --               .pld_clk_inuse
        testin_zero               => open,                                                  --               .testin_zero
        clr_st                    => open,                                                  --         clr_st.reset
        ninit_done                => pcie_init_done_n(0),                                   --     ninit_done.ninit_done
        rx_st_ready               => pcie_avst_down_ready(0),                               --          rx_st.ready
        rx_st_sop                 => pcie_avst_down_sop(0),                                 --               .startofpacket
        rx_st_eop                 => pcie_avst_down_eop(0),                                 --               .endofpacket
        rx_st_data                => pcie_avst_down_data(0)(512-1 downto 0),                --               .data
        rx_st_valid               => pcie_avst_down_valid(0)(2-1 downto 0),                 --               .valid
        rx_st_empty               => pcie_avst_down_empty(0)(6-1 downto 0),                 --               .empty
        tx_st_sop                 => pcie_avst_up_sop(0),                                   --          tx_st.startofpacket
        tx_st_eop                 => pcie_avst_up_eop(0),                                   --               .endofpacket
        tx_st_data                => pcie_avst_up_data(0)(512-1 downto 0),                  --               .data
        tx_st_valid               => pcie_avst_up_valid(0),                                 --               .valid
        tx_st_err                 => pcie_avst_up_error(0),                                 --               .error
        tx_st_ready               => pcie_avst_up_ready(0),                                 --               .ready
        rx_st_bar_range           => pcie_avst_down_bar_range(0),                           --         rx_bar.rx_st_bar_range
        tx_cdts_type              => open,                                                  --        tx_cred.tx_cdts_type
        tx_data_cdts_consumed     => open,                                                  --               .tx_data_cdts_consumed
        tx_hdr_cdts_consumed      => open,                                                  --               .tx_hdr_cdts_consumed
        tx_cdts_data_value        => open,                                                  --               .tx_cdts_data_value
        tx_cpld_cdts              => open,                                                  --               .tx_cpld_cdts
        tx_pd_cdts                => open,                                                  --               .tx_pd_cdts
        tx_npd_cdts               => open,                                                  --               .tx_npd_cdts
        tx_cplh_cdts              => open,                                                  --               .tx_cplh_cdts
        tx_ph_cdts                => open,                                                  --               .tx_ph_cdts
        tx_nph_cdts               => open,                                                  --               .tx_nph_cdts
        app_msi_req               => '0',                                                   --        int_msi.app_msi_req
        app_msi_ack               => open,                                                  --               .app_msi_ack
        app_msi_tc                => (others => '0'),                                       --               .app_msi_tc
        app_msi_num               => (others => '0'),                                       --               .app_msi_num
        app_int_sts               => (others => '0'),                                       --               .app_int_sts
        app_msi_func_num          => (others => '0'),                                       --               .app_msi_func_num
        int_status                => open,                                                  --     hip_status.int_status
        int_status_common         => open,                                                  --               .int_status_common
        derr_cor_ext_rpl          => open,                                                  --               .derr_cor_ext_rpl
        derr_rpl                  => open,                                                  --               .derr_rpl
        derr_cor_ext_rcv          => open,                                                  --               .derr_cor_ext_rcv
        derr_uncor_ext_rcv        => open,                                                  --               .derr_uncor_ext_rcv
        rx_par_err                => open,                                                  --               .rx_par_err
        tx_par_err                => open,                                                  --               .tx_par_err
        ltssmstate                => open,                                                  --               .ltssmstate
        link_up                   => pcie_link_up_comb(0),                                  --               .link_up
        lane_act                  => open,                                                  --               .lane_act
        -- flr_pf_done               => '0',               --       flr_ctrl.flr_pf_done
        -- flr_pf_active             => open,             --               .flr_pf_active
        tl_cfg_func               => open,                                                  --      config_tl.tl_cfg_func
        tl_cfg_add                => open,                                                  --               .tl_cfg_add
        tl_cfg_ctl                => open,                                                  --               .tl_cfg_ctl
        app_err_valid             => '0',                                                   --               .app_err_valid
        app_err_hdr               => (others => '0'),                                       --               .app_err_hdr
        app_err_info              => (others => '0'),                                       --               .app_err_info
        app_err_func_num          => (others => '0'),                                       --               .app_err_func_num
        test_in                   => (others => '0'),                                       --       hip_ctrl.test_in
        simu_mode_pipe            => '0',                                                   --               .simu_mode_pipe
        currentspeed              => open,                                                  --   currentspeed.currentspeed
        ceb_ack                   => pcie_ceb_ack,                                          --            ceb.ceb_ack
        ceb_din                   => pcie_ceb_din,                                          --               .ceb_din
        ceb_addr                  => pcie_ceb_addr,                                         --               .ceb_addr
        ceb_req                   => pcie_ceb_req,                                          --               .ceb_req
        ceb_dout                  => pcie_ceb_dout,                                         --               .ceb_dout
        ceb_wr                    => pcie_ceb_wr,                                           --               .ceb_wr
        ceb_cdm_convert_data      => (others => '0'),                                       --               .ceb_cdm_convert_data
        ceb_func_num              => open,                                                  --               .ceb_func_num
        sim_pipe_pclk_in          => '0',                                                   --       hip_pipe.sim_pipe_pclk_in
        sim_pipe_rate             => open,                                                  --               .sim_pipe_rate
        sim_ltssmstate            => open,                                                  --               .sim_ltssmstate
        txdata0                   => open,                                                  --               .txdata0
        txdata1                   => open,                                                  --               .txdata1
        txdata2                   => open,                                                  --               .txdata2
        txdata3                   => open,                                                  --               .txdata3
        txdata4                   => open,                                                  --               .txdata4
        txdata5                   => open,                                                  --               .txdata5
        txdata6                   => open,                                                  --               .txdata6
        txdata7                   => open,                                                  --               .txdata7
        txdata8                   => open,                                                  --               .txdata8
        txdata9                   => open,                                                  --               .txdata9
        txdata10                  => open,                                                  --               .txdata10
        txdata11                  => open,                                                  --               .txdata11
        txdata12                  => open,                                                  --               .txdata12
        txdata13                  => open,                                                  --               .txdata13
        txdata14                  => open,                                                  --               .txdata14
        txdata15                  => open,                                                  --               .txdata15
        txdatak0                  => open,                                                  --               .txdatak0
        txdatak1                  => open,                                                  --               .txdatak1
        txdatak2                  => open,                                                  --               .txdatak2
        txdatak3                  => open,                                                  --               .txdatak3
        txdatak4                  => open,                                                  --               .txdatak4
        txdatak5                  => open,                                                  --               .txdatak5
        txdatak6                  => open,                                                  --               .txdatak6
        txdatak7                  => open,                                                  --               .txdatak7
        txdatak8                  => open,                                                  --               .txdatak8
        txdatak9                  => open,                                                  --               .txdatak9
        txdatak10                 => open,                                                  --               .txdatak10
        txdatak11                 => open,                                                  --               .txdatak11
        txdatak12                 => open,                                                  --               .txdatak12
        txdatak13                 => open,                                                  --               .txdatak13
        txdatak14                 => open,                                                  --               .txdatak14
        txdatak15                 => open,                                                  --               .txdatak15
        txcompl0                  => open,                                                  --               .txcompl0
        txcompl1                  => open,                                                  --               .txcompl1
        txcompl2                  => open,                                                  --               .txcompl2
        txcompl3                  => open,                                                  --               .txcompl3
        txcompl4                  => open,                                                  --               .txcompl4
        txcompl5                  => open,                                                  --               .txcompl5
        txcompl6                  => open,                                                  --               .txcompl6
        txcompl7                  => open,                                                  --               .txcompl7
        txcompl8                  => open,                                                  --               .txcompl8
        txcompl9                  => open,                                                  --               .txcompl9
        txcompl10                 => open,                                                  --               .txcompl10
        txcompl11                 => open,                                                  --               .txcompl11
        txcompl12                 => open,                                                  --               .txcompl12
        txcompl13                 => open,                                                  --               .txcompl13
        txcompl14                 => open,                                                  --               .txcompl14
        txcompl15                 => open,                                                  --               .txcompl15
        txelecidle0               => open,                                                  --               .txelecidle0
        txelecidle1               => open,                                                  --               .txelecidle1
        txelecidle2               => open,                                                  --               .txelecidle2
        txelecidle3               => open,                                                  --               .txelecidle3
        txelecidle4               => open,                                                  --               .txelecidle4
        txelecidle5               => open,                                                  --               .txelecidle5
        txelecidle6               => open,                                                  --               .txelecidle6
        txelecidle7               => open,                                                  --               .txelecidle7
        txelecidle8               => open,                                                  --               .txelecidle8
        txelecidle9               => open,                                                  --               .txelecidle9
        txelecidle10              => open,                                                  --               .txelecidle10
        txelecidle11              => open,                                                  --               .txelecidle11
        txelecidle12              => open,                                                  --               .txelecidle12
        txelecidle13              => open,                                                  --               .txelecidle13
        txelecidle14              => open,                                                  --               .txelecidle14
        txelecidle15              => open,                                                  --               .txelecidle15
        txdetectrx0               => open,                                                  --               .txdetectrx0
        txdetectrx1               => open,                                                  --               .txdetectrx1
        txdetectrx2               => open,                                                  --               .txdetectrx2
        txdetectrx3               => open,                                                  --               .txdetectrx3
        txdetectrx4               => open,                                                  --               .txdetectrx4
        txdetectrx5               => open,                                                  --               .txdetectrx5
        txdetectrx6               => open,                                                  --               .txdetectrx6
        txdetectrx7               => open,                                                  --               .txdetectrx7
        txdetectrx8               => open,                                                  --               .txdetectrx8
        txdetectrx9               => open,                                                  --               .txdetectrx9
        txdetectrx10              => open,                                                  --               .txdetectrx10
        txdetectrx11              => open,                                                  --               .txdetectrx11
        txdetectrx12              => open,                                                  --               .txdetectrx12
        txdetectrx13              => open,                                                  --               .txdetectrx13
        txdetectrx14              => open,                                                  --               .txdetectrx14
        txdetectrx15              => open,                                                  --               .txdetectrx15
        powerdown0                => open,                                                  --               .powerdown0
        powerdown1                => open,                                                  --               .powerdown1
        powerdown2                => open,                                                  --               .powerdown2
        powerdown3                => open,                                                  --               .powerdown3
        powerdown4                => open,                                                  --               .powerdown4
        powerdown5                => open,                                                  --               .powerdown5
        powerdown6                => open,                                                  --               .powerdown6
        powerdown7                => open,                                                  --               .powerdown7
        powerdown8                => open,                                                  --               .powerdown8
        powerdown9                => open,                                                  --               .powerdown9
        powerdown10               => open,                                                  --               .powerdown10
        powerdown11               => open,                                                  --               .powerdown11
        powerdown12               => open,                                                  --               .powerdown12
        powerdown13               => open,                                                  --               .powerdown13
        powerdown14               => open,                                                  --               .powerdown14
        powerdown15               => open,                                                  --               .powerdown15
        txmargin0                 => open,                                                  --               .txmargin0
        txmargin1                 => open,                                                  --               .txmargin1
        txmargin2                 => open,                                                  --               .txmargin2
        txmargin3                 => open,                                                  --               .txmargin3
        txmargin4                 => open,                                                  --               .txmargin4
        txmargin5                 => open,                                                  --               .txmargin5
        txmargin6                 => open,                                                  --               .txmargin6
        txmargin7                 => open,                                                  --               .txmargin7
        txmargin8                 => open,                                                  --               .txmargin8
        txmargin9                 => open,                                                  --               .txmargin9
        txmargin10                => open,                                                  --               .txmargin10
        txmargin11                => open,                                                  --               .txmargin11
        txmargin12                => open,                                                  --               .txmargin12
        txmargin13                => open,                                                  --               .txmargin13
        txmargin14                => open,                                                  --               .txmargin14
        txmargin15                => open,                                                  --               .txmargin15
        txdeemph0                 => open,                                                  --               .txdeemph0
        txdeemph1                 => open,                                                  --               .txdeemph1
        txdeemph2                 => open,                                                  --               .txdeemph2
        txdeemph3                 => open,                                                  --               .txdeemph3
        txdeemph4                 => open,                                                  --               .txdeemph4
        txdeemph5                 => open,                                                  --               .txdeemph5
        txdeemph6                 => open,                                                  --               .txdeemph6
        txdeemph7                 => open,                                                  --               .txdeemph7
        txdeemph8                 => open,                                                  --               .txdeemph8
        txdeemph9                 => open,                                                  --               .txdeemph9
        txdeemph10                => open,                                                  --               .txdeemph10
        txdeemph11                => open,                                                  --               .txdeemph11
        txdeemph12                => open,                                                  --               .txdeemph12
        txdeemph13                => open,                                                  --               .txdeemph13
        txdeemph14                => open,                                                  --               .txdeemph14
        txdeemph15                => open,                                                  --               .txdeemph15
        txswing0                  => open,                                                  --               .txswing0
        txswing1                  => open,                                                  --               .txswing1
        txswing2                  => open,                                                  --               .txswing2
        txswing3                  => open,                                                  --               .txswing3
        txswing4                  => open,                                                  --               .txswing4
        txswing5                  => open,                                                  --               .txswing5
        txswing6                  => open,                                                  --               .txswing6
        txswing7                  => open,                                                  --               .txswing7
        txswing8                  => open,                                                  --               .txswing8
        txswing9                  => open,                                                  --               .txswing9
        txswing10                 => open,                                                  --               .txswing10
        txswing11                 => open,                                                  --               .txswing11
        txswing12                 => open,                                                  --               .txswing12
        txswing13                 => open,                                                  --               .txswing13
        txswing14                 => open,                                                  --               .txswing14
        txswing15                 => open,                                                  --               .txswing15
        txsynchd0                 => open,                                                  --               .txsynchd0
        txsynchd1                 => open,                                                  --               .txsynchd1
        txsynchd2                 => open,                                                  --               .txsynchd2
        txsynchd3                 => open,                                                  --               .txsynchd3
        txsynchd4                 => open,                                                  --               .txsynchd4
        txsynchd5                 => open,                                                  --               .txsynchd5
        txsynchd6                 => open,                                                  --               .txsynchd6
        txsynchd7                 => open,                                                  --               .txsynchd7
        txsynchd8                 => open,                                                  --               .txsynchd8
        txsynchd9                 => open,                                                  --               .txsynchd9
        txsynchd10                => open,                                                  --               .txsynchd10
        txsynchd11                => open,                                                  --               .txsynchd11
        txsynchd12                => open,                                                  --               .txsynchd12
        txsynchd13                => open,                                                  --               .txsynchd13
        txsynchd14                => open,                                                  --               .txsynchd14
        txsynchd15                => open,                                                  --               .txsynchd15
        txblkst0                  => open,                                                  --               .txblkst0
        txblkst1                  => open,                                                  --               .txblkst1
        txblkst2                  => open,                                                  --               .txblkst2
        txblkst3                  => open,                                                  --               .txblkst3
        txblkst4                  => open,                                                  --               .txblkst4
        txblkst5                  => open,                                                  --               .txblkst5
        txblkst6                  => open,                                                  --               .txblkst6
        txblkst7                  => open,                                                  --               .txblkst7
        txblkst8                  => open,                                                  --               .txblkst8
        txblkst9                  => open,                                                  --               .txblkst9
        txblkst10                 => open,                                                  --               .txblkst10
        txblkst11                 => open,                                                  --               .txblkst11
        txblkst12                 => open,                                                  --               .txblkst12
        txblkst13                 => open,                                                  --               .txblkst13
        txblkst14                 => open,                                                  --               .txblkst14
        txblkst15                 => open,                                                  --               .txblkst15
        txdataskip0               => open,                                                  --               .txdataskip0
        txdataskip1               => open,                                                  --               .txdataskip1
        txdataskip2               => open,                                                  --               .txdataskip2
        txdataskip3               => open,                                                  --               .txdataskip3
        txdataskip4               => open,                                                  --               .txdataskip4
        txdataskip5               => open,                                                  --               .txdataskip5
        txdataskip6               => open,                                                  --               .txdataskip6
        txdataskip7               => open,                                                  --               .txdataskip7
        txdataskip8               => open,                                                  --               .txdataskip8
        txdataskip9               => open,                                                  --               .txdataskip9
        txdataskip10              => open,                                                  --               .txdataskip10
        txdataskip11              => open,                                                  --               .txdataskip11
        txdataskip12              => open,                                                  --               .txdataskip12
        txdataskip13              => open,                                                  --               .txdataskip13
        txdataskip14              => open,                                                  --               .txdataskip14
        txdataskip15              => open,                                                  --               .txdataskip15
        rate0                     => open,                                                  --               .rate0
        rate1                     => open,                                                  --               .rate1
        rate2                     => open,                                                  --               .rate2
        rate3                     => open,                                                  --               .rate3
        rate4                     => open,                                                  --               .rate4
        rate5                     => open,                                                  --               .rate5
        rate6                     => open,                                                  --               .rate6
        rate7                     => open,                                                  --               .rate7
        rate8                     => open,                                                  --               .rate8
        rate9                     => open,                                                  --               .rate9
        rate10                    => open,                                                  --               .rate10
        rate11                    => open,                                                  --               .rate11
        rate12                    => open,                                                  --               .rate12
        rate13                    => open,                                                  --               .rate13
        rate14                    => open,                                                  --               .rate14
        rate15                    => open,                                                  --               .rate15
        rxpolarity0               => open,                                                  --               .rxpolarity0
        rxpolarity1               => open,                                                  --               .rxpolarity1
        rxpolarity2               => open,                                                  --               .rxpolarity2
        rxpolarity3               => open,                                                  --               .rxpolarity3
        rxpolarity4               => open,                                                  --               .rxpolarity4
        rxpolarity5               => open,                                                  --               .rxpolarity5
        rxpolarity6               => open,                                                  --               .rxpolarity6
        rxpolarity7               => open,                                                  --               .rxpolarity7
        rxpolarity8               => open,                                                  --               .rxpolarity8
        rxpolarity9               => open,                                                  --               .rxpolarity9
        rxpolarity10              => open,                                                  --               .rxpolarity10
        rxpolarity11              => open,                                                  --               .rxpolarity11
        rxpolarity12              => open,                                                  --               .rxpolarity12
        rxpolarity13              => open,                                                  --               .rxpolarity13
        rxpolarity14              => open,                                                  --               .rxpolarity14
        rxpolarity15              => open,                                                  --               .rxpolarity15
        currentrxpreset0          => open,                                                  --               .currentrxpreset0
        currentrxpreset1          => open,                                                  --               .currentrxpreset1
        currentrxpreset2          => open,                                                  --               .currentrxpreset2
        currentrxpreset3          => open,                                                  --               .currentrxpreset3
        currentrxpreset4          => open,                                                  --               .currentrxpreset4
        currentrxpreset5          => open,                                                  --               .currentrxpreset5
        currentrxpreset6          => open,                                                  --               .currentrxpreset6
        currentrxpreset7          => open,                                                  --               .currentrxpreset7
        currentrxpreset8          => open,                                                  --               .currentrxpreset8
        currentrxpreset9          => open,                                                  --               .currentrxpreset9
        currentrxpreset10         => open,                                                  --               .currentrxpreset10
        currentrxpreset11         => open,                                                  --               .currentrxpreset11
        currentrxpreset12         => open,                                                  --               .currentrxpreset12
        currentrxpreset13         => open,                                                  --               .currentrxpreset13
        currentrxpreset14         => open,                                                  --               .currentrxpreset14
        currentrxpreset15         => open,                                                  --               .currentrxpreset15
        currentcoeff0             => open,                                                  --               .currentcoeff0
        currentcoeff1             => open,                                                  --               .currentcoeff1
        currentcoeff2             => open,                                                  --               .currentcoeff2
        currentcoeff3             => open,                                                  --               .currentcoeff3
        currentcoeff4             => open,                                                  --               .currentcoeff4
        currentcoeff5             => open,                                                  --               .currentcoeff5
        currentcoeff6             => open,                                                  --               .currentcoeff6
        currentcoeff7             => open,                                                  --               .currentcoeff7
        currentcoeff8             => open,                                                  --               .currentcoeff8
        currentcoeff9             => open,                                                  --               .currentcoeff9
        currentcoeff10            => open,                                                  --               .currentcoeff10
        currentcoeff11            => open,                                                  --               .currentcoeff11
        currentcoeff12            => open,                                                  --               .currentcoeff12
        currentcoeff13            => open,                                                  --               .currentcoeff13
        currentcoeff14            => open,                                                  --               .currentcoeff14
        currentcoeff15            => open,                                                  --               .currentcoeff15
        rxeqeval0                 => open,                                                  --               .rxeqeval0
        rxeqeval1                 => open,                                                  --               .rxeqeval1
        rxeqeval2                 => open,                                                  --               .rxeqeval2
        rxeqeval3                 => open,                                                  --               .rxeqeval3
        rxeqeval4                 => open,                                                  --               .rxeqeval4
        rxeqeval5                 => open,                                                  --               .rxeqeval5
        rxeqeval6                 => open,                                                  --               .rxeqeval6
        rxeqeval7                 => open,                                                  --               .rxeqeval7
        rxeqeval8                 => open,                                                  --               .rxeqeval8
        rxeqeval9                 => open,                                                  --               .rxeqeval9
        rxeqeval10                => open,                                                  --               .rxeqeval10
        rxeqeval11                => open,                                                  --               .rxeqeval11
        rxeqeval12                => open,                                                  --               .rxeqeval12
        rxeqeval13                => open,                                                  --               .rxeqeval13
        rxeqeval14                => open,                                                  --               .rxeqeval14
        rxeqeval15                => open,                                                  --               .rxeqeval15
        rxeqinprogress0           => open,                                                  --               .rxeqinprogress0
        rxeqinprogress1           => open,                                                  --               .rxeqinprogress1
        rxeqinprogress2           => open,                                                  --               .rxeqinprogress2
        rxeqinprogress3           => open,                                                  --               .rxeqinprogress3
        rxeqinprogress4           => open,                                                  --               .rxeqinprogress4
        rxeqinprogress5           => open,                                                  --               .rxeqinprogress5
        rxeqinprogress6           => open,                                                  --               .rxeqinprogress6
        rxeqinprogress7           => open,                                                  --               .rxeqinprogress7
        rxeqinprogress8           => open,                                                  --               .rxeqinprogress8
        rxeqinprogress9           => open,                                                  --               .rxeqinprogress9
        rxeqinprogress10          => open,                                                  --               .rxeqinprogress10
        rxeqinprogress11          => open,                                                  --               .rxeqinprogress11
        rxeqinprogress12          => open,                                                  --               .rxeqinprogress12
        rxeqinprogress13          => open,                                                  --               .rxeqinprogress13
        rxeqinprogress14          => open,                                                  --               .rxeqinprogress14
        rxeqinprogress15          => open,                                                  --               .rxeqinprogress15
        invalidreq0               => open,                                                  --               .invalidreq0
        invalidreq1               => open,                                                  --               .invalidreq1
        invalidreq2               => open,                                                  --               .invalidreq2
        invalidreq3               => open,                                                  --               .invalidreq3
        invalidreq4               => open,                                                  --               .invalidreq4
        invalidreq5               => open,                                                  --               .invalidreq5
        invalidreq6               => open,                                                  --               .invalidreq6
        invalidreq7               => open,                                                  --               .invalidreq7
        invalidreq8               => open,                                                  --               .invalidreq8
        invalidreq9               => open,                                                  --               .invalidreq9
        invalidreq10              => open,                                                  --               .invalidreq10
        invalidreq11              => open,                                                  --               .invalidreq11
        invalidreq12              => open,                                                  --               .invalidreq12
        invalidreq13              => open,                                                  --               .invalidreq13
        invalidreq14              => open,                                                  --               .invalidreq14
        invalidreq15              => open,                                                  --               .invalidreq15
        rxdata0                   => (others => '0'),                                       --               .rxdata0
        rxdata1                   => (others => '0'),                                       --               .rxdata1
        rxdata2                   => (others => '0'),                                       --               .rxdata2
        rxdata3                   => (others => '0'),                                       --               .rxdata3
        rxdata4                   => (others => '0'),                                       --               .rxdata4
        rxdata5                   => (others => '0'),                                       --               .rxdata5
        rxdata6                   => (others => '0'),                                       --               .rxdata6
        rxdata7                   => (others => '0'),                                       --               .rxdata7
        rxdata8                   => (others => '0'),                                       --               .rxdata8
        rxdata9                   => (others => '0'),                                       --               .rxdata9
        rxdata10                  => (others => '0'),                                       --               .rxdata10
        rxdata11                  => (others => '0'),                                       --               .rxdata11
        rxdata12                  => (others => '0'),                                       --               .rxdata12
        rxdata13                  => (others => '0'),                                       --               .rxdata13
        rxdata14                  => (others => '0'),                                       --               .rxdata14
        rxdata15                  => (others => '0'),                                       --               .rxdata15
        rxdatak0                  => (others => '0'),                                       --               .rxdatak0
        rxdatak1                  => (others => '0'),                                       --               .rxdatak1
        rxdatak2                  => (others => '0'),                                       --               .rxdatak2
        rxdatak3                  => (others => '0'),                                       --               .rxdatak3
        rxdatak4                  => (others => '0'),                                       --               .rxdatak4
        rxdatak5                  => (others => '0'),                                       --               .rxdatak5
        rxdatak6                  => (others => '0'),                                       --               .rxdatak6
        rxdatak7                  => (others => '0'),                                       --               .rxdatak7
        rxdatak8                  => (others => '0'),                                       --               .rxdatak8
        rxdatak9                  => (others => '0'),                                       --               .rxdatak9
        rxdatak10                 => (others => '0'),                                       --               .rxdatak10
        rxdatak11                 => (others => '0'),                                       --               .rxdatak11
        rxdatak12                 => (others => '0'),                                       --               .rxdatak12
        rxdatak13                 => (others => '0'),                                       --               .rxdatak13
        rxdatak14                 => (others => '0'),                                       --               .rxdatak14
        rxdatak15                 => (others => '0'),                                       --               .rxdatak15
        phystatus0                => '0',                                                   --               .phystatus0
        phystatus1                => '0',                                                   --               .phystatus1
        phystatus2                => '0',                                                   --               .phystatus2
        phystatus3                => '0',                                                   --               .phystatus3
        phystatus4                => '0',                                                   --               .phystatus4
        phystatus5                => '0',                                                   --               .phystatus5
        phystatus6                => '0',                                                   --               .phystatus6
        phystatus7                => '0',                                                   --               .phystatus7
        phystatus8                => '0',                                                   --               .phystatus8
        phystatus9                => '0',                                                   --               .phystatus9
        phystatus10               => '0',                                                   --               .phystatus10
        phystatus11               => '0',                                                   --               .phystatus11
        phystatus12               => '0',                                                   --               .phystatus12
        phystatus13               => '0',                                                   --               .phystatus13
        phystatus14               => '0',                                                   --               .phystatus14
        phystatus15               => '0',                                                   --               .phystatus15
        rxvalid0                  => '0',                                                   --               .rxvalid0
        rxvalid1                  => '0',                                                   --               .rxvalid1
        rxvalid2                  => '0',                                                   --               .rxvalid2
        rxvalid3                  => '0',                                                   --               .rxvalid3
        rxvalid4                  => '0',                                                   --               .rxvalid4
        rxvalid5                  => '0',                                                   --               .rxvalid5
        rxvalid6                  => '0',                                                   --               .rxvalid6
        rxvalid7                  => '0',                                                   --               .rxvalid7
        rxvalid8                  => '0',                                                   --               .rxvalid8
        rxvalid9                  => '0',                                                   --               .rxvalid9
        rxvalid10                 => '0',                                                   --               .rxvalid10
        rxvalid11                 => '0',                                                   --               .rxvalid11
        rxvalid12                 => '0',                                                   --               .rxvalid12
        rxvalid13                 => '0',                                                   --               .rxvalid13
        rxvalid14                 => '0',                                                   --               .rxvalid14
        rxvalid15                 => '0',                                                   --               .rxvalid15
        rxstatus0                 => (others => '0'),                                       --               .rxstatus0
        rxstatus1                 => (others => '0'),                                       --               .rxstatus1
        rxstatus2                 => (others => '0'),                                       --               .rxstatus2
        rxstatus3                 => (others => '0'),                                       --               .rxstatus3
        rxstatus4                 => (others => '0'),                                       --               .rxstatus4
        rxstatus5                 => (others => '0'),                                       --               .rxstatus5
        rxstatus6                 => (others => '0'),                                       --               .rxstatus6
        rxstatus7                 => (others => '0'),                                       --               .rxstatus7
        rxstatus8                 => (others => '0'),                                       --               .rxstatus8
        rxstatus9                 => (others => '0'),                                       --               .rxstatus9
        rxstatus10                => (others => '0'),                                       --               .rxstatus10
        rxstatus11                => (others => '0'),                                       --               .rxstatus11
        rxstatus12                => (others => '0'),                                       --               .rxstatus12
        rxstatus13                => (others => '0'),                                       --               .rxstatus13
        rxstatus14                => (others => '0'),                                       --               .rxstatus14
        rxstatus15                => (others => '0'),                                       --               .rxstatus15
        rxelecidle0               => '0',                                                   --               .rxelecidle0
        rxelecidle1               => '0',                                                   --               .rxelecidle1
        rxelecidle2               => '0',                                                   --               .rxelecidle2
        rxelecidle3               => '0',                                                   --               .rxelecidle3
        rxelecidle4               => '0',                                                   --               .rxelecidle4
        rxelecidle5               => '0',                                                   --               .rxelecidle5
        rxelecidle6               => '0',                                                   --               .rxelecidle6
        rxelecidle7               => '0',                                                   --               .rxelecidle7
        rxelecidle8               => '0',                                                   --               .rxelecidle8
        rxelecidle9               => '0',                                                   --               .rxelecidle9
        rxelecidle10              => '0',                                                   --               .rxelecidle10
        rxelecidle11              => '0',                                                   --               .rxelecidle11
        rxelecidle12              => '0',                                                   --               .rxelecidle12
        rxelecidle13              => '0',                                                   --               .rxelecidle13
        rxelecidle14              => '0',                                                   --               .rxelecidle14
        rxelecidle15              => '0',                                                   --               .rxelecidle15
        rxsynchd0                 => (others => '0'),                                       --               .rxsynchd0
        rxsynchd1                 => (others => '0'),                                       --               .rxsynchd1
        rxsynchd2                 => (others => '0'),                                       --               .rxsynchd2
        rxsynchd3                 => (others => '0'),                                       --               .rxsynchd3
        rxsynchd4                 => (others => '0'),                                       --               .rxsynchd4
        rxsynchd5                 => (others => '0'),                                       --               .rxsynchd5
        rxsynchd6                 => (others => '0'),                                       --               .rxsynchd6
        rxsynchd7                 => (others => '0'),                                       --               .rxsynchd7
        rxsynchd8                 => (others => '0'),                                       --               .rxsynchd8
        rxsynchd9                 => (others => '0'),                                       --               .rxsynchd9
        rxsynchd10                => (others => '0'),                                       --               .rxsynchd10
        rxsynchd11                => (others => '0'),                                       --               .rxsynchd11
        rxsynchd12                => (others => '0'),                                       --               .rxsynchd12
        rxsynchd13                => (others => '0'),                                       --               .rxsynchd13
        rxsynchd14                => (others => '0'),                                       --               .rxsynchd14
        rxsynchd15                => (others => '0'),                                       --               .rxsynchd15
        rxblkst0                  => '0',                                                   --               .rxblkst0
        rxblkst1                  => '0',                                                   --               .rxblkst1
        rxblkst2                  => '0',                                                   --               .rxblkst2
        rxblkst3                  => '0',                                                   --               .rxblkst3
        rxblkst4                  => '0',                                                   --               .rxblkst4
        rxblkst5                  => '0',                                                   --               .rxblkst5
        rxblkst6                  => '0',                                                   --               .rxblkst6
        rxblkst7                  => '0',                                                   --               .rxblkst7
        rxblkst8                  => '0',                                                   --               .rxblkst8
        rxblkst9                  => '0',                                                   --               .rxblkst9
        rxblkst10                 => '0',                                                   --               .rxblkst10
        rxblkst11                 => '0',                                                   --               .rxblkst11
        rxblkst12                 => '0',                                                   --               .rxblkst12
        rxblkst13                 => '0',                                                   --               .rxblkst13
        rxblkst14                 => '0',                                                   --               .rxblkst14
        rxblkst15                 => '0',                                                   --               .rxblkst15
        rxdataskip0               => '0',                                                   --               .rxdataskip0
        rxdataskip1               => '0',                                                   --               .rxdataskip1
        rxdataskip2               => '0',                                                   --               .rxdataskip2
        rxdataskip3               => '0',                                                   --               .rxdataskip3
        rxdataskip4               => '0',                                                   --               .rxdataskip4
        rxdataskip5               => '0',                                                   --               .rxdataskip5
        rxdataskip6               => '0',                                                   --               .rxdataskip6
        rxdataskip7               => '0',                                                   --               .rxdataskip7
        rxdataskip8               => '0',                                                   --               .rxdataskip8
        rxdataskip9               => '0',                                                   --               .rxdataskip9
        rxdataskip10              => '0',                                                   --               .rxdataskip10
        rxdataskip11              => '0',                                                   --               .rxdataskip11
        rxdataskip12              => '0',                                                   --               .rxdataskip12
        rxdataskip13              => '0',                                                   --               .rxdataskip13
        rxdataskip14              => '0',                                                   --               .rxdataskip14
        rxdataskip15              => '0',                                                   --               .rxdataskip15
        dirfeedback0              => (others => '0'),                                       --               .dirfeedback0
        dirfeedback1              => (others => '0'),                                       --               .dirfeedback1
        dirfeedback2              => (others => '0'),                                       --               .dirfeedback2
        dirfeedback3              => (others => '0'),                                       --               .dirfeedback3
        dirfeedback4              => (others => '0'),                                       --               .dirfeedback4
        dirfeedback5              => (others => '0'),                                       --               .dirfeedback5
        dirfeedback6              => (others => '0'),                                       --               .dirfeedback6
        dirfeedback7              => (others => '0'),                                       --               .dirfeedback7
        dirfeedback8              => (others => '0'),                                       --               .dirfeedback8
        dirfeedback9              => (others => '0'),                                       --               .dirfeedback9
        dirfeedback10             => (others => '0'),                                       --               .dirfeedback10
        dirfeedback11             => (others => '0'),                                       --               .dirfeedback11
        dirfeedback12             => (others => '0'),                                       --               .dirfeedback12
        dirfeedback13             => (others => '0'),                                       --               .dirfeedback13
        dirfeedback14             => (others => '0'),                                       --               .dirfeedback14
        dirfeedback15             => (others => '0'),                                       --               .dirfeedback15
        sim_pipe_mask_tx_pll_lock => '0',                                                   --               .sim_pipe_mask_tx_pll_lock
        rx_in0                    => PCIE_RX_P(0),                                          --     hip_serial.rx_in0
        rx_in1                    => PCIE_RX_P(1),                                          --               .rx_in1
        rx_in2                    => PCIE_RX_P(2),                                          --               .rx_in2
        rx_in3                    => PCIE_RX_P(3),                                          --               .rx_in3
        rx_in4                    => PCIE_RX_P(4),                                          --               .rx_in4
        rx_in5                    => PCIE_RX_P(5),                                          --               .rx_in5
        rx_in6                    => PCIE_RX_P(6),                                          --               .rx_in6
        rx_in7                    => PCIE_RX_P(7),                                          --               .rx_in7
        rx_in8                    => PCIE_RX_P(8),                                          --               .rx_in8
        rx_in9                    => PCIE_RX_P(9),                                          --               .rx_in9
        rx_in10                   => PCIE_RX_P(10),                                         --               .rx_in10
        rx_in11                   => PCIE_RX_P(11),                                         --               .rx_in11
        rx_in12                   => PCIE_RX_P(12),                                         --               .rx_in12
        rx_in13                   => PCIE_RX_P(13),                                         --               .rx_in13
        rx_in14                   => PCIE_RX_P(14),                                         --               .rx_in14
        rx_in15                   => PCIE_RX_P(15),                                         --               .rx_in15
        tx_out0                   => PCIE_TX_P(0),                                          --               .tx_out0
        tx_out1                   => PCIE_TX_P(1),                                          --               .tx_out1
        tx_out2                   => PCIE_TX_P(2),                                          --               .tx_out2
        tx_out3                   => PCIE_TX_P(3),                                          --               .tx_out3
        tx_out4                   => PCIE_TX_P(4),                                          --               .tx_out4
        tx_out5                   => PCIE_TX_P(5),                                          --               .tx_out5
        tx_out6                   => PCIE_TX_P(6),                                          --               .tx_out6
        tx_out7                   => PCIE_TX_P(7),                                          --               .tx_out7
        tx_out8                   => PCIE_TX_P(8),                                          --               .tx_out8
        tx_out9                   => PCIE_TX_P(9),                                          --               .tx_out9
        tx_out10                  => PCIE_TX_P(10),                                         --               .tx_out10
        tx_out11                  => PCIE_TX_P(11),                                         --               .tx_out11
        tx_out12                  => PCIE_TX_P(12),                                         --               .tx_out12
        tx_out13                  => PCIE_TX_P(13),                                         --               .tx_out13
        tx_out14                  => PCIE_TX_P(14),                                         --               .tx_out14
        tx_out15                  => PCIE_TX_P(15),                                         --               .tx_out15
        pm_linkst_in_l1           => open,                                                  --     power_mgnt.pm_linkst_in_l1
        pm_linkst_in_l0s          => open,                                                  --               .pm_linkst_in_l0s
        pm_state                  => open,                                                  --               .pm_state
        pm_dstate                 => open,                                                  --               .pm_dstate
        apps_pm_xmt_pme           => '0',                                                   --               .apps_pm_xmt_pme
        apps_ready_entr_l23       => '0',                                                   --               .apps_ready_entr_l23
        apps_pm_xmt_turnoff       => '0',                                                   --               .apps_pm_xmt_turnoff
        app_init_rst              => '0',                                                   --               .app_init_rst
        app_xfer_pending          => '0'                                                    --               .app_xfer_pending
    -- flr_rcvd_vf               => open,               --    flr_ctrl_vf.flr_rcvd_vf
    -- flr_rcvd_pf_num           => open,           --               .flr_rcvd_pf_num
    -- flr_rcvd_vf_num           => open,           --               .flr_rcvd_vf_num
    -- flr_completed_vf          => '0',          --               .flr_completed_vf
    -- flr_completed_pf_num      => (others => '0'),      --               .flr_completed_pf_num
    -- flr_completed_vf_num      => (others => '0')       --               .flr_completed_vf_num
    );

    PCIE_TX_N <= not PCIE_TX_P;

    pcie_clk(0)         <= pcie_hip_clk(0);
    pcie_init_done_n(0) <= INIT_DONE_N;

    -- =========================================================================
    --  UP/DOWN AVALON-ST INTERFACE
    -- =========================================================================

    pcie_adapter_i : entity work.PCIE_ADAPTER
    generic map (
        CQ_MFB_REGIONS     => CQ_MFB_REGIONS,
        CQ_MFB_REGION_SIZE => CQ_MFB_REGION_SIZE,
        CQ_MFB_BLOCK_SIZE  => CQ_MFB_BLOCK_SIZE,
        CQ_MFB_ITEM_WIDTH  => CQ_MFB_ITEM_WIDTH,
        RC_MFB_REGIONS     => RC_MFB_REGIONS,
        RC_MFB_REGION_SIZE => RC_MFB_REGION_SIZE,
        RC_MFB_BLOCK_SIZE  => RC_MFB_BLOCK_SIZE,
        RC_MFB_ITEM_WIDTH  => RC_MFB_ITEM_WIDTH,
        CC_MFB_REGIONS     => CC_MFB_REGIONS,
        CC_MFB_REGION_SIZE => CC_MFB_REGION_SIZE,
        CC_MFB_BLOCK_SIZE  => CC_MFB_BLOCK_SIZE,
        CC_MFB_ITEM_WIDTH  => CC_MFB_ITEM_WIDTH,
        RQ_MFB_REGIONS     => RQ_MFB_REGIONS,
        RQ_MFB_REGION_SIZE => RQ_MFB_REGION_SIZE,
        RQ_MFB_BLOCK_SIZE  => RQ_MFB_BLOCK_SIZE,
        RQ_MFB_ITEM_WIDTH  => RQ_MFB_ITEM_WIDTH,
        ENDPOINT_TYPE      => "H_TILE",
        DEVICE             => DEVICE,
        CQ_FIFO_ITEMS      => CQ_FIFO_ITEMS,
        AXI_CQUSER_WIDTH   => 183,
        AXI_CCUSER_WIDTH   => 81,
        AXI_RQUSER_WIDTH   => 137,
        AXI_RCUSER_WIDTH   => 161,
        AXI_STRADDLING     => false
    )
    port map (
        PCIE_CLK            => pcie_clk(0),
        PCIE_RESET          => pcie_rst(0)(0),

        AVST_DOWN_DATA      => pcie_avst_down_data(0),
        AVST_DOWN_HDR       => (others => '0'), -- P-TILE only
        AVST_DOWN_PREFIX    => (others => '0'), -- P-TILE only
        AVST_DOWN_SOP       => pcie_avst_down_sop(0),
        AVST_DOWN_EOP       => pcie_avst_down_eop(0),
        AVST_DOWN_EMPTY     => pcie_avst_down_empty(0),
        AVST_DOWN_BAR_RANGE => pcie_avst_down_bar_range(0),
        AVST_DOWN_VALID     => pcie_avst_down_valid(0),
        AVST_DOWN_READY     => pcie_avst_down_ready(0),

        AVST_UP_DATA        => pcie_avst_up_data(0),
        AVST_UP_HDR         => open,
        AVST_UP_PREFIX      => open,
        AVST_UP_SOP         => pcie_avst_up_sop(0),
        AVST_UP_EOP         => pcie_avst_up_eop(0),
        AVST_UP_ERROR       => pcie_avst_up_error(0),
        AVST_UP_VALID       => pcie_avst_up_valid(0),
        AVST_UP_READY       => pcie_avst_up_ready(0),

        CRDT_DOWN_INIT_DONE => '0',
        CRDT_DOWN_UPDATE    => open,
        CRDT_DOWN_CNT_PH    => open,
        CRDT_DOWN_CNT_NPH   => open,
        CRDT_DOWN_CNT_CPLH  => open,
        CRDT_DOWN_CNT_PD    => open,
        CRDT_DOWN_CNT_NPD   => open,
        CRDT_DOWN_CNT_CPLD  => open,

        CRDT_UP_INIT_DONE   => '0',
        CRDT_UP_UPDATE      => open,
        CRDT_UP_CNT_PH      => open,
        CRDT_UP_CNT_NPH     => open,
        CRDT_UP_CNT_CPLH    => open,
        CRDT_UP_CNT_PD      => open,
        CRDT_UP_CNT_NPD     => open,
        CRDT_UP_CNT_CPLD    => open,

        CQ_AXI_DATA         => (others => '0'),
        CQ_AXI_USER         => (others => '0'),
        CQ_AXI_LAST         => '0',
        CQ_AXI_KEEP         => (others => '0'),
        CQ_AXI_VALID        => '0',
        CQ_AXI_READY        => open,

        RC_AXI_DATA         => (others => '0'),
        RC_AXI_USER         => (others => '0'),
        RC_AXI_LAST         => '0',
        RC_AXI_KEEP         => (others => '0'),
        RC_AXI_VALID        => '0',
        RC_AXI_READY        => open,

        CC_AXI_DATA         => open,
        CC_AXI_USER         => open,
        CC_AXI_LAST         => open,
        CC_AXI_KEEP         => open,
        CC_AXI_VALID        => open,
        CC_AXI_READY        => '0',

        RQ_AXI_DATA         => open,
        RQ_AXI_USER         => open,
        RQ_AXI_LAST         => open,
        RQ_AXI_KEEP         => open,
        RQ_AXI_VALID        => open,
        RQ_AXI_READY        => '0',

        CQ_MFB_DATA         => CQ_MFB_DATA(0),
        CQ_MFB_META         => CQ_MFB_META(0),
        CQ_MFB_SOF          => CQ_MFB_SOF(0),
        CQ_MFB_EOF          => CQ_MFB_EOF(0),
        CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS(0),
        CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS(0),
        CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY(0),
        CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY(0),

        RC_MFB_DATA         => RC_MFB_DATA(0),
        RC_MFB_META         => RC_MFB_META(0),
        RC_MFB_SOF          => RC_MFB_SOF(0),
        RC_MFB_EOF          => RC_MFB_EOF(0),
        RC_MFB_SOF_POS      => RC_MFB_SOF_POS(0),
        RC_MFB_EOF_POS      => RC_MFB_EOF_POS(0),
        RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY(0),
        RC_MFB_DST_RDY      => RC_MFB_DST_RDY(0),

        CC_MFB_DATA         => CC_MFB_DATA(0),
        CC_MFB_META         => CC_MFB_META(0),
        CC_MFB_SOF          => CC_MFB_SOF(0),
        CC_MFB_EOF          => CC_MFB_EOF(0),
        CC_MFB_SOF_POS      => CC_MFB_SOF_POS(0),
        CC_MFB_EOF_POS      => CC_MFB_EOF_POS(0),
        CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY(0),
        CC_MFB_DST_RDY      => CC_MFB_DST_RDY(0),

        RQ_MFB_DATA         => RQ_MFB_DATA(0),
        RQ_MFB_META         => RQ_MFB_META(0),
        RQ_MFB_SOF          => RQ_MFB_SOF(0),
        RQ_MFB_EOF          => RQ_MFB_EOF(0),
        RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS(0),
        RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS(0),
        RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY(0),
        RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY(0)
    );

    -- =========================================================================
    --  PCIE RESET LOGIC
    -- =========================================================================

    pcie_rst_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => RESET_WIDTH+1
    )
    port map (
        CLK       => pcie_clk(0),
        ASYNC_RST => pcie_reset_status(0),
        OUT_RST   => pcie_rst(0)
    );

    PCIE_USER_CLK(0)   <= pcie_clk(0);
    PCIE_USER_RESET(0) <= pcie_rst(0)(RESET_WIDTH+1-1 downto 1);

    -- =========================================================================
    --  PCIE CONFIGURATION REGISTERS
    -- =========================================================================

    process (pcie_clk(0))
    begin
        if (rising_edge(pcie_clk(0))) then
            pcie_link_up_reg(0) <= pcie_link_up_comb(0);
            PCIE_LINK_UP(0)     <= pcie_link_up_reg(0);
        end if;
    end process;

    PCIE_MPS(0)            <= "010"; -- 512B
    PCIE_MRRS(0)           <= "010"; -- 512B
    PCIE_EXT_TAG_EN(0)     <= '1';
    PCIE_RCB_SIZE(0)       <= '0';
    PCIE_10B_TAG_REQ_EN(0) <= '0';

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    -- Interface conversion (Intel CEB <=> Xilinx CFG_EXT)
    cfg_ext_reg_p : process (pcie_clk(0))
    begin
        if (rising_edge(pcie_clk(0))) then
            cfg_ext_register(0)   <= pcie_ceb_addr(11 downto 2);
            cfg_ext_write_be(0)   <= pcie_ceb_wr;
            cfg_ext_write_data(0) <= pcie_ceb_dout;
        end if;
    end process;

    cfg_ext_vld_reg_p : process (pcie_clk(0))
    begin
        if (rising_edge(pcie_clk(0))) then
            if (pcie_rst(0)(0) = '1' or pcie_ceb_ack = '1') then
                cfg_ext_write(0) <= '0';
                cfg_ext_read(0)  <= '0';
            else
                cfg_ext_write(0) <= (or pcie_ceb_wr) and pcie_ceb_req;
                cfg_ext_read(0)  <= (nor pcie_ceb_wr) and pcie_ceb_req;
            end if;
        end if;
    end process;

    pcie_ceb_din <= cfg_ext_read_data(0);
    pcie_ceb_ack <= cfg_ext_read_dv(0) or cfg_ext_write(0);

    -- Device Tree ROM
    pci_ext_cap_i: entity work.PCI_EXT_CAP
    generic map (
        ENDPOINT_ID            => 0,
        ENDPOINT_ID_ENABLE     => true,
        DEVICE_TREE_ENABLE     => true,
        VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
        VSEC_NEXT_POINTER      => 16#000#,
        CARD_ID_WIDTH          => CARD_ID_WIDTH,
        CFG_EXT_READ_DV_HOTFIX => false
    )
    port map (
        CLK                    => pcie_clk(0),
        CARD_ID                => CARD_ID(0),
        CFG_EXT_READ           => cfg_ext_read(0),
        CFG_EXT_WRITE          => cfg_ext_write(0),
        CFG_EXT_REGISTER       => cfg_ext_register(0),
        CFG_EXT_FUNCTION       => (others => '0'),
        CFG_EXT_WRITE_DATA     => cfg_ext_write_data(0),
        CFG_EXT_WRITE_BE       => cfg_ext_write_be(0),
        CFG_EXT_READ_DATA      => cfg_ext_read_data(0),
        CFG_EXT_READ_DV        => cfg_ext_read_dv(0)
    );

end architecture;
