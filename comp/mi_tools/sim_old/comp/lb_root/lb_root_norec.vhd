-- lb_root_norec.vhd: Local Bus Root Component without records
-- Copyright (C) 2009 CESNET
-- Author(s): Vitkor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.ib_pkg.all; -- Internal Bus package
use work.lb_pkg.all; -- Local Bus package
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ROOT_NOREC is
   generic(
      BASE_ADDR        : std_logic_vector(31 downto 0):=X"00000000";
      LIMIT            : std_logic_vector(31 downto 0):=X"00000100";

      -- Abort timeout counter width
      -- TIMEOUT and TIME will be 2**WIDTH cycles
      ABORT_CNT_WIDTH  : integer := 6
   );
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      RESET         : in std_logic;

      -- Local Bus Interface
      INTERNAL_BUS_DOWN_DATA        : in  std_logic_vector(63 downto 0);
      INTERNAL_BUS_DOWN_SOP_N       : in  std_logic;
      INTERNAL_BUS_DOWN_EOP_N       : in  std_logic;
      INTERNAL_BUS_DOWN_SRC_RDY_N   : in  std_logic;
      INTERNAL_BUS_DOWN_DST_RDY_N   : out std_logic;
      INTERNAL_BUS_UP_DATA          : out std_logic_vector(63 downto 0);
      INTERNAL_BUS_UP_SOP_N         : out std_logic;
      INTERNAL_BUS_UP_EOP_N         : out std_logic;
      INTERNAL_BUS_UP_SRC_RDY_N     : out std_logic;
      INTERNAL_BUS_UP_DST_RDY_N     : in  std_logic;

      -- Local Bus Interface
      LOCAL_BUS_DWR   : out std_logic_vector(15 downto 0);
      LOCAL_BUS_BE    : out std_logic_vector(1 downto 0);
      LOCAL_BUS_ADS_N : out std_logic;
      LOCAL_BUS_RD_N  : out std_logic;
      LOCAL_BUS_WR_N  : out std_logic;
      LOCAL_BUS_DRD   : in  std_logic_vector(15 downto 0);
      LOCAL_BUS_RDY_N : in  std_logic;
      LOCAL_BUS_ERR_N : in  std_logic;
      LOCAL_BUS_ABORT_N:out std_logic
  );
end entity LB_ROOT_NOREC;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ROOT_ARCH of LB_ROOT_NOREC is

     -- IB2ADC Map
     signal ib_endpoint_wr_req_addr      : std_logic_vector(log2(LIMIT)-1 downto 0);
     signal ib_endpoint_wr_req_data      : std_logic_vector(63 downto 0);
     signal ib_endpoint_wr_req_be        : std_logic_vector(7 downto 0);
     signal ib_endpoint_wr_req           : std_logic;
     signal ib_endpoint_wr_rdy           : std_logic;
     signal ib_endpoint_wr_sof           : std_logic;
     signal ib_endpoint_wr_eof           : std_logic;
     signal ib_endpoint_rd_req_addr      : std_logic_vector(log2(LIMIT)-1 downto 0);
     signal ib_endpoint_rd_req_be        : std_logic_vector(7 downto 0);
     signal ib_endpoint_rd_data          : std_logic_vector(63 downto 0);
     signal ib_endpoint_rd_req           : std_logic;
     signal ib_endpoint_rd_ardy          : std_logic;
     signal ib_endpoint_src_rdy          : std_logic;
     signal ib_endpoint_dst_rdy          : std_logic;
     signal ib_endpoint_rd_sof_in        : std_logic;
     signal ib_endpoint_rd_eof_in        : std_logic;

     -- Root Core
     signal core_addr           : std_logic_vector(31 downto 0);
     signal core_sof            : std_logic;
     signal core_eof            : std_logic;
     signal core_data           : std_logic_vector(63 downto 0);
     signal core_be             : std_logic_vector(7 downto 0);
     signal core_rd             : std_logic;
     signal core_wr             : std_logic;
     signal core_item_vld       : std_logic;
     signal core_next_item      : std_logic;
     signal core_drd            : std_logic_vector(63 downto 0);
     signal core_drdy           : std_logic;
     signal core_drd_last       : std_logic;

     -- Pipeline registers
     signal lb_dwr              : std_logic_vector(15 downto 0);
     signal lb_be               : std_logic_vector(1 downto 0);
     signal lb_ads              : std_logic;
     signal lb_rd               : std_logic;
     signal lb_wr               : std_logic;
     signal lb_drd              : std_logic_vector(15 downto 0);
     signal lb_rdy              : std_logic;
     signal lb_err              : std_logic;
     signal lb_abort            : std_logic;
     signal abort_reset         : std_logic;

     signal reset_pipe : std_logic;
     attribute equivalent_register_removal : string;
     attribute equivalent_register_removal of reset_pipe : signal is "no";

begin

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(RESET, IB_CLK)
   begin
      if IB_CLK'event and IB_CLK = '1' then
         reset_pipe  <= RESET;
      end if;
end process;

abort_reset <= reset_pipe or lb_abort;

-- Internal Bus Endpoint Component ---------------------------------------------
IB_ENDPOINT_U: entity work.IB_ENDPOINT_CORE
   generic map (
      ADDR_WIDTH          => log2(LIMIT),
      INPUT_BUFFER_SIZE   => 0,
      OUTPUT_BUFFER_SIZE  => 0,
      READ_REORDER_BUFFER => true,
      STRICT_EN           => true,
      MASTER_EN           => false
   )
   port map (
      -- Common Interface
      IB_CLK             => IB_CLK,
      IB_RESET           => reset_pipe,

      -- Internal Bus Interface
        -- DOWNSTREAM
      IB_DOWN_DATA       => INTERNAL_BUS_DOWN_DATA,
      IB_DOWN_SOP_N      => INTERNAL_BUS_DOWN_SOP_N,
      IB_DOWN_EOP_N      => INTERNAL_BUS_DOWN_EOP_N,
      IB_DOWN_SRC_RDY_N  => INTERNAL_BUS_DOWN_SRC_RDY_N,
      IB_DOWN_DST_RDY_N  => INTERNAL_BUS_DOWN_DST_RDY_N,
        -- UPSTREAM
      IB_UP_DATA         => INTERNAL_BUS_UP_DATA,
      IB_UP_SOP_N        => INTERNAL_BUS_UP_SOP_N,
      IB_UP_EOP_N        => INTERNAL_BUS_UP_EOP_N,
      IB_UP_SRC_RDY_N    => INTERNAL_BUS_UP_SRC_RDY_N,
      IB_UP_DST_RDY_N    => INTERNAL_BUS_UP_DST_RDY_N,

      -- Write Interface
      WR_ADDR            => ib_endpoint_wr_req_addr,
      WR_DATA            => ib_endpoint_wr_req_data,
      WR_BE              => ib_endpoint_wr_req_be,
      WR_REQ             => ib_endpoint_wr_req,
      WR_RDY             => ib_endpoint_wr_rdy,
      WR_SOF             => ib_endpoint_wr_sof,
      WR_EOF             => ib_endpoint_wr_eof,
      WR_LENGTH          => open,

      -- Read Interface
      RD_ADDR            => ib_endpoint_rd_req_addr,
      RD_BE              => ib_endpoint_rd_req_be,
      RD_REQ             => ib_endpoint_rd_req,
      RD_ARDY            => ib_endpoint_rd_ardy,
      RD_SOF_IN          => ib_endpoint_rd_sof_in,
      RD_EOF_IN          => ib_endpoint_rd_eof_in,
      RD_DATA            => ib_endpoint_rd_data,
      RD_SRC_RDY         => ib_endpoint_src_rdy,
      RD_DST_RDY         => ib_endpoint_dst_rdy,

      -- RD_WR Abort
      RD_WR_ABORT        => lb_abort,

      -- Master Interface Input
      BM_GLOBAL_ADDR     => X"0000000000000000",
      BM_LOCAL_ADDR      => X"00000000",
      BM_LENGTH          => X"000",
      BM_TAG             => X"0000",
      BM_TRANS_TYPE      => "00",
      BM_REQ             => '0',
      BM_ACK             => open,

      -- Master Output interface
      BM_OP_TAG          => open,
      BM_OP_DONE         => open
  );

-- Local Bus Root Buffer ---------------------------------------------
LB_ROOT_BUFFER_U : entity work.LB_ROOT_BUFFER
   generic map (
      BASE_ADDR          => BASE_ADDR,
      ADDR_WIDTH         => log2(LIMIT)
   )
   port map (
      -- Common Interface
      CLK                => IB_CLK,
      RESET              => abort_reset,

      -- Write Interface
      ADDR_WR            => ib_endpoint_wr_req_addr,
      DWR                => ib_endpoint_wr_req_data,
      BE_WR              => ib_endpoint_wr_req_be,
      WR                 => ib_endpoint_wr_req,
      RDY_WR             => ib_endpoint_wr_rdy,
      SOF_WR             => ib_endpoint_wr_sof,
      EOF_WR             => ib_endpoint_wr_eof,

      -- Read Interface
      ADDR_RD            => ib_endpoint_rd_req_addr,
      BE_RD              => ib_endpoint_rd_req_be,
      DRD                => ib_endpoint_rd_data,
      RD                 => ib_endpoint_rd_req,
      ARDY_RD            => ib_endpoint_rd_ardy,
      DRDY_RD            => ib_endpoint_src_rdy,
      ERDY_RD            => ib_endpoint_dst_rdy,
      SOF_RD             => ib_endpoint_rd_sof_in,
      EOF_RD             => ib_endpoint_rd_eof_in,

      -- Root Core Interface
      BUFFER_ADDR        => core_addr,
      BUFFER_SOF         => core_sof,
      BUFFER_EOF         => core_eof,
      BUFFER_DATA        => core_data,
      BUFFER_BE          => core_be,
      BUFFER_RD          => core_rd,
      BUFFER_WR          => core_wr,
      BUFFER_VLD         => core_item_vld,
      BUFFER_NEXT        => core_next_item,
      BUFFER_DRD         => core_drd,
      BUFFER_DRDY        => core_drdy,
      BUFFER_DRD_LAST    => core_drd_last
  );


-- Local Bus Core component ----------------------------------------------------
LB_ROOT_CORE_U : entity work.LB_ROOT_CORE
   generic map (
      ABORT_CNT_WIDTH => ABORT_CNT_WIDTH
   )
   port map (
      -- Common Interface
      CLK             => IB_CLK,
      RESET           => reset_pipe,
      -- Buffer Interface
      BUFFER_ADDR     => core_addr,
      BUFFER_SOF      => core_sof,
      BUFFER_EOF      => core_eof,
      BUFFER_DATA     => core_data,
      BUFFER_BE       => core_be,
      BUFFER_RD       => core_rd,
      BUFFER_WR       => core_wr,
      BUFFER_VLD      => core_item_vld,
      BUFFER_NEXT     => core_next_item,
      BUFFER_DRD      => core_drd,
      BUFFER_DRDY     => core_drdy,
      BUFFER_DRD_LAST => core_drd_last,

      -- Localbus Interface
      LB_DWR          => lb_dwr,
      LB_BE           => lb_be,
      LB_ADS          => lb_ads,
      LB_RD           => lb_rd,
      LB_WR           => lb_wr,
      LB_DRD          => lb_drd,
      LB_RDY          => lb_rdy,
      LB_ERR          => lb_err,
      LB_ABORT        => lb_abort
   );

-------------------------------------------------------------------------------
--                          OUTPUT MAPPING
-------------------------------------------------------------------------------
LOCAL_BUS_DWR      <= lb_dwr;
LOCAL_BUS_BE       <= lb_be;
LOCAL_BUS_ADS_N    <= not lb_ads;
LOCAL_BUS_RD_N     <= not lb_rd;
LOCAL_BUS_WR_N     <= not lb_wr;
lb_drd             <= LOCAL_BUS_DRD;
lb_rdy             <= not LOCAL_BUS_RDY_N;
lb_err             <= not LOCAL_BUS_ERR_N;
LOCAL_BUS_ABORT_N  <= not lb_abort;

end architecture LB_ROOT_ARCH;
