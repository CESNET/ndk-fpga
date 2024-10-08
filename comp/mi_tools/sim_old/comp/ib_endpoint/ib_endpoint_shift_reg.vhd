--
-- lb_endpoint_shift_reg.vhd: Internal Bus ADC Shift Register
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_SHIFT_REG is
   port (
      -- Common Interface
      CLK          : in  std_logic;
      RESET        : in  std_logic;

      -- Input Interface
      DATA_IN      : in  std_logic_vector(63 downto 0);
      SOP_IN       : in  std_logic;
      EOP_IN       : in  std_logic;
      SRC_RDY_IN   : in  std_logic;
      DST_RDY_IN   : out std_logic;

      --Output Interface
      DATA_OUT     : out std_logic_vector(63 downto 0);
      DATA_OUT_VLD : out std_logic;
      SOP_OUT      : out std_logic;
      EOP_OUT      : out std_logic;
      SHR_RE       : in  std_logic;

      -- Addr Dec interface
      WRITE_TRANS  : out std_logic;
      READ_TRANS   : out std_logic;
      READ_BACK    : out std_logic
      );
end entity IB_ENDPOINT_SHIFT_REG;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_SHIFT_REG_ARCH of IB_ENDPOINT_SHIFT_REG is
-- Signal Declaration ---------------------------------------------------------
   signal full                  : std_logic;
   signal empty                 : std_logic;
   signal sh_data_in            : std_logic_vector(68 downto 0);
   signal sh_data_out           : std_logic_vector(68 downto 0);

   -- Addr Decoder
   signal trans_type            : std_logic_vector(3 downto 0);
   signal aux_write_trans       : std_logic;
   signal aux_read_trans        : std_logic;
   signal aux_read_back_trans   : std_logic;
   signal aux_trans_type        : std_logic_vector(2 downto 0);
   signal addr_dec_en           : std_logic;

begin

trans_type  <= DATA_IN(15 downto C_IB_LENGTH_WIDTH);
addr_dec_en <= SOP_IN and SRC_RDY_IN;

aux_trans_type  <= trans_type(2 downto 0);
aux_write_trans     <= '1' when addr_dec_en='1' and (aux_trans_type = C_IB_L2LW_TRANSACTION or
                                aux_trans_type = C_IB_RD_COMPL_TRANSACTION) else '0';

aux_read_trans      <= '1' when addr_dec_en='1' and aux_trans_type = C_IB_L2LR_TRANSACTION else '0';

aux_read_back_trans <= '1' when addr_dec_en='1' and (aux_trans_type = C_IB_L2LW_TRANSACTION and
                                TRANS_TYPE(3)='1') else '0';


DST_RDY_IN    <= not full;
DATA_OUT_VLD  <= not empty;
sh_data_in    <= aux_read_back_trans & aux_read_trans & aux_write_trans &
                EOP_IN & SOP_IN & DATA_IN;
DATA_OUT      <= sh_data_out(63 downto 0);
SOP_OUT       <= sh_data_out(64);
EOP_OUT       <= sh_data_out(65);
WRITE_TRANS   <= sh_data_out(66);
READ_TRANS    <= sh_data_out(67);
READ_BACK     <= sh_data_out(68);

-- ----------------------------------------------------------------------------
sh_fifo_u : entity work.sh_fifo
   generic map (
      FIFO_WIDTH  => 69,
      FIFO_DEPTH  => 16,
      USE_INREG   => false,
      USE_OUTREG  => true
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      -- write interface
      DIN         => sh_data_in,
      WE          => SRC_RDY_IN,
      FULL        => full,

      -- read interface
      DOUT       => sh_data_out,
      RE         => SHR_RE,
      EMPTY      => empty
   );


end architecture IB_ENDPOINT_SHIFT_REG_ARCH;

