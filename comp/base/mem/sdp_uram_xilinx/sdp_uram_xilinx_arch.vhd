
--
-- SDP_URAM_XILINX.vhd: Architecture for simple dual port UltraRAM
-- Copyright (C) 2018 CESNET
-- Author(s): Kamil Vojanec <xvojan0@stud.fit.vutbr.cz>
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
use IEEE.numeric_std.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SDP_URAM_XILINX_arch of SDP_URAM_XILINX is
begin

   -- Generate read first mode entity
   read_first_gen : if(WRITE_MODE = "READ_FIRST") generate
      read_first : entity work.DP_URAM_XILINX
         generic map(
            DEVICE => DEVICE,
            DATA_WIDTH => DATA_WIDTH,
            ADDRESS_WIDTH => ADDRESS_WIDTH,
            ADDITIONAL_REG => ADDITIONAL_REG,
            EXTERNAL_OUT_REG => EXTERNAL_OUT_REG,
            INTERNAL_OUT_REG => INTERNAL_OUT_REG,
            DEBUG_ASSERT_UNINITIALIZED => DEBUG_ASSERT_UNINITIALIZED
            )
         port map(
            CLK => CLK,
            RSTA => RSTB,
            PIPE_ENA => PIPE_EN,
            REA => REB,
            WEA => '0',
            ADDRA => ADDRB,
            DIA => (others => '0'),
            DOA => DOB,
            DOA_DV => DOB_DV,

            RSTB => RSTB,
            PIPE_ENB => '1',
            REB => '0',
            WEB => WEA,
            DIB => DIA,
            ADDRB => ADDRA,
            DOB => open,
            DOB_DV => open
            );
   end generate;

   -- Generate write first mode entity
   write_first_gen : if(WRITE_MODE = "WRITE_FIRST") generate
      write_first : entity work.DP_URAM_XILINX
         generic map(
            DEVICE => DEVICE,
            DATA_WIDTH => DATA_WIDTH,
            ADDRESS_WIDTH => ADDRESS_WIDTH,
            ADDITIONAL_REG => ADDITIONAL_REG,
            EXTERNAL_OUT_REG => EXTERNAL_OUT_REG,
            INTERNAL_OUT_REG => INTERNAL_OUT_REG,
            DEBUG_ASSERT_UNINITIALIZED => DEBUG_ASSERT_UNINITIALIZED
            )
         port map(
            CLK => CLK,
            RSTA => RSTB,
            PIPE_ENA => '1',
            REA => '0',
            WEA => WEA,
            ADDRA => ADDRA,
            DIA => DIA,
            DOA => open,
            DOA_DV => open,

            RSTB => RSTB,
            PIPE_ENB => PIPE_EN,
            REB => REB,
            WEB => '0',
            DIB => (others => '0'),
            ADDRB => ADDRB,
            DOB => DOB,
            DOB_DV => DOB_DV
            );
   end generate;


end architecture SDP_URAM_XILINX_arch;
