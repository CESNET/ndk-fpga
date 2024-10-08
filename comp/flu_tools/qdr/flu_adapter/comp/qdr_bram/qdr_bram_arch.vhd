-- qdr_bram_arch.vhd
--!
--! \file
--! \brief Small QDR composed of BRAM architecture
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function.
use work.math_pack.all;

--! \brief Implementation small QDR composed of BRAM
architecture FULL of QDR_BRAM is

   signal we               : std_logic_vector(15 downto 0);
   signal user_rd_cmd_reg0 : std_logic;
   signal user_rd_cmd_reg1 : std_logic;

begin

   user_rd_cmd_regp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RST = '1') then
            user_rd_cmd_reg0 <= '0';
            user_rd_cmd_reg1 <= '0';
         else
            user_rd_cmd_reg0 <= USER_RD_CMD;
            user_rd_cmd_reg1 <= user_rd_cmd_reg0;
         end if;
      end if;
   end process;

   USER_RD_VALID <= user_rd_cmd_reg1;

   we <= not USER_WR_BW_N;

   BRAM_SDP_MACRO_inst0 : BRAM_SDP_MACRO
   generic map (
      BRAM_SIZE => "36Kb", -- Target BRAM, "18Kb" or "36Kb"
      DEVICE => "7SERIES", -- Target device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      WRITE_WIDTH => 72, -- Valid values are 1-72 (37-72 only valid when BRAM_SIZE="36Kb")
      READ_WIDTH => 72, -- Valid values are 1-72 (37-72 only valid when BRAM_SIZE="36Kb")
      DO_REG => 1, -- Optional output register (0 or 1)
      INIT_FILE => "NONE",
      SIM_COLLISION_CHECK => "ALL", -- Collision check enable "ALL", "WARNING_ONLY",
                                    -- "GENERATE_X_ONLY" or "NONE"
      SRVAL => X"000000000000000000", -- Set/Reset value for port output
      WRITE_MODE => "READ_FIRST", -- Specify "READ_FIRST" for same clock or synchronous clocks
                                   -- Specify "WRITE_FIRST for asynchrononous clocks on ports
      INIT => X"000000000000000000" -- Initial values on output port
      )
   port map (
      DO => USER_RD_DATA(71 downto 0), -- Output read data port, width defined by READ_WIDTH parameter
      DI => USER_WR_DATA(71 downto 0), -- Input write data port, width defined by WRITE_WIDTH parameter
      RDADDR => USER_RD_ADDR, -- Input read address, width defined by read port depth
      RDCLK => CLK, -- 1-bit input read clock
      RDEN => USER_RD_CMD, -- 1-bit input read port enable
      REGCE => '1', -- 1-bit input read output register enable
      RST => RST, -- 1-bit input reset
      WE => we(7 downto 0), -- Input write enable, width defined by write port depth
      WRADDR => USER_WR_ADDR, -- Input write address, width defined by write port depth
      WRCLK => CLK, -- 1-bit input write clock
      WREN =>  USER_WR_CMD-- 1-bit write port enable
   );

   BRAM_SDP_MACRO_inst1 : BRAM_SDP_MACRO
   generic map (
      BRAM_SIZE => "36Kb", -- Target BRAM, "18Kb" or "36Kb"
      DEVICE => "7SERIES", -- Target device: "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      WRITE_WIDTH => 72, -- Valid values are 1-72 (37-72 only valid when BRAM_SIZE="36Kb")
      READ_WIDTH => 72, -- Valid values are 1-72 (37-72 only valid when BRAM_SIZE="36Kb")
      DO_REG => 1, -- Optional output register (0 or 1)
      INIT_FILE => "NONE",
      SIM_COLLISION_CHECK => "ALL", -- Collision check enable "ALL", "WARNING_ONLY",
                                    -- "GENERATE_X_ONLY" or "NONE"
      SRVAL => X"000000000000000000", -- Set/Reset value for port output
      WRITE_MODE => "READ_FIRST", -- Specify "READ_FIRST" for same clock or synchronous clocks
                                   -- Specify "WRITE_FIRST for asynchrononous clocks on ports
      INIT => X"000000000000000000" -- Initial values on output port
      )
   port map (
      DO => USER_RD_DATA(143 downto 72), -- Output read data port, width defined by READ_WIDTH parameter
      DI => USER_WR_DATA(143 downto 72), -- Input write data port, width defined by WRITE_WIDTH parameter
      RDADDR => USER_RD_ADDR, -- Input read address, width defined by read port depth
      RDCLK => CLK, -- 1-bit input read clock
      RDEN => USER_RD_CMD, -- 1-bit input read port enable
      REGCE => '1', -- 1-bit input read output register enable
      RST => RST, -- 1-bit input reset
      WE => we(15 downto 8), -- Input write enable, width defined by write port depth
      WRADDR => USER_WR_ADDR, -- Input write address, width defined by write port depth
      WRCLK => CLK, -- 1-bit input write clock
      WREN =>  USER_WR_CMD-- 1-bit write port enable
   );

end architecture;
