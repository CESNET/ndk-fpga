--! cmp48_top.vhd
--!
--! \file
--! \brief MUL  implemented with Virtex-7 DSP slice
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
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

--! \brief DSP slice ALU entity
entity MI_register_array_top is
    generic (
         MI_WIDTH : integer := 32;
         NUM_REGS : integer := 3;
         MI_ADDR_WIDTH : integer := 32
    );
    port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;

      --! MI32 input interface -------------------------------------------------
      --! Input Data
      MI_DWR                        : in  std_logic_vector(MI_WIDTH-1 downto 0);
      --! addres
      MI_ADDR                       : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
      --! Read Request
      MI_RD                         : in  std_logic;
      --! Write Request
      MI_WR                         : in  std_logic;
      --! Byte Enable
      MI_BE                         : in  std_logic_vector(MI_WIDTH/8-1  downto 0);
      --! Output Data
      MI_DRD                        : out std_logic_vector(MI_WIDTH-1 downto 0);
      --! Address Ready
      MI_ARDY                       : out std_logic;
      --! Data Ready
      MI_DRDY                       : out std_logic;

      --! registers Data output
      REG_DATA_OUT                  : out std_logic_vector((NUM_REGS*MI_WIDTH)-1 downto 0);
      --! MI_WR signals
      REG_WR_OUT                    : out std_logic_vector(NUM_REGS-1 downto 0);
      --! MI_RD signals
      REG_RD_OUT                    : out std_logic_vector(NUM_REGS-1 downto 0);
      --! users data input
      REG_DATA_IN                   : in std_logic_vector((NUM_REGS*MI_WIDTH)-1 downto 0);
      --! users we signal
      REG_WE_IN                     : in std_logic_vector(NUM_REGS-1 downto 0);
      --! MI_ARDY signal from extern register
      REG_ARDY_IN                   : in std_logic_vector(NUM_REGS-1 downto 0)
   );
end MI_register_array_top;

architecture full of MI_register_array_top is
begin

   uut : entity work.MI_REGISTER_ARRAY(full)
   generic map(
      MI_WIDTH => MI_WIDTH,
      MI_ADDR_WIDTH => MI_ADDR_WIDTH,
      NUM_REGS => NUM_REGS,
      SIGN_BITS_ADDR => 32,
      MI_PIPE => false,
      FIRST_ADDR => (MI_ADDR_WIDTH-1 downto 0 => '0'),
      INICIAL => X"C0000003C0000002C0000001",

      --! range musi byt od "1 to (pocet registov)"
      GENER_REGS(1 to 3) =>  ( --! registers data width
                              (DATA_WIDTH => 31,                --! nastavujem generiky pre 1. register
                               --! true - inter , false - exter
                               INTER => true,
                               --! support MI read
                               MI_RD_EN => true,
                               --! support MI write
                               MI_WR_EN => true,
                               --! support user write
                               USR_WR_EN => true,
                               --! response to reset
                               RST_EN => true,
                               --! support MI_BE signal
                               BE_EN => true),

                              (DATA_WIDTH => 32,  --! nastavujem generiki pre 2. register
                               INTER => true,
                               MI_RD_EN => true,
                               MI_WR_EN => true,
                               USR_WR_EN => true,
                               RST_EN => true,
                               BE_EN => true),

                              (DATA_WIDTH => 31,  --! nastavujem generiki pre 3. register
                               INTER => false,
                               MI_RD_EN => true,
                               MI_WR_EN => true,
                               USR_WR_EN => true,
                               RST_EN => true,
                               BE_EN => false)
                            )
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      REG_DATA_OUT   => REG_DATA_OUT,
      REG_DATA_IN    => REG_DATA_IN,
      REG_WR_OUT     => REG_WR_OUT,
      REG_RD_OUT     => REG_RD_OUT,
      REG_WE_IN      => REG_WE_IN,
      REG_ARDY_IN    => REG_ARDY_IN,
      MI_DWR         => MI_DWR,
      MI_ADDR        => MI_ADDR,
      MI_RD          => MI_RD,
      MI_WR          => MI_WR,
      MI_BE          => MI_BE,
      MI_DRD         => MI_DRD,
      MI_ARDY        => MI_ARDY,
      MI_DRDY        => MI_DRDY
   );

end full;
