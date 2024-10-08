-- np_lutram_fixed.vhd: N-port distributed LUT memory with IN / OUT registers and constraints
-- Copyright (C) 2018 CESNET
-- Author(s): Václav Hummel <xhumme00@cesnet.cz>
--            Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-------------------------------------------------------------------------
--                          Description
-------------------------------------------------------------------------
-- This is a version of NP_LUTRAM with added input and output registers
-- and aditional constrains for number of ports. It is only used in
-- the NP_LUTRAM_PRO and whould not be used enywhere else!

entity NP_LUTRAM_FIXED is
   generic(
      DATA_WIDTH : integer := 64; -- any possitive value
      ITEMS      : integer := 256;  -- any possitive value
      WRITE_PORTS: integer := 4; -- >= 2
      READ_PORTS : integer := 8; -- has to be divisible by WRITE_PORTS, >= WRITE_PORTS
      DEVICE     : string  := "7SERIES"
   );
   port(
      -- Registered
      DI         : in  slv_array_t(0 to WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);
      -- Registered
      WE         : in  std_logic_vector(WRITE_PORTS-1 downto 0);
      WCLK       : in  std_logic;
      WCLKN      : in  std_logic; -- has to be WRITE_PORTS*WCLK, same source
      WRESET     : in  std_logic; -- !! MUST BE SYNCHRONISED ON rising_edge(WCLK) !!
      -- Registered
      ADDRA      : in  slv_array_t(0 to WRITE_PORTS-1)(LOG2(ITEMS)-1 downto 0);
      -- Registered
      ADDRB      : in  slv_array_t(0 to READ_PORTS-1)(LOG2(ITEMS)-1 downto 0);
      -- Registered, DOB is valid 2 clock cycles after ADDRB
      DOB        : out slv_array_t(0 to READ_PORTS-1)(DATA_WIDTH-1 downto 0)
   );
end entity;

architecture behavioral of NP_LUTRAM_FIXED is

   -- Write logic

   signal reg1_di_item     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg1_we_item     : std_logic;
   signal reg1_addra_item  : std_logic_vector(log2(ITEMS)-1 downto 0);

   signal reg2_di     : slv_array_t(0 to WRITE_PORTS+1-1)(DATA_WIDTH-1 downto 0);
   signal reg2_we     : std_logic_vector(WRITE_PORTS+1-1 downto 0);
   signal reg2_addra  : slv_array_t(0 to WRITE_PORTS+1-1)(log2(ITEMS)-1 downto 0);

   signal reg2b_di     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg2b_we     : std_logic;
   signal reg2b_addra  : std_logic_vector(log2(ITEMS)-1 downto 0);

   signal cnt        : std_logic_vector(max(log2(WRITE_PORTS),1)-1 downto 0);

   -- Memory
   signal memi_addr  : std_logic_vector((READ_PORTS/WRITE_PORTS+1)*log2(ITEMS)-1 downto 0);
   signal memi_do    : std_logic_vector((READ_PORTS/WRITE_PORTS+1)*DATA_WIDTH-1 downto 0);
   signal mem_dob    : slv_array_t(0 to READ_PORTS/WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);

   -- Read logic

   signal reg1_addrb_item_deser      : std_logic_vector((READ_PORTS/WRITE_PORTS)*log2(ITEMS)-1 downto 0);
   signal reg1_addrb_item      : slv_array_t(0 to READ_PORTS/WRITE_PORTS-1)(log2(ITEMS)-1 downto 0);
   signal reg2_addrb : slv_array_2d_t(0 to WRITE_PORTS+1-1)(0 to READ_PORTS/WRITE_PORTS-1)(log2(ITEMS)-1 downto 0);

   signal reg3_mem_dob : slv_array_2d_t(0 to WRITE_PORTS+1+1-1)(0 to READ_PORTS/WRITE_PORTS-1)(DATA_WIDTH-1 downto 0);

begin

   -- Write logic

   reg1_di_muxi: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      MUX_WIDTH => WRITE_PORTS
   )
   port map(
      DATA_IN => slv_array_ser(DI, WRITE_PORTS, DATA_WIDTH),
      SEL => cnt,
      DATA_OUT => reg1_di_item
   );

   reg1_we_muxi: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => 1,
      MUX_WIDTH => WRITE_PORTS
   )
   port map(
      DATA_IN => WE,
      SEL => cnt,
      DATA_OUT(0) => reg1_we_item
   );

   reg1_addra_muxi: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => log2(ITEMS),
      MUX_WIDTH => WRITE_PORTS
   )
   port map(
      DATA_IN => slv_array_ser(ADDRA, WRITE_PORTS, log2(ITEMS)),
      SEL => cnt,
      DATA_OUT => reg1_addra_item
   );

   -- N registers due to timing
   reg2_we(0) <= reg1_we_item;
   reg2_di(0) <= reg1_di_item;
   reg2_addra(0) <= reg1_addra_item;

   reg2_dig: for i in 0 to WRITE_PORTS-1 generate
      reg2_dip: process(WCLKN)
      begin
         if (WCLKN'event and WCLKN = '1') then
            if (WRESET = '1') then
               reg2_we(i+1) <= '0';
            else
               reg2_we(i+1) <= reg2_we(i);
            end if;
            reg2_di(i+1) <= reg2_di(i);
            reg2_addra(i+1) <= reg2_addra(i);
         end if;
      end process;
   end generate;

   -- Memory

   memi_addr(log2(ITEMS)-1 downto 0) <= reg2_addra(WRITE_PORTS-1);

   memi_addrg: for j in 0 to READ_PORTS/WRITE_PORTS-1 generate
      memi_addr((j+2)*log2(ITEMS)-1 downto (j+1)*log2(ITEMS)) <= reg2_addrb(1)(j);
   end generate;

   lutram_i : entity work.GEN_LUTRAM
   generic map (
      DATA_WIDTH         => DATA_WIDTH,
      ITEMS              => ITEMS,
      RD_PORTS           => READ_PORTS/WRITE_PORTS+1,
      RD_LATENCY         => 0,
      WRITE_USE_RD_ADDR0 => True,
      MLAB_CONSTR_RDW_DC => True,
      DEVICE             => DEVICE
   )
   port map (
      CLK     => WCLKN,
      WR_EN   => reg2_we(WRITE_PORTS-1),
      WR_ADDR => (others => '0'),
      WR_DATA => reg2_di(WRITE_PORTS-1),
      RD_ADDR => memi_addr,
      RD_DATA => memi_do
   );

   mem_dog: for j in 0 to READ_PORTS/WRITE_PORTS-1 generate
      mem_dob(j) <= memi_do((j+2)*DATA_WIDTH-1 downto (j+1)*DATA_WIDTH);
   end generate;

   -- Read logic

   reg1_addrb_muxi: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => READ_PORTS/WRITE_PORTS*log2(ITEMS),
      MUX_WIDTH => WRITE_PORTS
   )
   port map(
      DATA_IN => slv_array_ser(ADDRB, READ_PORTS, log2(ITEMS)),
      SEL => cnt,
      DATA_OUT => reg1_addrb_item_deser
   );

   reg1_addrb_item <= slv_array_to_deser(reg1_addrb_item_deser, READ_PORTS/WRITE_PORTS, log2(ITEMS));

   -- N registers due to timing
   reg2_addrb(0) <= reg1_addrb_item;

   reg2_addrbg: for i in 0 to WRITE_PORTS-1 generate
      reg2_addrbp: process(WCLKN)
      begin
         if (WCLKN'event and WCLKN = '1') then
            reg2_addrb(i+1) <= reg2_addrb(i);
         end if;
      end process;
   end generate;

   -- N registers due to timing
   reg3_mem_dob(0) <= mem_dob;

   reg3_mem_dobg: for i in 0 to WRITE_PORTS+1-1 generate
      reg3_mem_dobp: process(WCLKN)
      begin
         if (WCLKN'event and WCLKN = '1') then
            reg3_mem_dob(i+1) <= reg3_mem_dob(i);
         end if;
      end process;
   end generate;

   -- Output assignment
   reg4_mem_dob_ing: for i in 0 to WRITE_PORTS-1 generate
      reg4_mem_dob_ingg: for j in 0 to READ_PORTS/WRITE_PORTS-1 generate
         DOB(i*(READ_PORTS/WRITE_PORTS)+j) <= reg3_mem_dob(i+1)(j);
      end generate;
   end generate;

   -- CNT logic
   cnt_pr : process (WCLKN)
   begin
      if (rising_edge(WCLKN)) then

         -- Counts from highest position to the lowest
         -- to respect priority on write port 0.
         cnt <= std_logic_vector(unsigned(cnt)-1);

         -- !!!! THE WRESET FALL MUST BE SYNCHRONISED WITH RISING EDGE OF WCLK !!!!
         if (WRESET='1') then
            cnt <= (others => '1');
         end if;
      end if;
   end process;

end architecture;
