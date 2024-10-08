-- mark_asfifo.vhd: Asynchronous fifo from BlockRAM memories
-- with packet discarding, created as a modification of asfifo_bram_release
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Description
-- ----------------------------------------------------------------------------
-- Asynchronous FIFO with pointer marking mechanism
-- Setting MARK to '1' makes the FIFO remember current WR PTR
--    (if WR is '1' at the same time the pointer, to which it is currently being written is remembered)
-- Setting DISCARD to '1' makes the write pointer return to last mark
--    (if WR is '1' at the same time the data is written to the marked pointer position)
-- Setting both MARK and DISCARD to '1' causes the mark to remain the same (mark is done after discard)
-- Reading is only allowed up to last mark (the marked data is not read)

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity MARK_ASFIFO is
generic (
   -- Number of items in FIFO
   ITEMS        : natural := 1024;
   -- Data Width
   DATA_WIDTH   : natural := 1024;
   -- You can set additional latency of write pointer to read side.
   WR_PTR_ADD_LATENCY : natural := 0
);
port (
   -- Write interface
   CLK_WR      : in  std_logic;
   RESET_WR    : in  std_logic;

   WR          : in  std_logic;
   DI          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
   FULL        : out std_logic;
   STATUS      : out std_logic_vector(log2(ITEMS+1)-1 downto 0);

   MARK        : in  std_logic; -- mark current WR PTR
   DISCARD     : in  std_logic; -- discard all data after last mark

   -- Read interface
   CLK_RD      : in  std_logic;
   RESET_RD    : in  std_logic;

   RD          : in  std_logic;
   DO          : out std_logic_vector(DATA_WIDTH-1 downto 0);
   EMPTY       : out std_logic;
   -- Empty value in next clock cycle
   NEXT_EMPTY  : out std_logic

);
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of MARK_ASFIFO is

   -- ----------------------------------------------------------------------------
   -- Signals
   -- ----------------------------------------------------------------------------

   -- Marked WR PTR
   signal marked_wr_ptr_reg : unsigned(log2(ITEMS)+1-1 downto 0);
   signal mwr_ptr_shreg : slv_array_t(WR_PTR_ADD_LATENCY downto 0)(log2(ITEMS)+1-1 downto 0);

   -- WR PTR
   signal wr_ptr_reg : unsigned(log2(ITEMS)+1-1 downto 0);

   -- actual WR PTR
   signal wr_ptr_act : unsigned(log2(ITEMS)+1-1 downto 0);

   -- RD PTR
   signal rd_ptr_reg : unsigned(log2(ITEMS)+1-1 downto 0);
   signal rd_ptr_inc : std_logic;

   -- Asynch PTR propagation
   signal wr_ptr_rd_side : std_logic_vector(log2(ITEMS)+1-1 downto 0);
   signal rd_ptr_wr_side : std_logic_vector(log2(ITEMS)+1-1 downto 0);

   -- WR side status
   signal status_u : unsigned(log2(ITEMS+1)-1 downto 0);

   -- RAM output registers signals
   signal out_reg0_en  : std_logic;
   signal out_reg1_en  : std_logic;
   signal out_reg0_vld : std_logic;
   signal out_reg1_vld : std_logic;
   signal ptrs_equal   : std_logic;

   -- ----------------------------------------------------------------------------

begin

   -- ----------------------------------------------------------------------------
   -- Marked WR PTR
   -- ----------------------------------------------------------------------------

   marked_wr_ptr_reg_pr : process (CLK_WR)
   begin
      if (CLK_WR'event and CLK_WR='1') then
         if (MARK='1') then
            marked_wr_ptr_reg <= wr_ptr_act;
         end if;

         if (RESET_WR='1') then
            marked_wr_ptr_reg <= (others => '0');
         end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- WR PTR
   -- ----------------------------------------------------------------------------

   wr_ptr_reg_pr : process (CLK_WR)
   begin
      if (CLK_WR'event and CLK_WR='1') then
         if (WR='1' and FULL='0') then
            wr_ptr_reg <= wr_ptr_act+1;
         else
            wr_ptr_reg <= wr_ptr_act;
         end if;

         if (RESET_WR='1') then
            wr_ptr_reg <= (others => '0');
         end if;
      end if;
   end process;

   -- actual WR PTR
   wr_ptr_act <= wr_ptr_reg when DISCARD='0' else marked_wr_ptr_reg;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- RD PTR
   -- ----------------------------------------------------------------------------

   rd_ptr_reg_pr : process (CLK_RD)
   begin
      if (CLK_RD'event and CLK_RD='1') then
         if (rd_ptr_inc='1') then
            rd_ptr_reg <= rd_ptr_reg+1;
         end if;

         if (RESET_RD='1') then
            rd_ptr_reg <= (others => '0');
         end if;
      end if;
   end process;

   rd_ptr_inc <= out_reg0_en and not ptrs_equal;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- Asynch PTR propagation
   -- ----------------------------------------------------------------------------

   mwr_ptr_shreg(0) <= std_logic_vector(marked_wr_ptr_reg);

   mwr_ptr_shreg_g : for i in 0 to WR_PTR_ADD_LATENCY-1 generate
      mwr_ptr_shreg_p : process (CLK_WR)
      begin
         if (rising_edge(CLK_WR)) then
            if (RESET_WR='1') then
               mwr_ptr_shreg(i+1) <= (others => '0');
            else
               mwr_ptr_shreg(i+1) <= mwr_ptr_shreg(i);
            end if;
         end if;
      end process;
   end generate;

   wr_ptr_propagate_i : entity work.ASYNC_BUS_HANDSHAKE
   generic map(
      DATA_WIDTH => log2(ITEMS)+1
   )
   port map(
      ACLK       => CLK_WR  ,
      ARST       => RESET_WR,
      ADATAIN    => mwr_ptr_shreg(WR_PTR_ADD_LATENCY),
      ASEND      => '1'     ,
      AREADY     => open    ,

      BCLK       => CLK_RD  ,
      BRST       => RESET_RD,
      BDATAOUT   => wr_ptr_rd_side,
      BLOAD      => '1'     ,
      BVALID     => open
   );

   rd_ptr_propagate_i : entity work.ASYNC_BUS_HANDSHAKE
   generic map(
      DATA_WIDTH => log2(ITEMS)+1
   )
   port map(
      ACLK       => CLK_RD  ,
      ARST       => RESET_RD,
      ADATAIN    => std_logic_vector(rd_ptr_reg),
      ASEND      => '1'     ,
      AREADY     => open    ,

      BCLK       => CLK_WR  ,
      BRST       => RESET_WR,
      BDATAOUT   => rd_ptr_wr_side,
      BLOAD      => '1'     ,
      BVALID     => open
   );

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- WR side status and full
   -- ----------------------------------------------------------------------------

   status_u <= wr_ptr_reg-unsigned(rd_ptr_wr_side);
   STATUS   <= std_logic_vector(status_u);

   full_reg_pr : process (CLK_WR)
   begin
      if (CLK_WR'event and CLK_WR='1') then
         FULL <= '0';

         if (    status_u=to_unsigned(ITEMS,status_u'length)        -- no free spaces
             or  (    status_u=to_unsigned(ITEMS-1,status_u'length) -- one free space
                  and WR='1'                                        -- writing
                  and FULL='0'                                      -- writing allowed
                 )
            ) then
            FULL <= '1';
         end if;

         if (RESET_WR='1') then
            FULL <= '0';
         end if;
      end if;
   end process;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- RD side empty
   -- ----------------------------------------------------------------------------

   ptrs_equal <= '1' when unsigned(wr_ptr_rd_side)=rd_ptr_reg else '0';

   ptrs_equal_reg_pr : process (CLK_RD) -- RAM output reg 0 vld
   begin
      if (CLK_RD'event and CLK_RD='1') then
         if (out_reg0_en = '1') then
            out_reg0_vld <= not ptrs_equal;
         end if;

         if (RESET_RD='1') then
            out_reg0_vld <= '0';
         end if;
      end if;
   end process;

   NEXT_EMPTY <= not out_reg0_vld;

   empty_pr : process (CLK_RD)        -- RAM output reg 1 vld
   begin
      if (CLK_RD'event and CLK_RD='1') then
         if (out_reg1_en = '1') then
            out_reg1_vld <= out_reg0_vld;
         end if;

         if (RESET_RD = '1') then
            out_reg1_vld <= '0';
         end if;
      end if;
   end process;

   EMPTY <= not out_reg1_vld;

   -- ----------------------------------------------------------------------------

   -- ----------------------------------------------------------------------------
   -- Data BRAM memory
   -- ----------------------------------------------------------------------------

   bram_i : entity work.SDP_BRAM_BEHAV
   generic map(
      DATA_WIDTH      => DATA_WIDTH,
      ITEMS           => ITEMS     ,
      OUTPUT_REG      => true
   )
   port map(
      WR_CLK      => CLK_WR           ,
      WR_EN       => WR and (not FULL),
      WR_ADDR     => std_logic_vector(wr_ptr_act(log2(ITEMS)-1 downto 0)),
      WR_DIN      => DI               ,

      RD_CLK      => CLK_RD         ,
      RD_RST      => RESET_RD       ,
      RD_CE       => out_reg0_en    ,
      RD_REG_CE   => out_reg1_en    ,
      RD_EN       => std_logic'('1'),
      RD_ADDR     => std_logic_vector(rd_ptr_reg(log2(ITEMS)-1 downto 0)),
      RD_DOUT     => DO             ,
      RD_DOUT_VLD => open
   );

   out_reg0_en <= out_reg1_en or (not out_reg0_vld);
   out_reg1_en <= RD or (not out_reg1_vld);

   -- ----------------------------------------------------------------------------

end architecture;
