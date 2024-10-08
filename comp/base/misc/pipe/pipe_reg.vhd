-- pipe_reg.vhd: Pipe implemented in two registers
-- Copyright (C) 2017 CESNET
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- -----------------------------------------------------------------------------
--                              Entity declaration
-- -----------------------------------------------------------------------------
entity PIPE_REG is
   generic (
      DATA_WIDTH     : integer := 512;
      FAKE_PIPE      : boolean := false;
      CASCADE_REG    : boolean := true
   );
   port (
      CLK            : in std_logic;
      RESET          : in std_logic;

      IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SRC_RDY     : in  std_logic;
      IN_DST_RDY     : out std_logic;

      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SRC_RDY    : out std_logic;
      OUT_DST_RDY    : in  std_logic
   );
end entity PIPE_REG;

-- -----------------------------------------------------------------------------
--                           Architecture declaration
-- -----------------------------------------------------------------------------
architecture behavioral of PIPE_REG is

   type   fsm_states is (S_EMPTY, S_USED, S_FULL, S_RESET);
   signal present_state, next_state : fsm_states;

   signal in_data1   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_data1  : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_data2  : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal sel        : std_logic := '0';
   signal reg_sel    : std_logic := '0';
   signal reg1_we    : std_logic;
   signal reg2_we    : std_logic;

begin

   fake_reg_true : if(FAKE_PIPE = true) generate
      OUT_DATA    <= IN_DATA;
      OUT_SRC_RDY <= IN_SRC_RDY;
      IN_DST_RDY  <= OUT_DST_RDY;
   end generate;

   fake_reg_false : if(FAKE_PIPE = false) generate
      reg_p : process(CLK)
      begin
         if(CLK'event and CLK = '1') then
            if(reg1_we = '1') then
               reg_data1   <= in_data1;
            end if;

            if(reg2_we = '1') then
               reg_data2   <= IN_DATA;
            end if;

            if(CASCADE_REG = false) then
               reg_sel     <= sel;
            end if;
         end if;
      end process;

      -- -------------------------------------------------------------------------
      --                              CONTROL FSM                               --
      -- -------------------------------------------------------------------------

      -- synchronize logic -------------------------------------------------------
      sync_logicp : process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               present_state <= S_RESET;
            else
               present_state <= next_state;
            end if;
         end if;
      end process;

      -- next state logic --------------------------------------------------------
      nextstate_logicp : process(all)
      begin
         next_state <= present_state;

         case (present_state) is
            when S_EMPTY =>
               if(IN_SRC_RDY = '1') then
                  next_state  <= S_USED;
               end if;

            when S_USED =>
               if   (IN_SRC_RDY = '1' and OUT_DST_RDY = '0') then
                  next_state  <= S_FULL;
               elsif(IN_SRC_RDY = '0' and OUT_DST_RDY = '1') then
                  next_state  <= S_EMPTY;
               end if;

            when S_FULL =>
               if(OUT_DST_RDY = '1') then
                  next_state  <= S_USED;
               end if;

            when S_RESET =>
               next_state <= S_EMPTY;
         end case;
      end process;

      no_cascade_gen : if(CASCADE_REG = false) generate
         OUT_DATA                <= reg_data2 when reg_sel = '1' else reg_data1;
         in_data1                <= IN_DATA;

         -- output logic ------------------------------------------------------------
         output_logicp : process(all)
         begin
            IN_DST_RDY           <= '0';
            OUT_SRC_RDY          <= '0';
            reg1_we              <= '0';
            reg2_we              <= '0';
            sel                  <= reg_sel;

            case (present_state) is
               when S_EMPTY =>
                  IN_DST_RDY     <= '1';
                  reg1_we        <=     reg_sel;
                  reg2_we        <= not reg_sel;
                  sel            <= not reg_sel;

               when S_USED =>
                  IN_DST_RDY     <= '1';
                  OUT_SRC_RDY    <= '1';
                  reg1_we        <=     reg_sel;
                  reg2_we        <= not reg_sel;
                  if(OUT_DST_RDY = '1') then
                     sel         <= not reg_sel;
                  end if;

               when S_FULL =>
                  OUT_SRC_RDY    <= '1';
                  if(OUT_DST_RDY = '1') then
                     sel         <= not reg_sel;
                  end if;

               when S_RESET =>
            end case;
         end process;
      end generate;

      cascade_gen : if(CASCADE_REG = true) generate
         OUT_DATA                <= reg_data1;
         in_data1                <= reg_data2 when sel = '1' else IN_DATA;

         -- output logic ------------------------------------------------------------
         output_logicp : process(all)
         begin
            IN_DST_RDY           <= '0';
            OUT_SRC_RDY          <= '0';
            reg1_we              <= '0';
            reg2_we              <= '0';
            sel                  <= '0';

            case (present_state) is
               when S_EMPTY =>
                  IN_DST_RDY     <= '1';
                  reg1_we        <= '1';
                  reg2_we        <= '1';
                  sel            <= '0';

               when S_USED =>
                  IN_DST_RDY     <= '1';
                  OUT_SRC_RDY    <= '1';
                  reg1_we        <= OUT_DST_RDY;
                  reg2_we        <= '1';
                  sel            <= '0';

               when S_FULL =>
                  OUT_SRC_RDY    <= '1';
                  sel            <= '1';
                  reg1_we        <= OUT_DST_RDY;
                  reg2_we        <= '0';

               when S_RESET =>
            end case;
         end process;
      end generate;

   end generate;

end architecture;
