-- gbaser_decode.vhd : 40/100GBASE-R (64/66) multi-lane deecoder
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.gbaser_types.all;

entity gbaser_decode is
    generic (
        LANES : natural := 4
    );
    port (
        RESET        : in std_logic; -- Sync reset - set the FSM into initial state
        CLK          : in std_logic; -- RX clock
        -- PMA interface ----------------------------
        D            : in  std_logic_vector(LANES*66-1 downto 0); -- TX MII data
        -- RS/MAC interface -------------------------
        RXD          : out std_logic_vector(LANES*64-1 downto 0); -- GBASE-R encoded block payload
        RXC          : out std_logic_vector(LANES* 8-1 downto 0); -- TX MII command
        -- Control/status
        BLK_LOCK     : in std_logic := '1'; -- Block lock input
        HI_BER       : in std_logic := '0'; -- Hi BER flag
        BLK_ERR_CNTR : out std_logic_vector(21 downto 0);  -- block error counter
        BLK_ERR_CLR  : in std_logic := '0'; -- Clear block error counter
        DEC_ERROR    : out std_logic_vector(LANES-1 downto 0); -- Block decode error
        SEQ_ERROR    : out std_logic_vector(LANES-1 downto 0); -- Block sequencing error
        VALID_CODE   : out std_logic_vector(LANES-1 downto 0)  -- A valid control block recived
    );
end gbaser_decode;

-- ----------------------------------------------------------------------------
--             Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of gbaser_decode is

type rx_state_t is (IDLE, START, DATA, TERM, ERROR);
type rx_state_arr_t is array (LANES-1 downto 0) of rx_state_t;

signal state_r     : rx_state_t;
signal curr_state  : rx_state_arr_t;
signal err_cntr    : unsigned(BLK_ERR_CNTR'high+1 downto 0);
signal cntr_ov     : std_logic;

begin

encoders_gen: for i in 0 to LANES-1 generate
    signal blk_type   : std_logic_vector(3-1 downto 0);
    signal mii_data   : std_logic_vector(64-1 downto 0);
    signal mii_cmd    : std_logic_vector( 8-1 downto 0);
    signal prev_state : rx_state_t;
begin

    encode_i: entity work.blk_dec
    port map (
        D        => D(i*66+65 downto i*66),
        RXD      => mii_data,
        RXC      => mii_cmd,
        BLK_TYPE => blk_type
    );

    prev_state_0_g: if i = 0 generate
         prev_state <= state_r;
    end generate;
    prev_state_g: if i > 0 generate
        prev_state <= curr_state(i-1);
    end generate;

    curr_state(i) <=
        IDLE  when ((blk_type = C_BLKT_CTRL)  and (prev_state = IDLE  or prev_state = TERM or prev_state = ERROR))  else
        START when ((blk_type = C_BLKT_START) and (prev_state = IDLE  or prev_state = TERM))                        else
        DATA  when ((blk_type = C_BLKT_DATA)  and (prev_state = START or prev_state = DATA or prev_state = ERROR))  else
        TERM  when ((blk_type = C_BLKT_TERM)  and (prev_state = DATA  or prev_state = ERROR))                       else
        ERROR;

    rxd_out_r: process(CLK)
    begin
        if rising_edge(CLK) then
            if (BLK_LOCK = '0') or (HI_BER = '1') then
               -- Too many errors or link down - report local error sequence
                RXD(i*64+63 downto i*64) <= X"00000000010000"  & C_MII_SEQ;
                RXC(i*8 + 7 downto i* 8) <= X"01";
            elsif curr_state(i) = ERROR then
                RXD(i*64+63 downto i*64) <= C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR;
                RXC(i*8 + 7 downto i* 8) <= X"FF";
            else
                RXD(i*64+63 downto i*64) <= mii_data;
                RXC(i*8 + 7 downto i* 8) <= mii_cmd;
            end if;
        end if;
    end process;

    VALID_CODE(i) <= '1' when (blk_type /= C_BLKT_ERR) else '0';
    DEC_ERROR(i)  <= '1' when (blk_type = C_BLKT_ERR)  else '0';
    SEQ_ERROR(i)  <= '1' when (curr_state(i) = ERROR) and (blk_type /= C_BLKT_ERR) else '0';

end generate;

state_r_p: process(CLK)
begin
    if rising_edge(CLK) then
        if reset = '1' then
            state_r <= IDLE;
        else
            state_r <= curr_state(LANES-1);
        end if;
    end if;
end process;

-- Errored blocks counter
blkerr_cntr_p: process(CLK)
variable tmp : natural := 0;
begin
    if rising_edge(CLK) then
        if (reset = '1') or (BLK_ERR_CLR = '1') then
            err_cntr <= (others => '0');
        elsif (BLK_LOCK = '1') and (HI_BER = '0') then
            tmp := 0;
            for i in 0 to LANES-1 loop
                if curr_state(i) = ERROR then
                    tmp := tmp + 1;
                end if;
            end loop;
            if (err_cntr(err_cntr'high) = '0') then -- Increase the counter when not overflowed only
                err_cntr <= err_cntr + tmp;
            end if;
        end if;
    end if;
end process;

BLK_ERR_CNTR <= (others => '1') when err_cntr(err_cntr'high) = '1' else
                std_logic_vector(err_cntr(BLK_ERR_CNTR'range));

end behavioral;
