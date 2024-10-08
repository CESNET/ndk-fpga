-- blk_dec.vhd : 40/100GBASE-R block (64/66) single lane encoder
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.gbaser_types.all;

entity blk_dec is
    port (
        -- PMA interface -------------------------
        D        : in  std_logic_vector(65 downto 0); --  GBASE-R encoded block payload
        -- RS/MAC interface --------------------------
        RXD      : out std_logic_vector(63 downto 0);   -- RX MII Data
        RXC      : out std_logic_vector( 7 downto 0); -- RX MII command
        -- Control
        BLK_TYPE : out std_logic_vector(2 downto 0)
        -- TBD: Decode errors
    );
end blk_dec;

-- ----------------------------------------------------------------------------
--             Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of blk_dec is

signal mii_idle      : std_logic_vector(63 downto 0);
signal mii_err       : std_logic_vector(63 downto 0);
signal mii_start     : std_logic_vector(63 downto 0);
signal mii_seq       : std_logic_vector(63 downto 0);
signal mii_term_0    : std_logic_vector(63 downto 0);
signal mii_term_1    : std_logic_vector(63 downto 0);
signal mii_term_2    : std_logic_vector(63 downto 0);
signal mii_term_3    : std_logic_vector(63 downto 0);
signal mii_term_4    : std_logic_vector(63 downto 0);
signal mii_term_5    : std_logic_vector(63 downto 0);
signal mii_term_6    : std_logic_vector(63 downto 0);
signal mii_term_7    : std_logic_vector(63 downto 0);

alias HDR   : std_logic_vector(1 downto 0)  is D(1 downto 0);
alias PAYLD : std_logic_vector(63 downto 0) is D(65 downto 2);
alias RTYPE : std_logic_vector(7 downto 0)  is D(9 downto 2);

begin

mii_err    <= C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR  & C_MII_ERR;
mii_idle   <= C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE;
mii_term_0 <= C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_TERM;
mii_term_1 <= C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_TERM & PAYLD(15 downto 8);
mii_term_2 <= C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_TERM & PAYLD(23 downto 8);
mii_term_3 <= C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_TERM & PAYLD(31 downto 8);
mii_term_4 <= C_MII_IDLE & C_MII_IDLE & C_MII_IDLE & C_MII_TERM & PAYLD(39 downto 8);
mii_term_5 <= C_MII_IDLE & C_MII_IDLE & C_MII_TERM & PAYLD(47 downto 8);
mii_term_6 <= C_MII_IDLE & C_MII_TERM & PAYLD(55 downto 8);
mii_term_7 <= C_MII_TERM & PAYLD(63 downto 8);
mii_start  <= PAYLD(63 downto 8) & C_MII_START;
mii_seq    <= PAYLD(63 downto 8) & C_MII_SEQ;

decode_p: process(all)
begin
    if HDR = D_HDR then
        -- Block contains only data
        BLK_TYPE <= C_BLKT_DATA;
        RXD      <= PAYLD;
        RXC      <= X"00";
    elsif HDR = C_HDR then
        -- Block contains control - more detailed decoding follows
        case RTYPE is
            when BT_C_C  =>
                BLK_TYPE <= C_BLKT_CTRL;
                RXD      <= MII_IDLE;
                RXC      <= X"FF";
            when BT_O_C  =>
                BLK_TYPE <= C_BLKT_CTRL;
                RXD      <= mii_seq;
                RXC      <= X"01";
            when BT_S_D  =>
                BLK_TYPE <= C_BLKT_START;
                RXD      <= mii_start;
                RXC      <= X"01";
            when BT_T_C  =>  -- terminate + 7 controls
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_0;
                RXC      <= X"FF";
            when BT_D1_C =>  -- 1 data + terminate + 6 controls
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_1;
                RXC      <= X"FE";
            when BT_D2_C =>  -- 2 data + terminate + 5 controls
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_2;
                RXC      <= X"FC";
            when BT_D3_C =>  -- 3 data + terminate + 4 controls
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_3;
                RXC      <= X"F8";
            when BT_D4_C =>  -- 4 data + terminate + 3 controls
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_4;
                RXC      <= X"F0";
            when BT_D5_C =>  -- 5 data + terminate + 2 controls
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_5;
                RXC      <= X"E0";
            when BT_D6_C =>  -- 6 data + terminate + 1 control
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_6;
                RXC      <= X"C0";
            when BT_D7_T =>  -- 7 data + terminate
                BLK_TYPE <= C_BLKT_TERM;
                RXD      <= mii_term_7;
                RXC      <= X"80";
            when others =>
                -- Unknown block type = Error
                BLK_TYPE <= C_BLKT_ERR;
                RXD      <= MII_ERR;
                RXC      <= X"FF";
        end case;
    else
       -- Wrong sync header type ("00" or "11") = Error
        BLK_TYPE <= C_BLKT_ERR;
        RXD      <= MII_ERR;
        RXC      <= X"FF";
    end if;

end process;
--

end behavioral;
