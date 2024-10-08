-- gbaser_types.vhd : GBASE-R types and constants definitions package
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

package gbaser_types is

constant C_BLKT_CTRL  : std_logic_vector(2 downto 0) := "000";
constant C_BLKT_START : std_logic_vector(2 downto 0) := "001";
constant C_BLKT_DATA  : std_logic_vector(2 downto 0) := "010";
constant C_BLKT_TERM  : std_logic_vector(2 downto 0) := "011";
constant C_BLKT_ERR   : std_logic_vector(2 downto 0) := "100";

constant C_MII_IDLE   : std_logic_vector(7 downto 0) := X"07";
constant C_MII_START  : std_logic_vector(7 downto 0) := X"FB";
constant C_MII_TERM   : std_logic_vector(7 downto 0) := X"FD";
constant C_MII_ERR    : std_logic_vector(7 downto 0) := X"FE";
constant C_MII_SEQ    : std_logic_vector(7 downto 0) := X"9C";

constant C_HDR   : std_logic_vector(1 downto 0) :=  "01"; -- GBASE-R control block header
constant D_HDR   : std_logic_vector(1 downto 0) :=  "10"; -- GBASE-R data block header
-- Block types (802.3 Figure 82-5)
constant BT_C_C  : std_logic_vector(7 downto 0) := X"1E"; -- 8 controls (idles) in a block   0001_1110
constant BT_O_C  : std_logic_vector(7 downto 0) := X"4b"; -- ordered set + control           0100_1011
constant BT_S_D  : std_logic_vector(7 downto 0) := X"78"; -- start + 7 dat         a         0111_1000
constant BT_T_C  : std_logic_vector(7 downto 0) := X"87"; -- terminate + 7 controls          1000_0111
constant BT_D1_C : std_logic_vector(7 downto 0) := X"99"; -- 1 data + terminate + 6 controls 1001_1001
constant BT_D2_C : std_logic_vector(7 downto 0) := X"aa"; -- 2 data + terminate + 5 controls 1010_1010
constant BT_D3_C : std_logic_vector(7 downto 0) := X"b4"; -- 3 data + terminate + 4 controls 1011_0100
constant BT_D4_C : std_logic_vector(7 downto 0) := X"cc"; -- 4 data + terminate + 3 controls 1100_1100
constant BT_D5_C : std_logic_vector(7 downto 0) := X"d2"; -- 5 data + terminate + 2 controls 1101_0010
constant BT_D6_C : std_logic_vector(7 downto 0) := X"e1"; -- 6 data + terminate + 1 control  1110_0001
constant BT_D7_T : std_logic_vector(7 downto 0) := X"ff"; -- 7 data + terminate              1111_1111
-- Control block codes
constant IDLE_C  : std_logic_vector(6 downto 0) := "0000000"; -- IDLE code, 0x00
constant LPI_C   : std_logic_vector(6 downto 0) := "0000110"; -- LPI code (EEE), 0x06
constant ERR_C   : std_logic_vector(6 downto 0) := "0011110"; -- Error code, 0x1e
constant O_C     : std_logic_vector(3 downto 0) := "0000";    -- O-code, 0x0

constant C_BLK_ERR   : std_logic_vector(65 downto 0) := ERR_C  & ERR_C  & ERR_C  & ERR_C  & ERR_C  & ERR_C  & ERR_C  & ERR_C  & BT_C_C & C_HDR;
constant C_BLK_IDLE  : std_logic_vector(65 downto 0) := IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & BT_C_C & C_HDR;
constant C_BLK_TERM0 : std_logic_vector(65 downto 0) := IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & "0000000" & BT_T_C & C_HDR;

end gbaser_types;
