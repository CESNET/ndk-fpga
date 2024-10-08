-- stat_unit_ent.vhd: Entity of statistical unit with RFC2819 support
-- Copyright (C) 2009,2013 CESNET
-- Author(s): Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity stat_unit is
 generic(
   --! IFG detector setup
   EOP_POS_WIDTH     : integer := 3; --EOP_POS bus width
   SOP_ALIGN_WIDTH   : integer := 1; --SOP_ALIGN bus width
   ETH_CLK_SIZE      : integer := 8; --A number of bytes transfered in one clock

   --! Counters&regs setup
   DELAY_EN             : boolean := true;
   CRC_EN               : boolean := true;
   MAC_EN               : boolean := true;
   MTU_EN               : boolean := true;
   SIZE_EN              : boolean := true;
   READ_DELAY_EN        : boolean := true;
   BCAST_MCAST_EN       : boolean := true;
   FRAGMENT_JABBER_EN   : boolean := true;
   PAYLOAD_HISTOGRAM_EN : boolean := true;
   UNDERSIZE_FRAMES_EN  : boolean := true;
   CNT_DSP              : boolean := true;

   --! CRC from the packet is removed
   INBANDFCS            : boolean := true
   );
 port (
   -- -----------------------------------------------------
	--! \name Common input
   -- -----------------------------------------------------
   CLK	: in std_logic;
	RESET	: in std_logic;

   -- -----------------------------------------------------
	--! \name Statistics input data
   -- -----------------------------------------------------
   SOP                     : in std_logic;
   EOP                     : in std_logic;
   EOP_POS                 : in std_logic_vector(EOP_POS_WIDTH-1 downto 0);
   SOP_ALIGN_SIZE          : in std_logic_vector(SOP_ALIGN_WIDTH-1 downto 0);

   --! Statistical inputs(active when stat_dv is 1)
   STAT_PAYLOAD_LEN        : in std_logic_vector(15 downto 0);
   STAT_FRAME_ERROR        : in std_logic; -- 0: OK, 1: Error occured
   STAT_CRC_CHECK_FAILED   : in std_logic; -- 0: OK, 1: Bad CRC
   STAT_MAC_CHECK_FAILED   : in std_logic; -- 0: OK, 1: Bad MAC
   STAT_LEN_BELOW_MIN      : in std_logic; -- 0: OK, 1: Length is below min
   STAT_LEN_OVER_MTU       : in std_logic; -- 0: OK, 1: Length is over MTU
   STAT_FRAME_RECEIVED     : in std_logic; -- 0: Nothing, 1: Correctly received packet
   STAT_FRAME_DISCARDED    : in std_logic; -- 0: OK, 1: Frame was discarded
   STAT_BUFFER_OVF         : in std_logic; -- 0: OK, 1: Buffer overflow
   STAT_MAC_BCAST          : in std_logic; -- 0: Nothing, 1:Broadcast packet detected
   STAT_MAC_MCAST          : in std_logic; -- 0: Nothing, 1:Multicast packet detected
   STAT_DV                 : in std_logic; -- Data valid

   -- -----------------------------------------------------
   --! \name Control interface
   -- -----------------------------------------------------
   START_EN               : in std_logic;    --Enable statistics
   SW_RESET               : in std_logic;    --SW reset
   RESET_AFTER_READ       : in std_logic_vector(25 downto 0); --Reset after read
   READ_EN                : in std_logic;    --Read enable (snapshot)
   LAST_ADDR_EN           : in std_logic;    --Last address enable (release snapshot)

   -- -----------------------------------------------------
   --! \name Statistics output
   -- -----------------------------------------------------
   --! Input statistic are valid
   OUT_STAT_DV             : out std_logic;
   --! Discarded packets due to MAC check failure
   OUT_MAC_CHECK_FAILED    : out std_logic_vector(63 downto 0);
   --! Total number of succ. received packets
   OUT_FRAMES_RECEIVED     : out std_logic_vector(63 downto 0);
   --! Total number of discarded packets
   OUT_FRAMES_DISCARDED    : out std_logic_vector(63 downto 0);
   --! Total number of processed packets
   OUT_TOTAL_PACKET_TRAF   : out std_logic_vector(63 downto 0);
   --! Discarded due to buffer overflow
   OUT_BUFFER_OVF          : out std_logic_vector(63 downto 0);
   --! Total amount of packets which are used in sum
   OUT_SIZE_SUM_COUNT      : out std_logic_vector(63 downto 0);
   --! Total number of processed octets (received and
   --! discarded - with CRC octets)
   OUT_SIZE_SUM            : out std_logic_vector(63 downto 0);
   --! Total number of received octets (without CRC)
   OUT_SIZE_SUM_OK         : out std_logic_vector(63 downto 0);
   --! Total number of discarded packets due to buffer overlflow
   OUT_CRC_ERR             : out std_logic_vector(63 downto 0);
   --! Total number of packets over MTU
   OUT_OVER_MTU            : out std_logic_vector(63 downto 0);
   --! Total number of packets below minimal length
   OUT_BELOW_MIN           : out std_logic_vector(63 downto 0);
   --! Maximal received size
   OUT_MAX_SIZE            : out std_logic_vector(15 downto 0);
   --! Minimal received size
   OUT_MIN_SIZE            : out std_logic_vector(15 downto 0);
   --! Minimal byte delay between packets
   OUT_MIN_DELAY           : out std_logic_vector(63 downto 0);
   --! Maximal byte delay between packets
   OUT_MAX_DELAY           : out std_logic_vector(63 downto 0);
   --! Delay between two reads from the statistical unit
   OUT_LAST_READ_DELAY     : out std_logic_vector(63 downto 0);
   --! Total amount of received broadcast frames
   OUT_BCAST_FRAMES        : out std_logic_vector(63 downto 0);
   --! Total amount of received multicast frames that were not
   --! identified as broadcast
   OUT_MCAST_FRAMES        : out std_logic_vector(63 downto 0);
   --! Total amount of received "fragment" frames
   OUT_FRAGMENT_FRAMES     : out std_logic_vector(63 downto 0);
   --! Total amount of received "jabber" frames
   --! (frames above 1518 bytes including FCS)
   OUT_JABBER_FRAMES       : out std_logic_vector(63 downto 0);
   --! Counter of under size packets
   OUT_UNDERSIZE_FRAMES    : out std_logic_vector(63 downto 0);
   --! Frame length histograms
   OUT_FRAMES_64           : out std_logic_vector(63 downto 0);
   OUT_FRAMES_65_127       : out std_logic_vector(63 downto 0);
   OUT_FRAMES_128_255      : out std_logic_vector(63 downto 0);
   OUT_FRAMES_256_511      : out std_logic_vector(63 downto 0);
   OUT_FRAMES_512_1023     : out std_logic_vector(63 downto 0);
   OUT_FRAMES_1024_1518    : out std_logic_vector(63 downto 0);
   OUT_FRAMES_OVER_1518    : out std_logic_vector(63 downto 0)
 );
end entity stat_unit;
