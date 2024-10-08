--
-- binder_decl.vhd: FrameLink Binder declarations
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Package declaration
-- ----------------------------------------------------------------------------
package FL_BINDER_DECL is

   -- interface types
   type T_BINDER_QUEUE_POLICY is (most_occupied, round_robin, framed);

end FL_BINDER_DECL;

package body FL_BINDER_DECL is
end FL_BINDER_DECL;
