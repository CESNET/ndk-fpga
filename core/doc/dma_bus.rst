DMA Bus
=======

Multiple components in the system share a single DMA bus. To route completion to the
correct component, requests must be identified using routing metadata.
For this purpose, the DMA bus uses the ``UNIT_ID`` field as described below.

For each junction of two DMA components, a unique bit in the ``UNIT_ID`` is selected
(this is only necessary for connections where both DMA components generate Read Requests;
connections where one side generates only Write Requests do not need
to be marked for routing, as they do not use the downstream bus).

In the **upstream** direction (request), this bit is set in the DMA request header
to 0 or 1 depending on the relevant branch of the DMA bus.

In the **downstream** direction (response), the value of this bit in the ``UNIT_ID`` field
of the DMA completion header determines whether the response should be routed
to the left or right branch of the DMA bus tree.

For simplicity, the bit number corresponds to the depth of the respective connection.
This information is propagated as a generic to all DMA components of the system,
whereby this parameter is modified by the respective function at each use (junction)
and passed on to descendants.

Routing Tree Structure
----------------------

.. code-block:: none

       ROOT
        |      PATH
        |                  junc := dma_route_junction(parent_path, 2)  -- create junction on path
   ----------- JUNCTION
   |         |             child_path(i) := dma_route_path(junc, i)    -- create paths from junction
   | PATH 0  | PATH 1


Example of Usage for Application Core
--------------------------------------

Generic declarations:

.. code-block:: vhdl

   -- Application core gets generic DMA_ROUTES for all endpoints (already existing code).
   DMA_ROUTES            : dma_route_path_array_t := dma_route_path_array_default(DMA_ENDPOINTS);

Constant declarations:

.. code-block:: vhdl

   -- Application uses just PCI endpoint 0, but splits DMA_BUS to 2 subcores.
   constant PCIE0                     : natural := 0;
   constant SUBCORES                  : natural := 2;
   constant DMA_ROUTE_APP_JUNC        : dma_route_junction_t := dma_route_junction(DMA_ROUTES(PCIE0), SUBCORES);

   -- We need a specific helper function to create dynamically initialized array of paths, this one is simple.
   function dma_paths_f return dma_route_path_array_t is
       variable ret : dma_route_path_array_t(0 to SUBCORES-1);
   begin
       for i in 0 to SUBCORES-1 loop
           ret(i) := dma_route_path(DMA_ROUTE_APP_JUNCTION, i);
       end loop;
       return ret;
   end function;

   -- Description of route for every child created by junction (switch).
   constant SUBCORE_DMA_PATHS : dma_route_path_array_t := dma_paths_f;

   -- This signal holds switching value for MFB_SPLITTER; this one is a bit (to differentiate just 2 subcores), not a vector.
   signal dma_down_mvb_switch      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DMA_BUS_CFG.RES.D.REGIONS-1 downto 0);

Architecture body — Request part (upstream):


.. code-block:: vhdl

   -- Apply current routing to header signals from subcores
   req_mvb_routed_header_gen : for e in 0 to DMA_BUS_CFG.REQ.D.REGIONS-1 generate
      subtype HDR_R is natural range (e+1)*DMA_BUS_CFG.REQ.H.ITEM_WIDTH-1 downto e*DMA_BUS_CFG.REQ.H.ITEM_WIDTH;
   begin
      dma_req_mvb_data_routed0(HDR_R) <= dma_route_req_apply_path(SUBCORE_DMA_PATHS(0), dma_rq_mvb_data0(HDR_R));
      dma_req_mvb_data_routed1(HDR_R) <= dma_route_req_apply_path(SUBCORE_DMA_PATHS(1), dma_rq_mvb_data1(HDR_R));
   end generate;

Use MFB_MERGER to create junction functionality on upstream:

.. code-block:: vhdl

   dmabus_merger_i : entity work.MFB_MERGER
   port map (RX0_MVB_HDR => dma_req_mvb_data_routed0, RX1_MVB_HDR => dma_req_mvb_data_routed1);

Architecture body — Response (completion) part (downstream):


.. code-block:: vhdl

   -- Get the current routing vector for switching
   down_mvb_switch_gen : for e in 0 to DMA_BUS_CFG.RES.D.REGIONS-1 generate
      subtype HDR_R is natural range (e+1)*DMA_BUS_CFG.RES.H.ITEM_WIDTH-1 downto e*DMA_BUS_CFG.RES.H.ITEM_WIDTH;
   begin
       dma_down_mvb_switch(PCIE0)(e) <= dma_route_res_extract_switch(DMA_ROUTE_APP_JUNC, DMA_DOWN_MVB_DATA(PCIE0)(HDR_R))(0);
   end generate;

Use MFB_SPLITTER to create junction functionality on downstream:

.. code-block:: vhdl

   dmabus_splitter_i : entity work.MFB_SPLITER
   port map (RX_MVB_SWITCH => dma_down_mvb_switch(PCIE0));
