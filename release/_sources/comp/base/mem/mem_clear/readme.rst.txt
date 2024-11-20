.. _mem_clear:

Memory clear
------------

Simple component that will generate addresses for memory clearing when RST is asserted.

Component port and generics description
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: MEM_CLEAR
   :noautogenerics:


Instance template
^^^^^^^^^^^^^^^^^

.. code-block::

    data_clear_i : entity work.MEM_CLEAR
    generic map (
        DATA_WIDTH  => BOX_WIDTH,
        ITEMS       => BOX_CNT,
        CLEAR_EN    => CLEAR_BY_RST
    )
    port map (
        CLK         => CLK,
        RST         => RST,

        CLEAR_DONE  => RST_DONE,
        CLEAR_WR    => wr_clear,
        CLEAR_ADDR  => wr_addr_clear
    );
