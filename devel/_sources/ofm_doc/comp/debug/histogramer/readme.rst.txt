.. _histogramer:

Histogramer
------------------

Histogramer is used to manage a histogram.

Key features
^^^^^^^^^^^^^^^^^^^^^

* Histogram boxes are stored inside Block RAM
* Each box will be sequentially cleared after the reset 
* A new input request will increment the histogram box based on an input value
* Read request will read the content of a given box
* Read requests can be set to clear box content after execution
* Input or read request priority can be set
* A new read or write request can be processed in every clock cycle
* Collisions during read-modify-write access to Block RAM are handled

Component port and generics description
^^^^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: HISTOGRAMER
   :noautogenerics:


Instance template
^^^^^^^^^^^^^^^^^^^^^

.. code-block::

    histogrammer_i : entity work.HISTOGRAMER
    generic map(
        INPUT_WIDTH             => INPUT_WIDTH,
        BOX_WIDTH               => BOX_WIDTH,
        BOX_CNT                 => BOX_CNT,
        READ_PRIOR              => READ_PRIOR,
        CLEAR_BY_READ           => CLEAR_BY_READ,
        CLEAR_BY_RST            => CLEAR_BY_RST
    )
    port map(
        CLK                     => CLK,
        RST                     => RST,
        RST_DONE                => rst_done,

        INPUT                   => input,
        INPUT_VLD               => input_vld,

        READ_REQ                => read_req,
        READ_ADDR               => read_addr,
        READ_BOX_VLD            => read_box_vld,
        READ_BOX                => read_box
    );

