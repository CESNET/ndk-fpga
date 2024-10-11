.. _trans_sorter:

Transaction Sorter
------------------

This unit converts out-of-order confirmations of transactions to the original order of the transactions.
The unit has 3 interfaces:

#. Input transactions

    Here, transactions with specific ID and metadata arrive in order *A*.
    The transactions are stored inside until they are confirmed.

#. Input confirmations

    Here arrive confirmation on IDs of transactions in order *B* (may be different from *A*).

#. Output transaction

    Here, confirmed transactions are passed from the unit in order *A*.

Architecture
^^^^^^^^^^^^

.. _trans_sorter_diagram:

.. image:: doc/trans_sorter.svg
      :align: center
      :width: 100 %
      :alt:

The main parts of the architecture are the confirmation memory register array and the transaction sorage FIFO.
When a transaction arrives, it sets the register with the corresponding ID to '0' (not confirmed).
At the same time the transaction is stored in the FIFOX Multi.

When the transaction is propagated to the output of the FIFO, it is pre-loaded to Reg0 together with the corresponsing confirmation value.
This process is repeated with the same transaction as long as the confirmation is not '1'.
This happens when the user sends a confirmation with the same ID as the transaction (the confirmation writes value '1' to the register).

When all the transactions loaded in Reg0 are deemed as confirmed, they are propagated to the output register and a new set of transactions is loaded from the FIFOX Multi (if there are any).

The presence of the Reg0 and the output register has its plus sides and minus sides.

The plus side is that the output transactions are propagated directly from a register, which does not add anything to the user path.
The minus sides are two:

#. If there is only a single valid transaction on the FIFOX Multi output, it is loaded to the Reg0 and no new transactions are loaded until its confirmation even though there is space for multiple transactions.
   This might slightly lower the throughput in some specific cases.

#. The other down side is, that no transactions in Reg0 can be propagated to output register until **all of them** are confirmed.
   This can cause a deadlock when the confirmation input of one transaction is dependent on the output of another transaction.
   Such dependency is for example in the :ref:`CrossbarX<crossbarx>`, where we only use a 1-bit ID.
   To solve this case, when the ID width is 1, the Transaction Sorter only allows transactions with the same ID value to be loaded from the FIFOX Multi to the Reg0.
