.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Whole MFB interface 

.. _uvm_mfb_env:

MFB environment 
---------------



ITEM    - šířka itemu musí být menší nebo rovna 8. Mohl by se vygenerovat sequence_item pouze s 1 bytem. To by znamenalo to, že se do itemu zapíše pouze 1 byte a o datech ve zbytku itemu se nebude dát rozhodnout jaká by měla hodnotu. 
        - šířka itemu musí být celočíselně dělitelná 8(Aby se dala vygenerovat zarovnaná slova pomocí byte_array)
        