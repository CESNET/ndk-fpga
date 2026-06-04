SETTINGS = {
    # default combination. All parameters have to be in
    # package with generic. For example generic.sv
    "default" : {
        "RX_TDATA_WIDTH"      : 64,
        "TX_TDATA_WIDTH"      : 64,
        "TUSER_WIDTH"         : 64,
        # Core params setup variable in environment
        "__core_params__"  : {"UVM_TEST" : "test::base" },
    },
    "rx_1": {
        "RX_TDATA_WIDTH": 32,
    },
    "rx_2": {
        "RX_TDATA_WIDTH": 79,
    },
    "rx_3": {
        "RX_TDATA_WIDTH": 179,
    },
    "rx_4": {
        "RX_TDATA_WIDTH": 23,
    },
    "tx_1": {
        "TX_TDATA_WIDTH": 32,
    },
    "tx_2": {
        "TX_TDATA_WIDTH": 64,
    },
    "tx_3": {
        "TX_TDATA_WIDTH": 128,
    },
    "tx_4": {
        "TX_TDATA_WIDTH": 256,
    },
    "user_1": {
        "TUSER_WIDTH": 64,
    },
    "user_2": {
        "TUSER_WIDTH": 31,
    },
    # test uses combination setup above
    "_combinations_" : {
        "test_base"    :  ("default",),

        "test_rx1_tx1" :  ("default", "rx_1", "tx_1", "user_1"),
        "test_rx1_tx2" :  ("default", "rx_1", "tx_2", "user_2"),
        "test_rx1_tx3" :  ("default", "rx_1", "tx_3", "user_1"),
        "test_rx1_tx4" :  ("default", "rx_1", "tx_4", "user_2"),

        "test_rx2_tx1" :  ("default", "rx_2", "tx_1", "user_2"),
        "test_rx2_tx2" :  ("default", "rx_2", "tx_2", "user_1"),
        "test_rx2_tx3" :  ("default", "rx_2", "tx_3", "user_2"),
        "test_rx2_tx4" :  ("default", "rx_2", "tx_4", "user_1"),

        "test_rx3_tx1" :  ("default", "rx_3", "tx_1", "user_1"),
        "test_rx3_tx2" :  ("default", "rx_3", "tx_2", "user_2"),
        "test_rx3_tx3" :  ("default", "rx_3", "tx_3", "user_1"),
        "test_rx3_tx4" :  ("default", "rx_3", "tx_4", "user_2"),

        "test_rx4_tx1" :  ("default", "rx_4", "tx_1", "user_2"),
        "test_rx4_tx2" :  ("default", "rx_4", "tx_2", "user_1"),
        "test_rx4_tx3" :  ("default", "rx_4", "tx_3", "user_2"),
        "test_rx4_tx4" :  ("default", "rx_4", "tx_4", "user_1"),
    }
}
