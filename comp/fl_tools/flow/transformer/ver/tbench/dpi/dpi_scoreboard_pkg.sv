package dpi_scoreboard_pkg;

  // Transaction informations
  typedef struct {
    int stream_id;
    int scenario_id;
    int data_id;
    string inst;
  } tFlTransactionInfo;

  // Called after sending packet (called for each transaction packet)
  import "DPI-C" context function int c_flPostTx(input tFlTransactionInfo info, input int last, input byte unsigned pkt[]);

  // Called after receiving packet (called for each transaction packet)
  import "DPI-C" context function int c_flPostRx(input tFlTransactionInfo info, input int last, input byte unsigned pkt[]);

  // Display status informations
  import "DPI-C" context function void c_display();

endpackage

