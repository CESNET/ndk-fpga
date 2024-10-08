#include <iostream>
#include <string>
#include <vector>
#include "dpi_scoreboard_pkg.h"
#include "fl_transaction.h"

using namespace std;

//-----------------------------------------------------------------------------
//- GLOBAL VARIABLES
//-----------------------------------------------------------------------------

/* TX (driver) transaction */
FlTransaction *txTrans = NULL;

/* RX (driver) transaction */
FlTransaction *rxTrans = NULL;

/* Transaction table */
vector<FlTransaction> transTable;
int transTableAdded   = 0;
int transTableRemoved = 0;

//-----------------------------------------------------------------------------
//- USER Functions
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Called after receiving transaction (received to txTrans)
int processPostTx() {
  // txTrans->display();
  transTable.push_back(*txTrans);
  transTableAdded++;
  return 1; // Return 1 when everything is OKEY
}

//-----------------------------------------------------------------------------
// Called after receiving transaction (received to rxTrans)
int processPostRx() {
  int deleted=0;
  // rxTrans->display();
  for (int i=0; i< transTable.size(); i++) {
    if (transTable[i].compare(*rxTrans) && !deleted) {
	  transTable.erase(transTable.begin()+i);
      transTableRemoved++;
	  deleted=1;
	  }
  }
  if (!deleted) {
    cout << "Unexpected transaction received" << endl;
    rxTrans->display();
    }
  return deleted; // Return 1 when everything is OKEY
}


//-----------------------------------------------------------------------------
//- System verilog interface
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
void c_display() {
  cout<<"----------------------------------------------------------------"<<endl;
  cout<<"-- TRANSACTION TABLE (C++)"<<endl;
  cout<<"----------------------------------------------------------------"<<endl;
  cout<<"Size: "          << transTable.size() << endl;
  cout<<"Items added: "   << transTableAdded   << endl;
  cout<<"Items removed: " << transTableRemoved << endl;
  for (int i=0;i<transTable.size();i++)
    transTable[i].display();
  cout<<"----------------------------------------------------------------"<<endl;
}


//-----------------------------------------------------------------------------
// DO NOT MODIFY
int c_flPostTx(const tFlTransactionInfo* info,
               int last,
               const svOpenArrayHandle pkt) {
  int i;
  unsigned char *auxPkt;
  int packetSize = svSize(pkt, 1); // Get packet size
  int result = 1;

  // Allocate txPackets
  if (txTrans == NULL) {
    txTrans = new FlTransaction();
    txTrans->stream_id = info->stream_id;
    txTrans->scenario_id = info->scenario_id;
    txTrans->data_id = info->data_id;
	txTrans->inst = info->inst;
	}

  // Create packet vector
  vector<unsigned char> packetData;
  auxPkt = (unsigned char*) svGetArrayPtr(pkt);
  for (int i=0; i<packetSize; i++)
    packetData.push_back(auxPkt[i]);

  // Insert packet to transaction
  txTrans->data.push_back(packetData);

  if (last) {
    // Call Received
	result = processPostTx();
	delete txTrans;
	txTrans = NULL;
  }
  return result;
}


//-----------------------------------------------------------------------------
// DO NOT MODIFY
int c_flPostRx( const tFlTransactionInfo* info,
                int last,
                const svOpenArrayHandle pkt) {
  int i;
  unsigned char *auxPkt;
  int packetSize = svSize(pkt, 1); // Get packet size
  int result = 1;

  // Allocate txPackets
  if (rxTrans == NULL) {
    rxTrans = new FlTransaction();
    rxTrans->stream_id = info->stream_id;
    rxTrans->scenario_id = info->scenario_id;
    rxTrans->data_id = info->data_id;
	rxTrans->inst=info->inst;
	}

  // Create packet vector
  vector<unsigned char> packetData;
  auxPkt = (unsigned char*) svGetArrayPtr(pkt);
  for (int i=0; i<packetSize; i++)
    packetData.push_back(auxPkt[i]);

  // Insert packet to transaction
  rxTrans->data.push_back(packetData);

  if (last) {
    // Call Received
	result = processPostRx();
	delete rxTrans;
	rxTrans = NULL;
  }
  return result;
}
