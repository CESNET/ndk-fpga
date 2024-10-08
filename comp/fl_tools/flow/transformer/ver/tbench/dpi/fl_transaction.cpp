#include <iostream>
#include <string>
#include <vector>
#include "fl_transaction.h"

using namespace std;

//-----------------------------------------------------------------------------
int FlTransaction::getPacketCount() {
  return data.size();
}

//-----------------------------------------------------------------------------
int FlTransaction::getPacketSize(int packetNo) {
  return data[packetNo].size();
}

//-----------------------------------------------------------------------------
int FlTransaction::compare(FlTransaction tr, int kind) {
  int resultSizes = 1;
  int result      = 1;
	// First kind of compare
	if (kind == 0) {
        // Check Sizes first
        if (getPacketCount() == tr.getPacketCount()) {
          for (int i=0; i<getPacketCount(); i++) {
		    if (getPacketSize(i) != tr.getPacketSize(i))
			  resultSizes = 0;

		  }
		} // packet count
		else
		  resultSizes = 0;

        // Check data
		if (resultSizes) {
          for (int i=0; i<getPacketCount(); i++)
            for (int j=0; j<getPacketSize(i); j++)
			  if (data[i][j] != tr.data[i][j])
			    result = 0;
		}
		else
		  result = 0;
	  } // Kind 0
  	  return result;
	}

//-----------------------------------------------------------------------------
void FlTransaction::display() {
    cout << "--------------------" << endl;
    cout << "Transaction" << endl;
    cout << "StreamID: " << stream_id << endl;
	  cout << "ScenarioID: " << scenario_id << endl;
	  cout << "DataID: " << data_id << endl;
	  cout << "Inst: " << inst << endl;

      for (int i=0; i<getPacketCount(); i++) {
        cout << "PKT " << i << ": ";
        for (int j=0; j<getPacketSize(i); j++)
          cout << std::hex << (unsigned int) data[i][j];
        cout <<endl;
        }
      cout << "--------------------" << endl;
 	}

