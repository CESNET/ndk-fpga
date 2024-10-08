#ifndef INCLUDED_FL_TRANSACTION
#define INCLUDED_FL_TRANSACTION

#include <iostream>
#include <string>
#include <vector>

using namespace std;

//-----------------------------------------------------------------------------
// Transaction Class
class FlTransaction {

  public:
    int stream_id;
    int	scenario_id;
	int data_id;
	string inst;
    vector< vector <unsigned char> > data;

    //-----------------------------------------------------------------------------
    int getPacketCount();

    //-----------------------------------------------------------------------------
    int getPacketSize(int packetNo);

    //-----------------------------------------------------------------------------
	int compare(FlTransaction tr, int kind=0);

    //-----------------------------------------------------------------------------
	void display();
};

#endif
