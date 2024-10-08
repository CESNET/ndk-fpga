# Makefile for SystemVerilog DPI Library

# DLL to compile
SCOREBOARD_DLL  = dpi_scoreboard_pkg

ifeq ($(OS), Windows_NT)
	CC=g++
	LL=g++
	INCLUDE=C:\Modeltech\include
	LIB=C:\Modeltech\win32
	LIBS=-lmtipli -lm
	FLAGS=-c
	DLL_FLAGS=-shared -Bsymbolic
	DLL_SUFFIX=dll
	ifeq ($(TERM),cygwin)
		CC=$(WIN_GPLUSPLUS)
		LL=$(WIN_GPLUSPLUS)
	QUOTE="
	else
		QUOTE=
	endif

else # Linux
	PLATFORM=`uname`
	CC=g++
	LL=ld
	INCLUDE=/usr/local/fpga/modeltechdir/Modeltech62g/include
	LIB=
	LIBS=-lm
	FLAGS=-c -fPIC
	DLL_FLAGS=-shared -Bsymbolic -E --allow-shlib-undefined
	DLL_SUFFIX=so
	QUOTE="
endif


all: $(SCOREBOARD_DLL).$(DLL_SUFFIX)

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(SCOREBOARD_DLL).h

#
# Rules for compiling DPI library
#
$(SCOREBOARD_DLL).h: $(SCOREBOARD_DLL).sv
	vlib work
	echo $(QUOTE)import $(SCOREBOARD_DLL)::*; module top; endmodule$(QUOTE) > top.sv
	vlog -sv $(SCOREBOARD_DLL).sv
	vlog -sv -dpiheader $(SCOREBOARD_DLL).h top.sv
	rm -fR top.sv work

$(SCOREBOARD_DLL).$(DLL_SUFFIX): $(SCOREBOARD_DLL).o fl_transaction.o
	$(LL) $(DLL_FLAGS) -o $@ $^ -L$(LIB) $(LIBS)

$(SCOREBOARD_DLL).o: $(SCOREBOARD_DLL).h $(SCOREBOARD_DLL).c
	$(CC) $(FLAGS) -I$(INCLUDE) $(SCOREBOARD_DLL).c

fl_transaction.o: fl_transaction.h fl_transaction.cpp
	$(CC) $(FLAGS) -I$(INCLUDE) fl_transaction.cpp

