MODELSIM_PATH=$(dir $(shell which vsim))..

libdpi_pcap.so:dpi_pcap.c
	gcc -std=gnu11 -I$(MODELSIM_PATH)/include -fPIC dpi_pcap.c -o dpi_pcap.o -c
	ld -shared -o libdpi_pcap.so dpi_pcap.o -lpcap

