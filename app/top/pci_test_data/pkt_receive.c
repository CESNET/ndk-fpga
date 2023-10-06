#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#include <err.h>

#include <nfb/nfb.h>
#include <nfb/ndp.h>

#define NDP_PACKET_COUNT 64

// struct ndp_packet {
	// unsigned char *data; // packet data location
	// unsigned char *header; // packet metadata location
	// uint32_t data_length;  // packet data length
	// uint16_t header_length;  // packet metadata length
	// uint16_t flags;  // packet specific flags length
// }

// NDP = Network Data Pane

int main(int argc, char *argv[])
{
    int ret, attempts, pkt_counter, j, k, n;
    struct nfb_device *dev;
    struct ndp_queue *rxq;
    struct ndp_packet pkts[NDP_PACKET_COUNT];			
	// Prepare to reset many-core system
	struct nfb_comp *comp;
	int comp_offs; 
	
	// Output file name
	const char *filename_1 = "vcu118_pci.dat";
	const char *filename_2 = "vcu118_pci_mandelbrot.dat";	
	const char *filename_3 = "vcu118_pci_mandelbrot_image.ppm";
	
	// File pointers
	FILE *fileptr_1, *fileptr_2;
	// Open the file to write the elements
	fileptr_1 = fopen(filename_1, "wb");
	
	char *buffer = (char*)calloc(4, sizeof(char));	
	uint16_t index, value;
	
	// For Mandelbrot conversion 
	// Complex plane x and y coordinates
	const double xmin = -0.27;//-0.2;//0.27085;
	const double xmax = 0.73;//0.7;//0.27100;
	const double ymin = -0.55; //-0.5;//0.004000; //0.004640; 
	const double ymax = 0.45; //0.4;//0.004800; //0.004810;

	// Maximum number of iterations, at most 65535, set to 256 if less than 256
	const int max_iterations = 1000;

	// Image size
	const int xres = 128;
	const int yres = 128;//(xres * (ymax - ymin)) /(xmax - xmin); 

	// Get packets from PCI	
    /* Get handle to NFB device for futher operation */	
    if ((dev = nfb_open("0")) == NULL)
        errx(1, "Can't open device file");

	// Find component in the Device Tree of the dev
	comp_offs = nfb_comp_find(dev, "ziti,minimal,multicore_debug_core",0);
	if (comp_offs < 0)
		errx(1, "Unable to find component."); 

	// Open found component to be accessible
	comp = nfb_comp_open(dev, comp_offs);
	if (comp == NULL)
		errx(1,"Unable to open component.");

    /* Open one RX NDP queue for data transmit */
    rxq = ndp_open_rx_queue(dev, 0);

    if (rxq == NULL)
        errx(1, "Can't open queue");
	
    /* Start queue */
    // They have to be started before any transmission takes place because the
    // packets are dropped otherwise
    ndp_queue_start(rxq);

	// After starting the queue, write 1 to the component.
	// This puts APP_SUBCORE to reset
	nfb_comp_write32(comp, 0, 1);

    // For this case study, we need to fetch 16384 packets.
	// One time though the loop we try to fetch 64.
	pkt_counter = 0;
	while (pkt_counter < 1024) {
		/* Let try to receive some packets */
		for (attempts = 0; attempts < 2000; attempts++) {
			/* Let the library fill at most NDP_PACKET_COUNT, but it may be less */
			ret = ndp_rx_burst_get(rxq, pkts, NDP_PACKET_COUNT);
			if (ret == 0) {
				usleep(100);
				continue;
			}
			else if (ret > 0) {
				break;
			}
		}	
		
		// Write pkts to file
		for (k = 0; k < ret; k++) { 
			fwrite(pkts[k].data, 1, pkts[k].data_length, fileptr_1); 
		} 
	
		// Increment the number of packets
		pkt_counter += ret;
		
		// Release packets that were already read
		ndp_rx_burst_put(rxq);		
	}

	/* Stop queue and cleanup */
    ndp_queue_stop(rxq);
    ndp_close_rx_queue(rxq);
    nfb_close(dev);
	
	fclose(fileptr_1);
	
	// Open file for converting PCI data to Mandelbrot data
	fileptr_1 = fopen(filename_1, "rb");
	fileptr_2 = fopen(filename_2, "wb");
	
	while (!feof(fileptr_1)) {
		fread(buffer, 1, 4, fileptr_1);
		value = (*buffer) & 0x000003ff;
		//index = (*buffer) >> 10;
		//fwrite(&index, 2, 1, fileptr_2);
		fwrite(&value, 2, 1, fileptr_2);
	}
	
	fclose(fileptr_1);
	fclose(fileptr_2); 

	// Convert Mandelbrot data to image PPM
	fileptr_1 = fopen(filename_2, "rb");
	fileptr_2 = fopen(filename_3, "wb");
	
	// Write ASCII header to the file
	fprintf(fileptr_2,
		   "P6\n# Mandelbrot, xmin=%lf, xmax=%lf, ymin=%lf, ymax=%lf, max_iterations=%d\n%d\n%d\n%d\n",
		   xmin, xmax, ymin, ymax, max_iterations, xres, yres, (max_iterations < 128 ? 128 : max_iterations));
	
	fread(&n, 2, 1, fileptr_1);
	for (k = 0; k < yres; k++) 
	{
		for(j = 0; j < xres; j++) 
		{ 
		  fread(&n, 2, 1, fileptr_1);
		  // Compute pixel color depending on num of iterations and write it to file
		  if (n == max_iterations) // Bounded
		  {       
			const unsigned char color[] = {0, 10, 20, 50, 5, 10};
			fwrite(color, 6, 1, fileptr_2);
		  }
		  else // Unbounded
		  {       
			unsigned char color[6];
			color[0] = n >> 2;
			color[1] = n & 200;
			color[2] = n >> 1;
			color[3] = n & 200;
			color[4] = n >> 1;
			color[5] = n & 200;

			fwrite(color, 6, 1, fileptr_2);
		  }
		}
	} 
	
	fclose(fileptr_1);
	fclose(fileptr_2); 
	
    return 0;
}
