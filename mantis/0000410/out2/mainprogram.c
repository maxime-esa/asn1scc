#include <stdio.h>
#include <memory.h>
#include <math.h>
#include <float.h>
#include <limits.h>
#include "asn1crt.h"

#include "PUS.h"

typedef unsigned short uint16_t;

#define CRC16 0x8005

uint16_t gen_crc16(const byte *data, uint16_t size)
{
    uint16_t out = 0;
    int bits_read = 0, bit_flag;

    /* Sanity check: */
    if(data == NULL)
        return 0;

    while(size > 0)
    {
        bit_flag = out >> 15;

        /* Get next bit: */
        out <<= 1;
        out |= (*data >> bits_read) & 1; // item a) work from the least significant bits

        /* Increment bit counter: */
        bits_read++;
        if(bits_read > 7)
        {
            bits_read = 0;
            data++;
            size--;
        }

        /* Cycle check: */
        if(bit_flag)
            out ^= CRC16;

    }

    // item b) "push out" the last 16 bits
    int i;
    for (i = 0; i < 16; ++i) {
        bit_flag = out >> 15;
        out <<= 1;
        if(bit_flag)
            out ^= CRC16;
    }

    // item c) reverse the bits
    uint16_t crc = 0;
    i = 0x8000;
    int j = 0x0001;
    for (; i != 0; i >>=1, j <<= 1) {
        if (i & out) crc |= j;
    }

    return crc;
}


int main(int argc, char* argv[])
{
	(void)argc;
	(void)argv;


    static byte encBuff[TM_PACKET_REQUIRED_BYTES_FOR_ACN_ENCODING];
	BitStream bitStrm;
	BitStream bitStrm_aux;
	flag ret;
	int errCode;
	int i;
	//telemetry packet to be encoded
	static TM_PACKET tm_packet = 
		{
			.header = {
				.applicationProcessID = 0,
				.grouping_flags = first_packet,
				.sequence_count = 0
			},
			.data = {
				.header = {
					.packetSubcounter = 0,
					.destinationID = 0,
					.absTime = 0
				},
				.sourceData = {
					.kind = tcVerification_PRESENT,
					.u = { .tcVerification = {
					.kind = tcAcceptanceReport_PRESENT,
					.u = { .tcAcceptanceReport = 0}
				}}
				}
			},
			.exist = {
				.data = 1
			}
		};
	
	
	
	//initialize bit stream;
  	BitStream_Init(&bitStrm, encBuff, TM_PACKET_REQUIRED_BYTES_FOR_ACN_ENCODING);
	
    // Encode value
    ret = TM_PACKET_ACN_Encode(&tm_packet, &bitStrm, &errCode, TRUE);
	asn1SccSint encoded_data_length = BitStream_GetLength(&bitStrm);
	
	//encode length field;
	bitStrm_aux.buf = bitStrm.buf;
	bitStrm_aux.count = bitStrm.count;
	bitStrm_aux.currentByte = 4;
	bitStrm_aux.currentBit = 0; 
	BitStream_EncodeConstraintWholeNumber(&bitStrm_aux, encoded_data_length - 6, 0, 0xFFFF);
	

	//encode crc field;
	bitStrm_aux.buf = bitStrm.buf;
	bitStrm_aux.count = bitStrm.count;
	bitStrm_aux.currentByte = bitStrm.currentByte - 2;
	bitStrm_aux.currentBit = 0; 
	uint16_t crc = gen_crc16(encBuff, bitStrm.currentByte);
	BitStream_EncodeConstraintWholeNumber(&bitStrm_aux, crc, 0, 0xFFFF);
	
	
    if (ret) {
		
		for(i=0; i<encoded_data_length; i++) {
			printf("%02x ", encBuff[i] & 0xff);
		}
		printf("\n");
		
		return 0;
	}	else {
		printf("Encoding failed. Error code is %d", errCode);
		return 1;
	}
}