#include "ada_helpers.h"

#include <stdio.h>
#include <string.h>

#include "001.h"
#include "file_utility.h"

int read_memory(const char *filename, char buffer[]) {
    unsigned char real_buffer[MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING];
    memset(real_buffer, 0, MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING);

    read_from_file(filename, (char *) real_buffer, MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING);

    for (int i = 0; i < MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING; ++i) {
        for (int j = 0; j < 8; ++j) {
            int to_write = (real_buffer[i] & (1 << (7-j))) != 0;
            set(buffer, j+i*8, to_write);
        }
    }
    return 0;
}

int write_memory(const char *filename, char buffer[]) {
    unsigned char real_buffer[MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING];
    memset(real_buffer, 0, MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING);
    for (int i = 0; i < MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING; ++i) {
        for (int j = 0; j < 8; ++j) {
            unsigned char bit = get(buffer, j+i*8);
            real_buffer[i] |= (bit << (7-j));
        }
    }

    write_to_file(filename, (char *) real_buffer, MyInt_REQUIRED_BYTES_FOR_ACN_ENCODING);
    return 0;
}
