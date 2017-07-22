#ifndef ADA_HELPERS_H
#define ADA_HELPERS_H

extern int get(char buffer[], int index);
extern void set(char buffer[], int index, int value);

int read_memory(const char *filename, char buffer[]);
int write_memory(const char *filename, char buffer[]);

#endif //ADA_HELPERS_H
