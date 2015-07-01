# The directories containing the source files, separated by ':'
VPATH=.

# To make "debug" the default configuration if invoked with just "make":
#
# The source files: regardless of where they reside in the source tree,
# VPATH will locate them...
Group0_SRC = $(shell echo *.c)

# Build a Dependency list and an Object list, by replacing the .c
# extension to .d for dependency files, and .o for object files.
Group0_OBJ = $(patsubst %.c, %.o, ${Group0_SRC})

# Your final binary
TARGET=mainprogram

# What include flags to pass to the compiler
INCLUDEFLAGS= -I .

# Separate compile options per configuration
CFLAGS += -g -Wall -Wextra -D_DEBUG ${INCLUDEFLAGS} -O0 
LDFLAGS += -g 

# A common link flag for all configurations
LDFLAGS +=

all:	${TARGET}

${TARGET}: ${Group0_OBJ}
	@mkdir -p $(dir $@)
	gcc -g -o $@ $^ ${LDFLAGS}

%.o: %.c
	@mkdir -p $(dir $@)
	gcc -c $(CFLAGS) -o $@ $<


clean:
	@rm -rf *.o $(TARGET) 