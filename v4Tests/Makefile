export PATH:=$(realpath ../Asn1f4/bin/Debug/):$(PATH)

$(info ${PATH})

all:	adaTests cTests

cTests:
	./scripts/runTests.py -l c

adaTests:
	./scripts/runTests.py -l Ada

