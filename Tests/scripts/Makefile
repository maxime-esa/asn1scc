# all:	adaTests cTests 
all:	cTests 

cTests:
	PATH=$$PATH:../../Asn1f4/bin/Debug ./runTests.py -l c

adaTests:
	PATH=$$PATH:../../Asn1f4/bin/Debug ./runTests.py -l Ada

clean:
	rm -rf log.txt tmp.err tmp/
