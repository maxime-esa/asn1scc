#!/bin/bash
Asn1f2.exe -c -ACN -o out2/ PUS.asn1 PUS.acn || exit 1
cd out2 || exit 1
make || exit 1
./mainprogram
 