#!/bin/bash


Asn1f2 -atc -o def/a_c_out/ -c -uPER a.asn1
Asn1f2 -atc -o def/a_ada_out/ -Ada -uPER a.asn1
Asn1f2 -atc -o def/b_ada_out/ -Ada -uPER b.asn1
Asn1f2 -atc -o def/b_c_out/ -c -uPER b.asn1


Asn1f2 -atc -renamePolicy 1 -o p1/a_c_out/ -c -uPER a.asn1
Asn1f2 -atc -renamePolicy 1 -o p1/a_ada_out/ -Ada -uPER a.asn1
Asn1f2 -atc -renamePolicy 1 -o p1/b_ada_out/ -Ada -uPER b.asn1
Asn1f2 -atc -renamePolicy 1 -o p1/b_c_out/ -c -uPER b.asn1

Asn1f2 -atc -renamePolicy 2 -o p2/a_c_out/ -c -uPER a.asn1
Asn1f2 -atc -renamePolicy 2 -o p2/a_ada_out/ -Ada -uPER a.asn1
Asn1f2 -atc -renamePolicy 2 -o p2/b_ada_out/ -Ada -uPER b.asn1
Asn1f2 -atc -renamePolicy 2 -o p2/b_c_out/ -c -uPER b.asn1

Asn1f2 -atc -renamePolicy 0 -o p0/a_ada_out/ -Ada -uPER a.asn1
Asn1f2 -atc -renamePolicy 0 -o p0/b_ada_out/ -Ada -uPER b.asn1
