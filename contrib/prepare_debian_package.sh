#!/bin/bash -e
INITIAL_FOLDER=$(pwd)
cd ..
VERSION=$(cat Asn1f2/SvnVersion.cs | cut -d \" -f 2)
echo Creating a Debian package for ASN1Scc version 3.0.$VERSION
test -f Asn1f2/bin/Debug/Asn1f2.exe || (echo 'Run ./build.sh first to build ASN1SCC' && false)
rm -rf asn1scc
mkdir -p asn1scc/DEBIAN
mkdir -p asn1scc/usr/local/bin
mkdir -p asn1scc/usr/local/share/asn1scc
cp -r Asn1f2/bin/Debug/* asn1scc/usr/local/share/asn1scc
rm -f asn1scc/usr/local/share/asn1scc/*.mdb
mv asn1scc/usr/local/share/asn1scc/Asn1f2.exe asn1scc/usr/local/share/asn1scc/asn1.exe
cd asn1scc/usr/local/bin
ln -s ../share/asn1scc/* .
cd ../../../..
echo "Package: asn1scc
Version: 3.0.${VERSION}
Section: base
Priority: optional
Architecture: all
Depends: libmono-system-runtime4.0-cil,libmono-corlib4.0-cil,libmono-system-runtime-serialization-formatters-soap4.0-cil, libmono-system-web4.0-cil,libmono-system-xml4.0-cil,libmono-system4.0-cil,mono-runtime,libmono-system-numerics4.0-cil,libmono-system-data-linq4.0-cil,libmono-corlib2.0-cil,libmono-system2.0-cil,libmono-corlib4.5-cil
Maintainer: Thanassis Tsiodras
Description: ASN.1 Space Certified Compiler - Generate Spark/Ada and C code for ASN.1 uPER or custom binary encoders/decoders
Homepage: http://github.com/ttsiodras/asn1scc" > asn1scc/DEBIAN/control
echo '#!/bin/sh
echo "All done!"
' >> asn1scc/DEBIAN/postinst
chmod +x asn1scc/DEBIAN/postinst
dpkg-deb --build asn1scc
cd $INITIAL_FOLDER
mv ../*.deb .
rm -rf ../asn1scc
echo -e 'Done...\n\nThe .deb file is here:\n'
pwd
ls -l *deb
