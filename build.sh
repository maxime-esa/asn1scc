#!/bin/bash
for i in  */Back*fsproj ; do 
    cat $i | sed 's/\(PreBuildEvent>\)\([^m].*parseStg2.exe\)/\1mono \2/' > tmp.$$ && mv tmp.$$ "$i"
done
set -e
MAIN_FOLDER="$(pwd)"
cd parseStg2/
xbuild
cd ../
cd Backend.c.ST/
mono ../parseStg2/bin/Debug/parseStg2.exe backends.xml
cd ../Backend2.ST/
mono ../parseStg2/bin/Debug/parseStg2.exe backends.xml
cd ../
mkdir -p ./Asn1f2//Resources/
cp SPARK_RTL/adaasn1rtl.* ./Asn1f2//Resources/
cp SPARK_RTL/IgnoredExaminerWarnings.wrn ./Asn1f2//Resources/
cp SPARK_RTL/gnat.cfg ./Asn1f2//Resources/
cp SPARK_RTL/run.sh ./Asn1f2//Resources/
cp SPARK_RTL/GPS_project.gpr ./Asn1f2//Resources/

CRT_FILES="\
	Acn.c\
	asn1crt_acn.h\
	asn1crt_ber.h\
	asn1crt_core.h\
	asn1crt_real.h\
	asn1crt_util.h\
	asn1crt_xer.h\
	asn1crt.h\
	ber.c\
	BitStream.c\
	BitStream.h\
	ByteStream.c\
	ByteStream.h\
	real.c\
	util.c\
	xer.c"

for F in $CRT_FILES; do
	cp asn1crt/$F ./Asn1f2/Resources
done

SVNVERSION=$(git log | head -1 | cut -c8-16)
cd Asn1f2
if [ ! -f SvnVersion.cs ] ; then
    cat >> SvnVersion.cs <<OEF
namespace Asn1f2 { public class Svn    { public const string Version = "$SVNVERSION";    }}
OEF
fi
grep PreBuildEvent Asn1f2.csproj >/dev/null && grep -v TargetFrameworkProfile Asn1f2.csproj | awk 'BEGIN{i=0} /<PreBuildEvent/{i=1;}  {if (i== 0) { print $0; }}  /<\/PreBuildEvent?/{i=0;}' > a && mv a Asn1f2.csproj
cd ../Antlr
xbuild || exit 1
cd "$MAIN_FOLDER"
xbuild || exit 1
cd Asn1f2/
mkdir -p bin/Debug/
cp ../*/*.stg bin/Debug/
echo .stg copied, your compiler is ready, here:
echo "   " $(pwd)/bin/Debug/Asn1f2.exe
