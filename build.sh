#!/bin/bash
set -e
MAIN_FOLDER="$(pwd)"
cd parseStg2/
xbuild
cd ../
cd Backend.c.ST/
cp XER.stg xer.stg
../parseStg2/bin/Debug/parseStg2.exe backends.xml
cd ../Backend2.ST/
../parseStg2/bin/Debug/parseStg2.exe backends.xml
cd ../
mkdir -p ./Asn1f2//Resources/
cp SPARK_RTL/adaasn1rtl.* ./Asn1f2//Resources/
cp SPARK_RTL/IgnoredExaminerWarnings.wrn ./Asn1f2//Resources/
cp SPARK_RTL/gnat.cfg ./Asn1f2//Resources/
cp SPARK_RTL/run.sh ./Asn1f2//Resources/
cp SPARK_RTL/GPS_project.gpr ./Asn1f2//Resources/
cp asn1crt/asn1crt.c  ./Asn1f2//Resources/
cp asn1crt/asn1crt.h  ./Asn1f2//Resources/
cp asn1crt/Acn.c ./Asn1f2//Resources/
cp asn1crt/ber.c ./Asn1f2//Resources/
cp asn1crt/xer.c ./Asn1f2//Resources/
cp asn1crt/real.c ./Asn1f2//Resources/
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
