#!/bin/bash
echo Checking for Java 1.6 or 1.7 ...
java -version 2>&1 | egrep '"1\.[67]' || {
    echo Either Java is not installed or your Java version is not 1.7 or 1.6.
    echo The invocation of ANTLR may fail - if that happens, please switch
    echo your JRE to 1.7 or 1.6
    echo
    echo Press ENTER to continue
    read ANS
}
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
