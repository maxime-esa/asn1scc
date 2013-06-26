#!/bin/bash
set -e
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
SVNVERSION=$(svnversion)
cd Asn1f2
if [ ! -f SvnVersion.cs ] ; then
    cat >> SvnVersion.cs <<OEF
namespace Asn1f2 { public class Svn    { public const string Version = "$SVNVERSION";    }}
OEF
fi
grep PreBuildEvent Asn1f2.csproj >/dev/null && grep -v TargetFrameworkProfile Asn1f2.csproj | awk 'BEGIN{i=0} /<PreBuildEvent/{i=1;}  {if (i== 0) { print $0; }}  /<\/PreBuildEvent?/{i=0;}' > a && mv a Asn1f2.csproj
cd ../Antlr
xbuild
cd -
echo ====================================================
echo ====================================================
echo 1. Spawn Monodevelop, and open 'Asn1.sln'.
echo "   (Ignore the warning about .vcxproj)"
echo 2. Then change 'Debug' to 'Debug|Mixed Platforms'
echo 3. Right-click on Asn1f2, and click Set As Startup project
echo 4, Then right-click it again, and choose Build.
echo 5. It should work - the Asn1f2/bin/Debug must contain the .exe/.dlls
echo 6. It also needs the .stg - hit ENTER here and I will copy them there.
read ANS
cp ../*/*.stg bin/Debug/
echo .stg copied, your compiler is ready, inside 
echo $(pwd)/bin/Debug
