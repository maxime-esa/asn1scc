#!/bin/bash

ASN1CRT_H="asn1crt_acn.h \
	asn1crt_ber.h \
	asn1crt_core.h \
	asn1crt_real.h \
	asn1crt_util.h \
	asn1crt_xer.h \
	asn1crt.h \
	BitStream.h \
	ByteStream.h"

ASN1CRT_C="Acn.c\
	ber.c\
	BitStream.c\
	ByteStream.c\
	real.c\
	util.c\
	xer.c"

#
# creates the output file at the specified relative path
init_output() {
	OUT="$1"
	mkdir -p `dirname "$OUT"`
	echo -n > $OUT
}

# - asn1scc/.gitignore
echo '*** asn1scc/.gitignore'
echo  '<TODO>'

# asn1scc/Asn1f2/Asn1f2.csproj
gen_csproj() {
	F=Asn1f2/Asn1f2.csproj
	OUT=out/$F.delta-crt
	echo "*** $F ***"
	init_output $OUT


	for SF in $ASN1CRT_H $ASN1CRT_C ; do
cat >>$OUT << END
  <ItemGroup>
    <None Include="Resources\\${SF}" />
  </ItemGroup>
END
	done


cat >>$OUT << END
<Target Name="BeforeBuild">
	<ItemGroup>
END
	for SF in $ASN1CRT_H $ASN1CRT_C ; do
	echo '      <ResourceFilesToCopy Include="$(SolutionDir)asn1crt/'${SF}'" />' >> $OUT
	done
cat >>$OUT << END
    </ItemGroup>
</Target>
END

}

# asn1scc/Asn1f2/Resource1.resx
gen_resx_entry() {
FILE_NAME=$1
RES_NAME=$( echo $FILE_NAME | tr . _ )
cat <<END
  <data name="$RES_NAME" type="System.Resources.ResXFileRef, System.Windows.Forms">
    <value>Resources/$FILE_NAME;System.String, mscorlib, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089;windows-1253</value>
  </data>
END
}

gen_resx() {
	F="Asn1f2/Resource1.resx"
	OUT=out/$F.delta-crt
	echo "*** $F ***"
	init_output $OUT
	for F in $ASN1CRT_H $ASN1CRT_C ; do
		gen_resx_entry $F >> $OUT
	done
}

# - asn1scc/Asn1f2/Program.cs
gen_program_cs() {
	BF="Asn1f2/Program.cs";
	OUT=out/$BF.delta-crt
	echo "*** $BF ***"
	init_output $OUT
	
	for SF in $ASN1CRT_H $ASN1CRT_C ; do
		RES_NAME=$( echo $SF | tr . _ )
		cat >> $OUT <<END
WriteTextFile(Path.Combine(outDir, "$SF"), Resource1.$RES_NAME);
END
	done
}

# - asn1scc/asn1crt/asn1crt.vcproj

gen_vcproj_entry_c() { 
cat <<END
			<File
				RelativePath=".\\$1"
				>
				<FileConfiguration
					Name="Debug|Win32"
					>
					<Tool
						Name="VCCLCompilerTool"
						Detect64BitPortabilityProblems="false"
					/>
				</FileConfiguration>
			</File>
END
}

gen_vcproj_entry_h() {
cat<<END
			<File
				RelativePath=".\\$1"
				>
			</File>
END
}

gen_vcproj() {
	F=asn1crt/asn1crt.vcproj
	OUT=out/$F.delta-crt
	echo "*** $F ***"
	init_output $OUT
	
	for F in $ASN1CRT_H ; do
		gen_vcproj_entry_h $F >> $OUT
	done
	for F in $ASN1CRT_C ; do
		gen_vcproj_entry_c $F >> $OUT
	done
}

# asn1crt/asn1crt.vcxproj
gen_vcxproj() {
	F=asn1crt/asn1crt.vcxproj
	OUT=out/$F.delta-crt
	echo "*** $F ***"
	init_output $OUT
	
	for F in $ASN1CRT_H ; do
		echo "    <ClInclude Include=\"${F}\" />" >> $OUT
	done
	for F in $ASN1CRT_C ; do
		echo "    <ClCompile Include=\"${F}\" />" >> $OUT
	done
}


###### Main program ######
gen_csproj
gen_resx
gen_program_cs
gen_vcproj
gen_vcxproj



