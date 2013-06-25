@ECHO on
SET LANG=C

FOR /F "usebackq" %%s IN (`c:\cygwin\bin\svnversion.exe .`) DO @SET REV=%%s

echo namespace Asn1f2 { public class Svn    { public const string Version = "%REV%";    }} > SvnVersion.cs.tmp

fc SvnVersion.cs.tmp SvnVersion.cs

IF ERRORLEVEL 1 copy /Y SvnVersion.cs.tmp SvnVersion.cs
