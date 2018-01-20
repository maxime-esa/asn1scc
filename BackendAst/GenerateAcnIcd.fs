module GenerateAcnIcd
open System.Globalization
open System
open System.Numerics
open System.IO
open FsUtils
open CommonTypes
open DAst
open DastFold
open DAstUtilFunctions
open Antlr.Asn1
open Antlr.Runtime


let DoWork (r:AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (stgFileName:string)   outFileName =
    let content = """
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd"> 
<html xmlns="http://www.w3.org/1999/xhtml" >
<body>
<em>The following tables describe the binary encodings of the data model using the ACN Encoding Rules.
</em><br/><br/>
</body>
</html>
"""
    File.WriteAllText(outFileName, content.Replace("\r",""))

