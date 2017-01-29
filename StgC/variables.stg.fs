module variables_c
open System
open System.Numerics
open Ast

let PrintIntValue (nValue:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintIntValue" [("nValue",nValue :>Object)]

let PrintRealValue (dValue:double) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintRealValue" [("dValue",dValue :>Object)]

let PrintEnumValue (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintEnumValue" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintRefValue1 (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintRefValue1" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintRefValue2 (sModName:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintRefValue2" [("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintStringValue (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintStringValue" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintCharValue (cValue:char) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintCharValue" [("cValue",cValue :>Object)]

let PrintBooleanValue (bValue:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintBooleanValue" [("bValue",bValue :>Object)]

let PrintNullValue () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintNullValue" []

let PrintBitOrOctetStringValue (bIsFixedSize:bool) (arruBytes:seq<byte>) (nCount:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintBitOrOctetStringValue" [("bIsFixedSize",bIsFixedSize :>Object);("arruBytes",arruBytes|>Seq.toArray :>Object);("nCount",nCount :>Object)]

let PrintSequenceValueChild (sName:string) (sInnerValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintSequenceValueChild" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sInnerValue",(if sInnerValue = null then null else ST.StrHelper sInnerValue:>Object) )]

let PrintSequenceValue_child_exists (sName:string) (sExistsBit:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintSequenceValue_child_exists" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sExistsBit",(if sExistsBit = null then null else ST.StrHelper sExistsBit:>Object) )]

let PrintSequenceValue (arrsChildren:seq<string>) (arrsOptionalPresentFields:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintSequenceValue" [("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsOptionalPresentFields",(arrsOptionalPresentFields|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintChoiceValue (sAltNamePresent:string) (sAltName:string) (sInnerValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintChoiceValue" [("sAltNamePresent",(if sAltNamePresent = null then null else ST.StrHelper sAltNamePresent:>Object) );("sAltName",(if sAltName = null then null else ST.StrHelper sAltName:>Object) );("sInnerValue",(if sInnerValue = null then null else ST.StrHelper sInnerValue:>Object) )]

let PrintSequenceOfValue (bIsFixedSize:bool) (arrsInnerValues:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "variables" "PrintSequenceOfValue" [("bIsFixedSize",bIsFixedSize :>Object);("arrsInnerValues",(arrsInnerValues|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

