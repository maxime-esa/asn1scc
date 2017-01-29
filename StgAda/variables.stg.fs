module a_variables
open System
open System.Numerics
open Ast

let PrintIntValue (nValue:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintIntValue" [("nValue",nValue :>Object)]

let PrintRealValue (dValue:double) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintRealValue" [("dValue",dValue :>Object)]

let PrintStringValue (sValue:string) (arrsNullChars:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintStringValue" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) );("arrsNullChars",(arrsNullChars|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintStringValueNull () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintStringValueNull" []

let PrintStringValueChar (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintStringValueChar" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintRefValue1 (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintRefValue1" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintRefValue2 (sModName:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintRefValue2" [("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintEnumValue (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintEnumValue" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintRefValue_lengthOf (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintRefValue_lengthOf" [("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintCharValue (cValue:char) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintCharValue" [("cValue",cValue :>Object)]

let PrintBooleanValue (bValue:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintBooleanValue" [("bValue",bValue :>Object)]

let PrintNullValue () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintNullValue" []

let PrintOctetStringValue (sTasName:string) (bIsFixedSize:bool) (arruBytes:seq<byte>) (nCount:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintOctetStringValue" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("arruBytes",arruBytes|>Seq.toArray :>Object);("nCount",nCount :>Object)]

let PrintBitStringValue (sTasName:string) (bIsFixedSize:bool) (arrsBits:seq<string>) (nCount:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintBitStringValue" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("arrsBits",(arrsBits|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nCount",nCount :>Object)]

let PrintSequenceValueChild (sName:string) (sInnerValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintSequenceValueChild" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sInnerValue",(if sInnerValue = null then null else ST.StrHelper sInnerValue:>Object) )]

let PrintSequenceValue_child_exists (sName:string) (sExistsBit:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintSequenceValue_child_exists" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sExistsBit",(if sExistsBit = null then null else ST.StrHelper sExistsBit:>Object) )]

let PrintSequenceValue_Exists (sTasName:string) (arrsOptionalPresentFields:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintSequenceValue_Exists" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsOptionalPresentFields",(arrsOptionalPresentFields|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintSequenceValue (sTasName:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintSequenceValue" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintChoiceValue (sTasName:string) (sChildName:string) (sChildVal:string) (sChildNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintChoiceValue" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("sChildVal",(if sChildVal = null then null else ST.StrHelper sChildVal:>Object) );("sChildNamePresent",(if sChildNamePresent = null then null else ST.StrHelper sChildNamePresent:>Object) )]

let PrintChoiceValue_setters (sTasName:string) (sChildName:string) (sChildVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintChoiceValue_setters" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("sChildVal",(if sChildVal = null then null else ST.StrHelper sChildVal:>Object) )]

let PrintSequenceOfValue (sTasName:string) (bIsFixedSize:bool) (nLength:BigInteger) (arrsInnerValues:seq<string>) (sDefValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "variables" "PrintSequenceOfValue" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("nLength",nLength :>Object);("arrsInnerValues",(arrsInnerValues|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sDefValue",(if sDefValue = null then null else ST.StrHelper sDefValue:>Object) )]

