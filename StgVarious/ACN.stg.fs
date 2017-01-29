module stg_acn
open System
open System.Numerics
open Ast

let PrintAsn1File (arrsModules:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintAsn1File" [("arrsModules",(arrsModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintModule (sName:string) (arrsTas:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintModule" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsTas",(arrsTas|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintParam (sName:string) (sType:string) (sMode:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintParam" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) );("sMode",(if sMode = null then null else ST.StrHelper sMode:>Object) )]

let PrintTemp (sName:string) (sType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintTemp" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) )]

let PrintTypeAssigment (sName:string) (arrsParasm:seq<string>) (arrsTempTypes:seq<string>) (sType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintTypeAssigment" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsParasm",(arrsParasm|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTempTypes",(arrsTempTypes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sType",(if sType = null then null else ST.StrHelper sType:>Object) )]

let PrintTypeChild (sName:string) (arrsArgs:seq<string>) (sImplMode:string) (sType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintTypeChild" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sImplMode",(if sImplMode = null then null else ST.StrHelper sImplMode:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) )]

let PrintType (arrsProps:seq<string>) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PrintType" [("arrsProps",(arrsProps|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PP_Encoding_PosInt () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Encoding_PosInt" []

let PP_Encoding_TwosComplement () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Encoding_TwosComplement" []

let PP_Encoding_Ascii () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Encoding_Ascii" []

let PP_Encoding_BCD () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Encoding_BCD" []

let PP_Encoding_IEEE754_32 () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Encoding_IEEE754_32" []

let PP_Encoding_IEEE754_64 () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Encoding_IEEE754_64" []

let PP_Size_Auto () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Size_Auto" []

let PP_Size_NullTerminated () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Size_NullTerminated" []

let PP_Size_Fixed (nFixedValue:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Size_Fixed" [("nFixedValue",nFixedValue :>Object)]

let PP_Sixe_Fld (sLongFld:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Sixe_Fld" [("sLongFld",(if sLongFld = null then null else ST.StrHelper sLongFld:>Object) )]

let PP_Adjust (nValue:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Adjust" [("nValue",nValue :>Object)]

let PP_Aligment_byte () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Aligment_byte" []

let PP_Aligment_word () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Aligment_word" []

let PP_Aligment_dword () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Aligment_dword" []

let PP_EncodeValues () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_EncodeValues" []

let PP_TrueValue (sVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_TrueValue" [("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let PP_FalseValue (sVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_FalseValue" [("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let PP_NullValue (sVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_NullValue" [("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let PP_Endianness_big () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Endianness_big" []

let PP_Endianness_little () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_Endianness_little" []

let PP_PresentWhenConditionBool (sLongField:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_PresentWhenConditionBool" [("sLongField",(if sLongField = null then null else ST.StrHelper sLongField:>Object) )]

let PP_PresentWhenConditionInt (sLongField:string) (nVal:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_PresentWhenConditionInt" [("sLongField",(if sLongField = null then null else ST.StrHelper sLongField:>Object) );("nVal",nVal :>Object)]

let PP_PresentWhenConditionStr (sLongField:string) (sVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_PresentWhenConditionStr" [("sLongField",(if sLongField = null then null else ST.StrHelper sLongField:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let PP_PresentWhen (arrsConditios:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_PresentWhen" [("arrsConditios",(arrsConditios|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PP_ChoiceDeterminant (sLongFdlToEnum:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_ChoiceDeterminant" [("sLongFdlToEnum",(if sLongFdlToEnum = null then null else ST.StrHelper sLongFdlToEnum:>Object) )]

let PP_MappingFunction (sFuncName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ACN" "PP_MappingFunction" [("sFuncName",(if sFuncName = null then null else ST.StrHelper sFuncName:>Object) )]

