module c_header
open System
open System.Numerics
open Ast

let PrintHeaderFile (sFileNameWithNoExtUpperCase:string) (arrsIncludedModules:seq<string>) (arrsTypeAssignments:seq<string>) (arrsValueAssignments:seq<string>) (arrsPrototypes:seq<string>) (arrsUtilityDefines:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintHeaderFile" [("sFileNameWithNoExtUpperCase",(if sFileNameWithNoExtUpperCase = null then null else ST.StrHelper sFileNameWithNoExtUpperCase:>Object) );("arrsIncludedModules",(arrsIncludedModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsValueAssignments",(arrsValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsPrototypes",(arrsPrototypes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsUtilityDefines",(arrsUtilityDefines|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let EnumUtilDefine (sItemName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "EnumUtilDefine" [("sItemName",(if sItemName = null then null else ST.StrHelper sItemName:>Object) )]

let EnumInnerUtilDefine (sTasName:string) (sItemName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "EnumInnerUtilDefine" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sItemName",(if sItemName = null then null else ST.StrHelper sItemName:>Object) )]

let ChoiceUtilDefine (sTasName:string) (sChildNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "ChoiceUtilDefine" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sChildNamePresent",(if sChildNamePresent = null then null else ST.StrHelper sChildNamePresent:>Object) )]

let PrintValueAssignment (sTypeDecl:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintValueAssignment" [("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let PrintTypeAssignment (sTypeDecl:string) (sArrayPostfix:string) (sName:string) (nMaxBitsInPER:BigInteger) (nMaxBytesInPER:BigInteger) (nMaxBitsInACN:BigInteger) (nMaxBytesInACN:BigInteger) (nMaxBytesInXER:BigInteger) (sStar:string) (bGenEqual:bool) (arrsErrorCodes:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintTypeAssignment" [("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sArrayPostfix",(if sArrayPostfix = null then null else ST.StrHelper sArrayPostfix:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nMaxBitsInPER",nMaxBitsInPER :>Object);("nMaxBytesInPER",nMaxBytesInPER :>Object);("nMaxBitsInACN",nMaxBitsInACN :>Object);("nMaxBytesInACN",nMaxBytesInACN :>Object);("nMaxBytesInXER",nMaxBytesInXER :>Object);("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("bGenEqual",bGenEqual :>Object);("arrsErrorCodes",(arrsErrorCodes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintPrototypes (arrsEncPrototypes:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintPrototypes" [("arrsEncPrototypes",(arrsEncPrototypes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintErrorCode (sErrorName:string) (nErrCode:BigInteger) (sComment:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintErrorCode" [("sErrorName",(if sErrorName = null then null else ST.StrHelper sErrorName:>Object) );("nErrCode",nErrCode :>Object);("sComment",(if sComment = null then null else ST.StrHelper sComment:>Object) )]

let UPER_encPrototypes (sName:string) (sStar:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "UPER_encPrototypes" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) )]

let XER_encPrototypes (sName:string) (sStar:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "XER_encPrototypes" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) )]

let BER_encPrototypes (sName:string) (sStar:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "BER_encPrototypes" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) )]

let PrintAcnParameter (sTypeDecl:string) (bEncOut:bool) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintAcnParameter" [("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("bEncOut",bEncOut :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let ACN_encPrototypes (sName:string) (sStar:string) (arrsEncodingParams:seq<string>) (arrsDecodingParams:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "ACN_encPrototypes" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsEncodingParams",(arrsEncodingParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsDecodingParams",(arrsDecodingParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Declare_Integer () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Integer" []

let Declare_Integer_min_max (nMin:BigInteger) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Integer_min_max" [("nMin",nMin :>Object);("nMax",nMax :>Object)]

let Declare_PosInteger_min_max (nMin:BigInteger) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_PosInteger_min_max" [("nMin",nMin :>Object);("nMax",nMax :>Object)]

let Declare_Integer_posInf (nMin:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Integer_posInf" [("nMin",nMin :>Object)]

let Declare_PosInteger_posInf (nMin:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_PosInteger_posInf" [("nMin",nMin :>Object)]

let Declare_Integer_negInf (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Integer_negInf" [("nMax",nMax :>Object)]

let Declare_Boolean () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Boolean" []

let Declare_Real () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Real" []

let Declare_IA5String () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_IA5String" []

let Declare_NumericString () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_NumericString" []

let Declare_NullType () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_NullType" []

let Declare_BitString (bIsFixeSize:bool) (nMaxOctets:BigInteger) (nMaxBits:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_BitString" [("bIsFixeSize",bIsFixeSize :>Object);("nMaxOctets",nMaxOctets :>Object);("nMaxBits",nMaxBits :>Object)]

let Declare_OctetString (bIsFixeSize:bool) (nMaxOctets:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_OctetString" [("bIsFixeSize",bIsFixeSize :>Object);("nMaxOctets",nMaxOctets :>Object)]

let PrintNamedItem (sName:string) (nValue:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintNamedItem" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nValue",nValue :>Object)]

let Declare_Enumerated (arrsItems:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Enumerated" [("arrsItems",(arrsItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintSeq_ChoiceChild (sTypeDecl:string) (sName:string) (sArrayPostfix:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintSeq_ChoiceChild" [("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sArrayPostfix",(if sArrayPostfix = null then null else ST.StrHelper sArrayPostfix:>Object) )]

let Declare_Choice (sChoiceIDForNone:string) (arrsEnmItems:seq<string>) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Choice" [("sChoiceIDForNone",(if sChoiceIDForNone = null then null else ST.StrHelper sChoiceIDForNone:>Object) );("arrsEnmItems",(arrsEnmItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Declare_Sequence (arrsChildren:seq<string>) (arrsOptionalChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Sequence" [("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsOptionalChildren",(arrsOptionalChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Declare_SequenceOf (bIsFixedSize:bool) (sTypeDecl:string) (nLength:BigInteger) (sArrayPostfix:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_SequenceOf" [("bIsFixedSize",bIsFixedSize :>Object);("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("nLength",nLength :>Object);("sArrayPostfix",(if sArrayPostfix = null then null else ST.StrHelper sArrayPostfix:>Object) )]

