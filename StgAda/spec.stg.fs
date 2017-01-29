module a_header
open System
open System.Numerics
open Ast

let PrintFile (arrsPackages:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintFile" [("arrsPackages",(arrsPackages|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let rtlModuleName () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "rtlModuleName" []

let PrintPackageSpec (sPackageName:string) (arrsIncludedModules:seq<string>) (arrsTypeAssignments:seq<string>) (arrsValueAssignments:seq<string>) (arrsPrivateChoices:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintPackageSpec" [("sPackageName",(if sPackageName = null then null else ST.StrHelper sPackageName:>Object) );("arrsIncludedModules",(arrsIncludedModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsValueAssignments",(arrsValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsPrivateChoices",(arrsPrivateChoices|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintNegativeRealConstant (sName:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintNegativeRealConstant" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintPackageBody (sPackageName:string) (arrsIncludedModules:seq<string>) (arrsNegativeReals:seq<string>) (arrsBoolPatterns:seq<string>) (arrsTypeAssignments:seq<string>) (arrsChoiceValueAssignments:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintPackageBody" [("sPackageName",(if sPackageName = null then null else ST.StrHelper sPackageName:>Object) );("arrsIncludedModules",(arrsIncludedModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsNegativeReals",(arrsNegativeReals|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsBoolPatterns",(arrsBoolPatterns|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsChoiceValueAssignments",(arrsChoiceValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintValueAssignment (sVasName:string) (sTypeDecl:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintValueAssignment" [("sVasName",(if sVasName = null then null else ST.StrHelper sVasName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintValueAssignment_Choice (sVasName:string) (sTypeDecl:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintValueAssignment_Choice" [("sVasName",(if sVasName = null then null else ST.StrHelper sVasName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintValueAssignment_Choice_body (sVasName:string) (sTypeDecl:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintValueAssignment_Choice_body" [("sVasName",(if sVasName = null then null else ST.StrHelper sVasName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintTypeAssignment (sName:string) (sTasDecl:string) (nMaxBitsInPER:BigInteger) (nMaxBytesInPER:BigInteger) (nMaxBitsInACN:BigInteger) (nMaxBytesInACN:BigInteger) (arrsErrorCodes:seq<string>) (bGenIsValid:bool) (bGenEqual:bool) (arrsEncPrototypes:seq<string>) (bIsComplex:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintTypeAssignment" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTasDecl",(if sTasDecl = null then null else ST.StrHelper sTasDecl:>Object) );("nMaxBitsInPER",nMaxBitsInPER :>Object);("nMaxBytesInPER",nMaxBytesInPER :>Object);("nMaxBitsInACN",nMaxBitsInACN :>Object);("nMaxBytesInACN",nMaxBytesInACN :>Object);("arrsErrorCodes",(arrsErrorCodes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bGenIsValid",bGenIsValid :>Object);("bGenEqual",bGenEqual :>Object);("arrsEncPrototypes",(arrsEncPrototypes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bIsComplex",bIsComplex :>Object)]

let PRIMITIVE_tas_decl (sName:string) (sTypeDecl:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PRIMITIVE_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) )]

let SEQUENCE_tas_decl_child_bit (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "SEQUENCE_tas_decl_child_bit" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let SEQUENCE_tas_decl_child (sName:string) (sType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "SEQUENCE_tas_decl_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) )]

let SEQUENCE_tas_decl (sName:string) (arrsChildren:seq<string>) (arrsOptionalChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "SEQUENCE_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsOptionalChildren",(arrsOptionalChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let CHOICE_tas_decl_child (sTasName:string) (sName:string) (sType:string) (sNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "CHOICE_tas_decl_child" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) );("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let CHOICE_tas_decl (sName:string) (arrsChildren:seq<string>) (arrsPresent:seq<string>) (nIndexMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "CHOICE_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsPresent",(arrsPresent|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nIndexMax",nIndexMax :>Object)]

let CHOICE_tas_decl_priv_child (sName:string) (sType:string) (sPresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "CHOICE_tas_decl_priv_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) );("sPresent",(if sPresent = null then null else ST.StrHelper sPresent:>Object) )]

let CHOICE_tas_decl_priv (sName:string) (sFirstChildNamePresent:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "CHOICE_tas_decl_priv" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sFirstChildNamePresent",(if sFirstChildNamePresent = null then null else ST.StrHelper sFirstChildNamePresent:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let SEQUENCE_OF_tas_decl (sName:string) (nMin:BigInteger) (nMax:BigInteger) (bFixedSize:bool) (sChildType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "SEQUENCE_OF_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nMin",nMin :>Object);("nMax",nMax :>Object);("bFixedSize",bFixedSize :>Object);("sChildType",(if sChildType = null then null else ST.StrHelper sChildType:>Object) )]

let BIT_STRING_tas_decl (sName:string) (nMin:BigInteger) (nMax:BigInteger) (bFixedSize:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "BIT_STRING_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nMin",nMin :>Object);("nMax",nMax :>Object);("bFixedSize",bFixedSize :>Object)]

let OCTET_STRING_tas_decl (sName:string) (nMin:BigInteger) (nMax:BigInteger) (bFixedSize:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "OCTET_STRING_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nMin",nMin :>Object);("nMax",nMax :>Object);("bFixedSize",bFixedSize :>Object)]

let IA5STRING_OF_tas_decl (sName:string) (nMin:BigInteger) (nMax:BigInteger) (nCMax:BigInteger) (arrnAlphaChars:seq<BigInteger>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "IA5STRING_OF_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nMin",nMin :>Object);("nMax",nMax :>Object);("nCMax",nCMax :>Object);("arrnAlphaChars",arrnAlphaChars|>Seq.toArray :>Object)]

let ENUMERATED_tas_decl_item (sName:string) (nValue:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "ENUMERATED_tas_decl_item" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nValue",nValue :>Object)]

let ENUMERATED_tas_decl (sName:string) (arrsEnumNames:seq<string>) (arrsEnumNamesAndValues:seq<string>) (nIndexMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "ENUMERATED_tas_decl" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsEnumNames",(arrsEnumNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEnumNamesAndValues",(arrsEnumNamesAndValues|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nIndexMax",nIndexMax :>Object)]

let UPER_annotations (sName:string) (bKDependsOnValue:bool) (bAcnEncodeFuncRequiresResult:bool) (bResDependsOnData:bool) (bKDependsOnData:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "spec" "UPER_annotations_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bKDependsOnValue",bKDependsOnValue :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object)]
    | Decode    ->
        ST.call "spec" "UPER_annotations_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bKDependsOnValue",bKDependsOnValue :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object)]

let UPER_encPrototypes (sName:string) (bEmptyEncodingSpace:bool) (bKDependsOnValue:bool) (bAcnEncodeFuncRequiresResult:bool) (bResDependsOnData:bool) (bKDependsOnData:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "UPER_encPrototypes" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bEmptyEncodingSpace",bEmptyEncodingSpace :>Object);("bKDependsOnValue",bKDependsOnValue :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object)]

let ACN_encPrototypes (sName:string) (bEmptyEncodingSpace:bool) (bKDependsOnValue:bool) (bAcnEncodeFuncRequiresResult:bool) (bResDependsOnData:bool) (bKDependsOnData:bool) (arrsExtraEncParams:seq<string>) (arrsExtraDecParams:seq<string>) (arrsDecInParamNames:seq<string>) (arrsEncDecInOutPrmsNames:seq<string>) (arrsEncDecInOutPrmsNames_noBools:seq<string>) (arrsUpdatePrototypes:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "ACN_encPrototypes" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bEmptyEncodingSpace",bEmptyEncodingSpace :>Object);("bKDependsOnValue",bKDependsOnValue :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("arrsExtraEncParams",(arrsExtraEncParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsExtraDecParams",(arrsExtraDecParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsDecInParamNames",(arrsDecInParamNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEncDecInOutPrmsNames",(arrsEncDecInOutPrmsNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEncDecInOutPrmsNames_noBools",(arrsEncDecInOutPrmsNames_noBools|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsUpdatePrototypes",(arrsUpdatePrototypes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let ACN_annotations (sName:string) (bKDependsOnValue:bool) (bAcnEncodeFuncRequiresResult:bool) (bResDependsOnData:bool) (bKDependsOnData:bool) (arrsDecInParamNames:seq<string>) (arrsEncDecInOutPrmsNames:seq<string>) (arrsEncDecInOutPrmsNames_noBools:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "spec" "ACN_annotations_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bKDependsOnValue",bKDependsOnValue :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("arrsDecInParamNames",(arrsDecInParamNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEncDecInOutPrmsNames",(arrsEncDecInOutPrmsNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEncDecInOutPrmsNames_noBools",(arrsEncDecInOutPrmsNames_noBools|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "spec" "ACN_annotations_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bKDependsOnValue",bKDependsOnValue :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("arrsDecInParamNames",(arrsDecInParamNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEncDecInOutPrmsNames",(arrsEncDecInOutPrmsNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsEncDecInOutPrmsNames_noBools",(arrsEncDecInOutPrmsNames_noBools|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Acn_update_param_protorype (sTasName:string) (bHasSuccess:bool) (sParamName:string) (sParamType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Acn_update_param_protorype" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bHasSuccess",bHasSuccess :>Object);("sParamName",(if sParamName = null then null else ST.StrHelper sParamName:>Object) );("sParamType",(if sParamType = null then null else ST.StrHelper sParamType:>Object) )]

let PrintErrorCode (sErrorName:string) (nErrCode:BigInteger) (sComment:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "PrintErrorCode" [("sErrorName",(if sErrorName = null then null else ST.StrHelper sErrorName:>Object) );("nErrCode",nErrCode :>Object);("sComment",(if sComment = null then null else ST.StrHelper sComment:>Object) )]

let Declare_spark_Integer () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_spark_Integer" []

let Declare_Integer () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Integer" []

let Declare_Integer_min_max (nMin:BigInteger) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Integer_min_max" [("nMin",nMin :>Object);("nMax",nMax :>Object)]

let Declare_Integer_posInf (nMin:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Integer_posInf" [("nMin",nMin :>Object)]

let Declare_Integer_negInf (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Integer_negInf" [("nMax",nMax :>Object)]

let Declare_Integer_Empty () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Integer_Empty" []

let Declare_BOOLEAN () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_BOOLEAN" []

let Declare_REAL () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_REAL" []

let Declare_NULL () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_NULL" []

let Declare_Reference1 (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Reference1" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let Declare_Reference2 (sModName:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "spec" "Declare_Reference2" [("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

