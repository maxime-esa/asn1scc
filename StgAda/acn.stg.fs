module acn_a
open System
open System.Numerics
open Ast

let PrintParam (sName:string) (sDirection:string) (sType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PrintParam" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sDirection",(if sDirection = null then null else ST.StrHelper sDirection:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) )]

let Tas (sName:string) (bAcnEncodeFuncRequiresResult:bool) (arrsLocalVariables:seq<string>) (sContent:string) (arrsAnnotations:seq<string>) (arrsExtraParams:seq<string>) (arrsExtraParamNames:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Tas_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("arrsAnnotations",(arrsAnnotations|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsExtraParams",(arrsExtraParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsExtraParamNames",(arrsExtraParamNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "acn" "Tas_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("arrsAnnotations",(arrsAnnotations|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsExtraParams",(arrsExtraParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsExtraParamNames",(arrsExtraParamNames|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintType (sMainBody:string) (bAligmentApplied:bool) (nAligmentValue:BigInteger) (bHasDependencies:bool) (sDependencyUpdates:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "PrintType_encode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("nAligmentValue",nAligmentValue :>Object);("bHasDependencies",bHasDependencies :>Object);("sDependencyUpdates",(if sDependencyUpdates = null then null else ST.StrHelper sDependencyUpdates:>Object) )]
    | Decode    ->
        ST.call "acn" "PrintType_decode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("nAligmentValue",nAligmentValue :>Object);("bHasDependencies",bHasDependencies :>Object);("sDependencyUpdates",(if sDependencyUpdates = null then null else ST.StrHelper sDependencyUpdates:>Object) )]

let PrintTypeNoUpdate (sMainBody:string) (bAligmentApplied:bool) (nAligmentValue:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "PrintTypeNoUpdate_encode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("nAligmentValue",nAligmentValue :>Object)]
    | Decode    ->
        ST.call "acn" "PrintTypeNoUpdate_decode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("nAligmentValue",nAligmentValue :>Object)]

let string_InternalItem (p:string) (i:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "string_InternalItem_encode" [("p",p :>Object);("i",i :>Object)]
    | Decode    ->
        ST.call "acn" "string_InternalItem_decode" [("p",p :>Object);("i",i :>Object)]

let str_FixedSize (p:string) (sTasName:string) (i:string) (sInternalItem:string) (nFixedSize:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "str_FixedSize_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "acn" "str_FixedSize_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]

let str_VarSize (p:string) (sTasName:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (nSizeInBits:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "str_VarSize_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nSizeInBits",nSizeInBits :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "acn" "str_VarSize_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nSizeInBits",nSizeInBits :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]

let str_external_field (p:string) (sTasName:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (sExtFld:string) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "str_external_field_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "acn" "str_external_field_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("nAlignSize",nAlignSize :>Object)]

let bit_oct_sqf_external_field (sTasName:string) (p:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (sExtFld:string) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "bit_oct_sqf_external_field_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "acn" "bit_oct_sqf_external_field_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("nAlignSize",nAlignSize :>Object)]

let RefTypeParam_tmpVar (sName:string) (sTypeDecl:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "RefTypeParam_tmpVar" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) )]

let ReferenceType1 (p:string) (sName:string) (bAcnEncodeFuncRequiresResult:bool) (arrsArgs:seq<string>) (arrsLocalPrms:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "ReferenceType1_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalPrms",(arrsLocalPrms|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "acn" "ReferenceType1_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalPrms",(arrsLocalPrms|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let ReferenceType2 (p:string) (sTasName:string) (sName:string) (bAcnEncodeFuncRequiresResult:bool) (arrsArgs:seq<string>) (arrsLocalPrms:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "ReferenceType2_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalPrms",(arrsLocalPrms|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "acn" "ReferenceType2_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalPrms",(arrsLocalPrms|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Sequence_optChild (p:string) (sChName:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_optChild_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_optChild_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Sequence_optChild_pres_bool (p:string) (sChName:string) (sExtFldName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_optChild_pres_bool_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_optChild_pres_bool_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) )]

let Sequence_optChild_pres_int (p:string) (sChName:string) (sExtFldName:string) (nIntVal:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_optChild_pres_int_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("nIntVal",nIntVal :>Object)]
    | Decode    ->
        ST.call "acn" "Sequence_optChild_pres_int_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("nIntVal",nIntVal :>Object)]

let Sequence_optChild_pres_str (p:string) (sChName:string) (sExtFldName:string) (sVal:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_optChild_pres_str_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_optChild_pres_str_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let Sequence_Child (p:string) (sChName:string) (bIsUperOptional:bool) (sChildContent:string) (bHasDefaultValue:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_Child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("bIsUperOptional",bIsUperOptional :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("bHasDefaultValue",bHasDefaultValue :>Object)]
    | Decode    ->
        ST.call "acn" "Sequence_Child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("bIsUperOptional",bIsUperOptional :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("bHasDefaultValue",bHasDefaultValue :>Object)]

let Sequence_always_present_Child (p:string) (sChName:string) (bIsUperOptional:bool) (sChildContent:string) (bHasDefaultValue:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_always_present_Child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("bIsUperOptional",bIsUperOptional :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("bHasDefaultValue",bHasDefaultValue :>Object)]
    | Decode    ->
        ST.call "acn" "Sequence_always_present_Child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("bIsUperOptional",bIsUperOptional :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("bHasDefaultValue",bHasDefaultValue :>Object)]

let Sequence (p:string) (arrsChildren:seq<string>) (sTasName:string) (bRequiresInit:bool) (arrsDecOutParamsInit:seq<string>) (bResultRequiresInit:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bRequiresInit",bRequiresInit :>Object);("arrsDecOutParamsInit",(arrsDecOutParamsInit|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bResultRequiresInit",bResultRequiresInit :>Object)]
    | Decode    ->
        ST.call "acn" "Sequence_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bRequiresInit",bRequiresInit :>Object);("arrsDecOutParamsInit",(arrsDecOutParamsInit|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bResultRequiresInit",bResultRequiresInit :>Object)]

let PrmUpdate (sPrmName:string) (sPrmInitValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PrmUpdate" [("sPrmName",(if sPrmName = null then null else ST.StrHelper sPrmName:>Object) );("sPrmInitValue",(if sPrmInitValue = null then null else ST.StrHelper sPrmInitValue:>Object) )]

let JoinItems (sTasName:string) (sPart:string) (sNestedPart:string) (nRequiredBitsSoFar:BigInteger) (bRequiresAssert:bool) (bReqResultCheck:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "JoinItems_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) );("nRequiredBitsSoFar",nRequiredBitsSoFar :>Object);("bRequiresAssert",bRequiresAssert :>Object);("bReqResultCheck",bReqResultCheck :>Object)]
    | Decode    ->
        ST.call "acn" "JoinItems_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) );("nRequiredBitsSoFar",nRequiredBitsSoFar :>Object);("bRequiresAssert",bRequiresAssert :>Object);("bReqResultCheck",bReqResultCheck :>Object)]

let UpdateFailedPart () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "UpdateFailedPart" []

let ChoiceChild (sTasName:string) (sName:string) (sChildBody:string) (nIndex:BigInteger) (nIndexSizeInBits:BigInteger) (sNamePresent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "ChoiceChild_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("nIndex",nIndex :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object);("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]
    | Decode    ->
        ST.call "acn" "ChoiceChild_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("nIndex",nIndex :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object);("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let ChoiceChild_tmpVar (sName:string) (sTypeDecl:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceChild_tmpVar" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) )]

let Choice (sTasName:string) (arrsChildren:seq<string>) (nIndexMax:BigInteger) (nIndexSizeInBits:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Choice_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nIndexMax",nIndexMax :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object)]
    | Decode    ->
        ST.call "acn" "Choice_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nIndexMax",nIndexMax :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object)]

let Declare_ChoiceIndex () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "Declare_ChoiceIndex" []

let ChoiceChild_preWhen (sTasName:string) (sName:string) (sChildBody:string) (arrsConditions:seq<string>) (bFirst:bool) (sNamePresent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "ChoiceChild_preWhen_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("arrsConditions",(arrsConditions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bFirst",bFirst :>Object);("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]
    | Decode    ->
        ST.call "acn" "ChoiceChild_preWhen_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("arrsConditions",(arrsConditions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bFirst",bFirst :>Object);("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let ChoiceChild_preWhen_bool_condition (sExtFld:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceChild_preWhen_bool_condition" [("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let ChoiceChild_preWhen_int_condition (sExtFld:string) (nVal:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceChild_preWhen_int_condition" [("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("nVal",nVal :>Object)]

let ChoiceChild_preWhen_str_condition (sExtFld:string) (sVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceChild_preWhen_str_condition" [("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let Choice_preWhen (sTasName:string) (arrsChildren:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Choice_preWhen_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "acn" "Choice_preWhen_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let ChoiceChild_Enum (sTasName:string) (sName:string) (sEnumItem:string) (sChildBody:string) (sNamePresent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "ChoiceChild_Enum_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sEnumItem",(if sEnumItem = null then null else ST.StrHelper sEnumItem:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]
    | Decode    ->
        ST.call "acn" "ChoiceChild_Enum_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sEnumItem",(if sEnumItem = null then null else ST.StrHelper sEnumItem:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let Choice_Enum (sTasName:string) (arrsChildren:seq<string>) (sEnmExtFld:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "acn" "Choice_Enum_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sEnmExtFld",(if sEnmExtFld = null then null else ST.StrHelper sEnmExtFld:>Object) )]
    | Decode    ->
        ST.call "acn" "Choice_Enum_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sEnmExtFld",(if sEnmExtFld = null then null else ST.StrHelper sEnmExtFld:>Object) )]

let PrintAcn_update_param (sTasName:string) (bHasSuccess:bool) (sParamName:string) (sContent:string) (sParamType:string) (arrsTmpVars:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PrintAcn_update_param" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bHasSuccess",bHasSuccess :>Object);("sParamName",(if sParamName = null then null else ST.StrHelper sParamName:>Object) );("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("sParamType",(if sParamType = null then null else ST.StrHelper sParamType:>Object) );("arrsTmpVars",(arrsTmpVars|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintAcn_update_param_body_choice_child (sChildName:string) (sChildUpdateStatement:string) (bCheckSuccess:bool) (sChildNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PrintAcn_update_param_body_choice_child" [("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("sChildUpdateStatement",(if sChildUpdateStatement = null then null else ST.StrHelper sChildUpdateStatement:>Object) );("bCheckSuccess",bCheckSuccess :>Object);("sChildNamePresent",(if sChildNamePresent = null then null else ST.StrHelper sChildNamePresent:>Object) )]

let PrintAcn_update_param_body_choice (sTasName:string) (arrsChildUpdateStatements:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PrintAcn_update_param_body_choice" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildUpdateStatements",(arrsChildUpdateStatements|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintAcn_update_param_body (sPart:string) (sNestedPart:string) (bCheckSuccess:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PrintAcn_update_param_body" [("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) );("bCheckSuccess",bCheckSuccess :>Object)]

let RefTypeArgument1 (v:string) (sTasName:string) (sParamName:string) (sRefTypePath:string) (bHasSuccess:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "RefTypeArgument1" [("v",v :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sParamName",(if sParamName = null then null else ST.StrHelper sParamName:>Object) );("sRefTypePath",(if sRefTypePath = null then null else ST.StrHelper sRefTypePath:>Object) );("bHasSuccess",bHasSuccess :>Object)]

let RefTypeArgument2 (v:string) (sModName:string) (sTasName:string) (sParamName:string) (sRefTypePath:string) (bHasSuccess:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "RefTypeArgument2" [("v",v :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sParamName",(if sParamName = null then null else ST.StrHelper sParamName:>Object) );("sRefTypePath",(if sRefTypePath = null then null else ST.StrHelper sRefTypePath:>Object) );("bHasSuccess",bHasSuccess :>Object)]

let SizeDependency (v:string) (sCount:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "SizeDependency" [("v",v :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) )]

let ChoiceDependencyEnum_Item (v:string) (sChildCID:string) (sEnumCName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceDependencyEnum_Item" [("v",v :>Object);("sChildCID",(if sChildCID = null then null else ST.StrHelper sChildCID:>Object) );("sEnumCName",(if sEnumCName = null then null else ST.StrHelper sEnumCName:>Object) )]

let ChoiceDependencyEnum (sTasName:string) (arrsChoiceEnumItems:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceDependencyEnum" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChoiceEnumItems",(arrsChoiceEnumItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PresenceDependency (v:string) (sSeqPath:string) (sChildName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "PresenceDependency" [("v",v :>Object);("sSeqPath",(if sSeqPath = null then null else ST.StrHelper sSeqPath:>Object) );("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) )]

let ChoiceDependencyIntPres_child (v:string) (sChildName:string) (nChildRetVal:BigInteger) (sChildNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceDependencyIntPres_child" [("v",v :>Object);("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("nChildRetVal",nChildRetVal :>Object);("sChildNamePresent",(if sChildNamePresent = null then null else ST.StrHelper sChildNamePresent:>Object) )]

let ChoiceDependencyStrPres_child (v:string) (sChildName:string) (sChildRetVal:string) (sChildNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceDependencyStrPres_child" [("v",v :>Object);("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("sChildRetVal",(if sChildRetVal = null then null else ST.StrHelper sChildRetVal:>Object) );("sChildNamePresent",(if sChildNamePresent = null then null else ST.StrHelper sChildNamePresent:>Object) )]

let ChoiceDependencyPres (sTasName:string) (arrsChoiceItems:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "ChoiceDependencyPres" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChoiceItems",(arrsChoiceItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let MultiUpdateCheckWithFirstValue (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "MultiUpdateCheckWithFirstValue" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let MultiUpdateCheckWithFirstValueInteger (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "MultiUpdateCheckWithFirstValueInteger" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let MultiParamUpdateCheckWithFirstValue (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "MultiParamUpdateCheckWithFirstValue" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let CheckBeforeAssignToIntField_min_max (sTmpVar0:string) (nMin:BigInteger) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "CheckBeforeAssignToIntField_min_max" [("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("nMin",nMin :>Object);("nMax",nMax :>Object)]

let CheckBeforeAssignToIntField_max (sTmpVar0:string) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "CheckBeforeAssignToIntField_max" [("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("nMax",nMax :>Object)]

let CheckBeforeAssignToIntField_min (sTmpVar0:string) (nMin:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "CheckBeforeAssignToIntField_min" [("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("nMin",nMin :>Object)]

let UpdateAsn1Field (sAcnField:string) (sTmpVar:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "UpdateAsn1Field" [("sAcnField",(if sAcnField = null then null else ST.StrHelper sAcnField:>Object) );("sTmpVar",(if sTmpVar = null then null else ST.StrHelper sTmpVar:>Object) )]

let UpdateAsn1IntegerField (sAcnField:string) (sTmpVar0:string) (sAsn1FieldType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "UpdateAsn1IntegerField" [("sAcnField",(if sAcnField = null then null else ST.StrHelper sAcnField:>Object) );("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("sAsn1FieldType",(if sAsn1FieldType = null then null else ST.StrHelper sAsn1FieldType:>Object) )]

let MultiUpdateCheckWithFirstValue2 (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "MultiUpdateCheckWithFirstValue2" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let MultiParamUpdateCheckWithFirstValue2 (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "acn" "MultiParamUpdateCheckWithFirstValue2" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

