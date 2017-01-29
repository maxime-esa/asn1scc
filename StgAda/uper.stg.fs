module uper_a
open System
open System.Numerics
open Ast

let Tas (sName:string) (bAcnEncodeFuncRequiresResult:bool) (arrsLocalVariables:seq<string>) (sContent:string) (bIsFixedSize:bool) (bResDependsOnData:bool) (bKDependsOnData:bool) (arrsAnnotations:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Tas_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("arrsAnnotations",(arrsAnnotations|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "uper" "Tas_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("arrsAnnotations",(arrsAnnotations|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let IntFullyConstraint (p:string) (nMin:BigInteger) (nMax:BigInteger) (nBits:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "IntFullyConstraint_encode" [("p",p :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntFullyConstraint_decode" [("p",p :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntUnconstraint (p:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "IntUnconstraint_encode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntUnconstraint_decode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntUnconstraintMax (p:string) (nMax:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "IntUnconstraintMax_encode" [("p",p :>Object);("nMax",nMax :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntUnconstraintMax_decode" [("p",p :>Object);("nMax",nMax :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntSemiConstraint (p:string) (nMin:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "IntSemiConstraint_encode" [("p",p :>Object);("nMin",nMin :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntSemiConstraint_decode" [("p",p :>Object);("nMin",nMin :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntRootExt (p:string) (nMin:BigInteger) (sRootBaseConstraint:string) (sIntBody:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "IntRootExt_encode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntRootExt_decode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Declare_ExtensionBit () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_ExtensionBit" []

let IntRootExt2 (p:string) (nMin:BigInteger) (sRootBaseConstraint:string) (sIntBody:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "IntRootExt2_encode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntRootExt2_decode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Null (p:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Null_encode" [("p",p :>Object)]
    | Decode    ->
        ST.call "uper" "Null_decode" [("p",p :>Object)]

let Boolean (p:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Boolean_encode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Boolean_decode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Real (p:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Real_encode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Real_decode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Declare_EnumIndex () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_EnumIndex" []

let Declare_AsnIntForMappingFuncion () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_AsnIntForMappingFuncion" []

let Enumerated_item (p:string) (sName:string) (nIndex:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Enumerated_item_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nIndex",nIndex :>Object)]
    | Decode    ->
        ST.call "uper" "Enumerated_item_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nIndex",nIndex :>Object)]

let Enumerated (p:string) (sTasName:string) (arrsItem:seq<string>) (nMin:BigInteger) (nMax:BigInteger) (nBits:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Enumerated_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Enumerated_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Sequence_optChild (p:string) (sChName:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Sequence_optChild_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Sequence_optChild_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Sequence_always_present_optChild (p:string) (sChName:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Sequence_always_present_optChild_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Sequence_always_present_optChild_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Sequence_Child (p:string) (sChName:string) (bIsUperOptional:bool) (sChildContent:string) (bHasDefaultValue:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Sequence_Child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("bIsUperOptional",bIsUperOptional :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("bHasDefaultValue",bHasDefaultValue :>Object)]
    | Decode    ->
        ST.call "uper" "Sequence_Child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("bIsUperOptional",bIsUperOptional :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("bHasDefaultValue",bHasDefaultValue :>Object)]

let JoinItems (sTasName:string) (sPart:string) (sNestedPart:string) (nRequiredBitsSoFar:BigInteger) (bRequiresResultCheck:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "JoinItems_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) );("nRequiredBitsSoFar",nRequiredBitsSoFar :>Object);("bRequiresResultCheck",bRequiresResultCheck :>Object)]
    | Decode    ->
        ST.call "uper" "JoinItems_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) );("nRequiredBitsSoFar",nRequiredBitsSoFar :>Object);("bRequiresResultCheck",bRequiresResultCheck :>Object)]

let Sequence (p:string) (arrsChildren:seq<string>) (sTasName:string) (bRequiresInit:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Sequence_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bRequiresInit",bRequiresInit :>Object)]
    | Decode    ->
        ST.call "uper" "Sequence_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("bRequiresInit",bRequiresInit :>Object)]

let ChoiceChild (sTasName:string) (sName:string) (sChildBody:string) (nIndex:BigInteger) (nIndexSizeInBits:BigInteger) (sNamePresent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "ChoiceChild_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("nIndex",nIndex :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object);("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]
    | Decode    ->
        ST.call "uper" "ChoiceChild_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("nIndex",nIndex :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object);("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let ChoiceChild_tmpVar (sName:string) (sTypeDecl:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "ChoiceChild_tmpVar" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) )]

let Choice (sTasName:string) (arrsChildren:seq<string>) (nIndexMax:BigInteger) (nIndexSizeInBits:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Choice_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nIndexMax",nIndexMax :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object)]
    | Decode    ->
        ST.call "uper" "Choice_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nIndexMax",nIndexMax :>Object);("nIndexSizeInBits",nIndexSizeInBits :>Object)]

let Declare_ChoiceIndex () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_ChoiceIndex" []

let ReferenceType1 (p:string) (sName:string) (bAcnEncodeFuncRequiresResult:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "ReferenceType1_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object)]
    | Decode    ->
        ST.call "uper" "ReferenceType1_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object)]

let ReferenceType2 (p:string) (sTasName:string) (sName:string) (bAcnEncodeFuncRequiresResult:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "ReferenceType2_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object)]
    | Decode    ->
        ST.call "uper" "ReferenceType2_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object)]

let InternalItem_oct_str (p:string) (i:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_oct_str_encode" [("p",p :>Object);("i",i :>Object)]
    | Decode    ->
        ST.call "uper" "InternalItem_oct_str_decode" [("p",p :>Object);("i",i :>Object)]

let InternalItem_bit_str (p:string) (i:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_bit_str_encode" [("p",p :>Object);("i",i :>Object)]
    | Decode    ->
        ST.call "uper" "InternalItem_bit_str_decode" [("p",p :>Object);("i",i :>Object)]

let oct_sqf_FixedSize (p:string) (i:string) (sInternalItem:string) (nFixedSize:BigInteger) (sTasName:string) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "oct_sqf_FixedSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "uper" "oct_sqf_FixedSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]

let oct_sqf_VarSize (sTasName:string) (p:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (nSizeInBits:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "oct_sqf_VarSize_encode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nSizeInBits",nSizeInBits :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "uper" "oct_sqf_VarSize_decode" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nSizeInBits",nSizeInBits :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]

let Declare_Length () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_Length" []

let Declare_CharValue () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_CharValue" []

let InternalItem_string_no_alpha (p:string) (i:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_string_no_alpha_encode" [("p",p :>Object);("i",i :>Object)]
    | Decode    ->
        ST.call "uper" "InternalItem_string_no_alpha_decode" [("p",p :>Object);("i",i :>Object)]

let InternalItem_string_with_alpha (p:string) (sTasName:string) (i:string) (nCharIndexSize:BigInteger) (nCharIndexMax:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_string_with_alpha_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("nCharIndexSize",nCharIndexSize :>Object);("nCharIndexMax",nCharIndexMax :>Object)]
    | Decode    ->
        ST.call "uper" "InternalItem_string_with_alpha_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("nCharIndexSize",nCharIndexSize :>Object);("nCharIndexMax",nCharIndexMax :>Object)]

let str_FixedSize (p:string) (sTasName:string) (i:string) (sInternalItem:string) (nFixedSize:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "str_FixedSize_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "uper" "str_FixedSize_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]

let str_VarSize (p:string) (sTasName:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (nSizeInBits:BigInteger) (nIntItemMinSize:BigInteger) (nIntItemMaxSize:BigInteger) (nAlignSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "str_VarSize_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nSizeInBits",nSizeInBits :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]
    | Decode    ->
        ST.call "uper" "str_VarSize_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("nSizeInBits",nSizeInBits :>Object);("nIntItemMinSize",nIntItemMinSize :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("nAlignSize",nAlignSize :>Object)]

let str_length (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "str_length" [("p",p :>Object)]

let bit_oct_sqof_length (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "bit_oct_sqof_length" [("p",p :>Object)]

let Declare_nCount () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_nCount" []

let Declare_curBlockSize () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_curBlockSize" []

let Declare_curItem () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_curItem" []

let Declare_len2 () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "uper" "Declare_len2" []

let Tas_fragmentation (sName:string) (arrsLocalVariables:seq<string>) (sContent:string) (bIsFixedSize:bool) (bResDependsOnData:bool) (bKDependsOnData:bool) (nIntItemMaxSize:BigInteger) (sInternalItem:string) (nUperMax:BigInteger) (bAcnEncodeFuncRequiresResult:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Tas_fragmentation_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nUperMax",nUperMax :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object)]
    | Decode    ->
        ST.call "uper" "Tas_fragmentation_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("bIsFixedSize",bIsFixedSize :>Object);("bResDependsOnData",bResDependsOnData :>Object);("bKDependsOnData",bKDependsOnData :>Object);("nIntItemMaxSize",nIntItemMaxSize :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nUperMax",nUperMax :>Object);("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object)]

let Fragmentation_sqf (sCount:string) (sInternalItem:string) (nIntItemMaxSize:BigInteger) (nUperMax:BigInteger) (bHasLength:bool) (sTasName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    match codec with
    | Encode    ->
        ST.call "uper" "Fragmentation_sqf_encode" [("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nIntItemMaxSize",nIntItemMaxSize :>Object);("nUperMax",nUperMax :>Object);("bHasLength",bHasLength :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) )]
    | Decode    ->
        ST.call "uper" "Fragmentation_sqf_decode" [("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nIntItemMaxSize",nIntItemMaxSize :>Object);("nUperMax",nUperMax :>Object);("bHasLength",bHasLength :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) )]

