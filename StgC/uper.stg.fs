module uper_c
open System
open System.Numerics
open Ast

let getStringSize (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "getStringSize" [("p",p :>Object)]

let getSizeableSize (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "getSizeableSize" [("p",p :>Object)]

let Print_AlphabetCheckFunc_str (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Print_AlphabetCheckFunc_str" [("p",p :>Object)]

let main (sFileNameWithoutExtension:string) (arrsUnnamedVariables:seq<string>) (arrsValueAssignments:seq<string>) (arrsTypeAssignments:seq<string>) (soMappingFunctionsModule:string option) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "main" [("sFileNameWithoutExtension",(if sFileNameWithoutExtension = null then null else ST.StrHelper sFileNameWithoutExtension:>Object) );("arrsUnnamedVariables",(arrsUnnamedVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsValueAssignments",(arrsValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("soMappingFunctionsModule",(if soMappingFunctionsModule.IsNone then null else ST.StrHelper soMappingFunctionsModule.Value:>Object) )]

let gcc_main (sFileNameWithoutExtension:string) (arrsValueAssignments:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "gcc_main" [("sFileNameWithoutExtension",(if sFileNameWithoutExtension = null then null else ST.StrHelper sFileNameWithoutExtension:>Object) );("arrsValueAssignments",(arrsValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintUnnamedVariable (sTypeDecl:string) (sName:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintUnnamedVariable" [("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintValueAssignment (sTypeDecl:string) (sName:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintValueAssignment" [("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintInitialize (sTasName:string) (sStar:string) (sContent:string) (bIsString:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintInitialize" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("bIsString",bIsString :>Object)]

let PrintIsConstraintValid (sTasName:string) (sStar:string) (arrsLocalVariables:seq<string>) (sContent:string) (arrsAlphaCheckFunctions:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintIsConstraintValid" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("arrsAlphaCheckFunctions",(arrsAlphaCheckFunctions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let SingleValContraint (p:string) (v:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "SingleValContraint" [("p",p :>Object);("v",v :>Object)]

let SingleValContraint_bitString_fixedSize (p1:string) (p2:string) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "SingleValContraint_bitString_fixedSize" [("p1",p1 :>Object);("p2",p2 :>Object);("nFixedSize",nFixedSize :>Object)]

let SingleValContraint_bitString_varSize (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "SingleValContraint_bitString_varSize" [("p1",p1 :>Object);("p2",p2 :>Object)]

let SingleValContraint_octetString_fixedSize (p1:string) (p2:string) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "SingleValContraint_octetString_fixedSize" [("p1",p1 :>Object);("p2",p2 :>Object);("nFixedSize",nFixedSize :>Object)]

let SingleValContraint_octetString_varSize (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "SingleValContraint_octetString_varSize" [("p1",p1 :>Object);("p2",p2 :>Object)]

let stringContainsChar (sStrVal:string) (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "stringContainsChar" [("sStrVal",(if sStrVal = null then null else ST.StrHelper sStrVal:>Object) );("p",p :>Object)]

let RangeContraint (p:string) (v1:string) (v2:string) (bMin:bool) (bMax:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "RangeContraint" [("p",p :>Object);("v1",v1 :>Object);("v2",v2 :>Object);("bMin",bMin :>Object);("bMax",bMax :>Object)]

let RangeContraint_val_MAX (p:string) (v:string) (bMin:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "RangeContraint_val_MAX" [("p",p :>Object);("v",v :>Object);("bMin",bMin :>Object)]

let RangeContraint_MIN_val (p:string) (v:string) (bMax:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "RangeContraint_MIN_val" [("p",p :>Object);("v",v :>Object);("bMax",bMax :>Object)]

let AND_Constraint (sCon1:string) (sCon2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "AND_Constraint" [("sCon1",(if sCon1 = null then null else ST.StrHelper sCon1:>Object) );("sCon2",(if sCon2 = null then null else ST.StrHelper sCon2:>Object) )]

let OR_Constraint (sCon1:string) (sCon2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "OR_Constraint" [("sCon1",(if sCon1 = null then null else ST.StrHelper sCon1:>Object) );("sCon2",(if sCon2 = null then null else ST.StrHelper sCon2:>Object) )]

let AllExceptConstraint (sCon:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "AllExceptConstraint" [("sCon",(if sCon = null then null else ST.StrHelper sCon:>Object) )]

let ExceptConstraint (sCon1:string) (sCon2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "ExceptConstraint" [("sCon1",(if sCon1 = null then null else ST.StrHelper sCon1:>Object) );("sCon2",(if sCon2 = null then null else ST.StrHelper sCon2:>Object) )]

let callAlphaFunc (sFuncName:string) (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "callAlphaFunc" [("sFuncName",(if sFuncName = null then null else ST.StrHelper sFuncName:>Object) );("p",p :>Object)]

let PrintMultipleConstraints (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintMultipleConstraints" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Emit_local_variable_SQF_Index (nI:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_local_variable_SQF_Index" [("nI",nI :>Object)]

let Print_AlphabetCheckFunc (sName:string) (arrsAlphaConBody:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Print_AlphabetCheckFunc" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsAlphaConBody",(arrsAlphaConBody|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Emit_type (arrsConstraints:seq<string>) (sErrCodeName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_type" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sErrCodeName",(if sErrCodeName = null then null else ST.StrHelper sErrCodeName:>Object) )]

let Emit_Reference1 (p:string) (sTasName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_Reference1" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) )]

let Emit_Reference2 (p:string) (sModName:string) (sTasName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_Reference2" [("p",p :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) )]

let Emit_sequence_optional_component (sParentPath:string) (sName:string) (sChildBody:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_sequence_optional_component" [("sParentPath",(if sParentPath = null then null else ST.StrHelper sParentPath:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) )]

let Emit_sequence_check_component_is_always_present_or_absent (sParentPath:string) (sName:string) (nPresOrAbs:BigInteger) (sErrCode:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_sequence_check_component_is_always_present_or_absent" [("sParentPath",(if sParentPath = null then null else ST.StrHelper sParentPath:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nPresOrAbs",nPresOrAbs :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let JoinItems (sPart:string) (sNestedPart:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "JoinItems" [("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) )]

let Emit_choice_child (sChPresent:string) (sChildBody:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_choice_child" [("sChPresent",(if sChPresent = null then null else ST.StrHelper sChPresent:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) )]

let Emit_choice (p:string) (arrsChildren:seq<string>) (sChoiceErrName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_choice" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sChoiceErrName",(if sChoiceErrName = null then null else ST.StrHelper sChoiceErrName:>Object) )]

let Emit_fixedSize_constraint () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_fixedSize_constraint" []

let Emit_sequence_of (sI:string) (sPath:string) (nMax:BigInteger) (sSizeConstraint:string) (sChildBody:string) (bFixed:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Emit_sequence_of" [("sI",(if sI = null then null else ST.StrHelper sI:>Object) );("sPath",(if sPath = null then null else ST.StrHelper sPath:>Object) );("nMax",nMax :>Object);("sSizeConstraint",(if sSizeConstraint = null then null else ST.StrHelper sSizeConstraint:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("bFixed",bFixed :>Object)]

let PrintEqual (sName:string) (sStar:string) (arrsLocalVariables:seq<string>) (sContent:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintEqual" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]

let isEqual_Integer (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Integer" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Enumerated (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Enumerated" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Boolean (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Boolean" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Real (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Real" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_IA5String (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_IA5String" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_NumericString (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_NumericString" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_NullType () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_NullType" []

let isEqual_BitString (p1:string) (p2:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_BitString" [("p1",p1 :>Object);("p2",p2 :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object)]

let isEqual_OctetString (p1:string) (p2:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_OctetString" [("p1",p1 :>Object);("p2",p2 :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object)]

let isEqual_Choice_Child (sCid:string) (sInnerType:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Choice_Child" [("sCid",(if sCid = null then null else ST.StrHelper sCid:>Object) );("sInnerType",(if sInnerType = null then null else ST.StrHelper sInnerType:>Object) )]

let isEqual_Choice (p1:string) (p2:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Choice" [("p1",p1 :>Object);("p2",p2 :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let isEqual_Sequence_child (p1:string) (p2:string) (bIsOptional:bool) (sChName:string) (sInnerType:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_Sequence_child" [("p1",p1 :>Object);("p2",p2 :>Object);("bIsOptional",bIsOptional :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sInnerType",(if sInnerType = null then null else ST.StrHelper sInnerType:>Object) )]

let isEqual_SequenceOf (p1:string) (p2:string) (i:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) (sInnerType:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_SequenceOf" [("p1",p1 :>Object);("p2",p2 :>Object);("i",i :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object);("sInnerType",(if sInnerType = null then null else ST.StrHelper sInnerType:>Object) )]

let isEqual_ReferenceType (sPtr1:string) (sPtr2:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "isEqual_ReferenceType" [("sPtr1",(if sPtr1 = null then null else ST.StrHelper sPtr1:>Object) );("sPtr2",(if sPtr2 = null then null else ST.StrHelper sPtr2:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let Declare_EnumIndex () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Declare_EnumIndex" []

let Declare_Length () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Declare_Length" []

let Declare_ChoiceIndex () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Declare_ChoiceIndex" []

let Declare_SequenceBitMask (sName:string) (nSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "Declare_SequenceBitMask" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nSize",nSize :>Object)]

let PrintUper (sName:string) (sStar:string) (arrsLocalVariables:seq<string>) (sContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "PrintUper_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]
    | Decode    ->
        ST.call "uper" "PrintUper_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]

let InternalItem_oct_str (p:string) (i:string) (sErrInsufficientData:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_oct_str_encode" [("p",p :>Object);("i",i :>Object);("sErrInsufficientData",(if sErrInsufficientData = null then null else ST.StrHelper sErrInsufficientData:>Object) )]
    | Decode    ->
        ST.call "uper" "InternalItem_oct_str_decode" [("p",p :>Object);("i",i :>Object);("sErrInsufficientData",(if sErrInsufficientData = null then null else ST.StrHelper sErrInsufficientData:>Object) )]

let PrintAlphabet2 (arrnCharSet:seq<BigInteger>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintAlphabet2" [("arrnCharSet",arrnCharSet|>Seq.toArray :>Object)]

let InternalItem_string_with_alpha (p:string) (i:string) (nLastItemIndex:BigInteger) (arrnAlphabetAsciiCodes:seq<BigInteger>) (nAlphabetLength:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_string_with_alpha_encode" [("p",p :>Object);("i",i :>Object);("nLastItemIndex",nLastItemIndex :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nAlphabetLength",nAlphabetLength :>Object)]
    | Decode    ->
        ST.call "uper" "InternalItem_string_with_alpha_decode" [("p",p :>Object);("i",i :>Object);("nLastItemIndex",nLastItemIndex :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nAlphabetLength",nAlphabetLength :>Object)]

let InternalItem_string_no_alpha (p:string) (i:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "InternalItem_string_no_alpha_encode" [("p",p :>Object);("i",i :>Object)]
    | Decode    ->
        ST.call "uper" "InternalItem_string_no_alpha_decode" [("p",p :>Object);("i",i :>Object)]

let IntFullyConstraint (p:string) (nMin:BigInteger) (nMax:BigInteger) (nBits:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntFullyConstraint_encode" [("p",p :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntFullyConstraint_decode" [("p",p :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntFullyConstraintPos (p:string) (nMin:BigInteger) (nMax:BigInteger) (nBits:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntFullyConstraintPos_encode" [("p",p :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntFullyConstraintPos_decode" [("p",p :>Object);("nMin",nMin :>Object);("nMax",nMax :>Object);("nBits",nBits :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntUnconstraint (p:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntUnconstraint_encode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntUnconstraint_decode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntSemiConstraint (p:string) (nMin:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntSemiConstraint_encode" [("p",p :>Object);("nMin",nMin :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntSemiConstraint_decode" [("p",p :>Object);("nMin",nMin :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntSemiConstraintPos (p:string) (nMin:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntSemiConstraintPos_encode" [("p",p :>Object);("nMin",nMin :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntSemiConstraintPos_decode" [("p",p :>Object);("nMin",nMin :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntNoneRequired (p:string) (nConst:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntNoneRequired_encode" [("p",p :>Object);("nConst",nConst :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntNoneRequired_decode" [("p",p :>Object);("nConst",nConst :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntRootExt (p:string) (nMin:BigInteger) (sRootBaseConstraint:string) (sIntBody:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntRootExt_encode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntRootExt_decode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let IntRootExt2 (p:string) (nMin:BigInteger) (sRootBaseConstraint:string) (sIntBody:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "IntRootExt2_encode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "IntRootExt2_decode" [("p",p :>Object);("nMin",nMin :>Object);("sRootBaseConstraint",(if sRootBaseConstraint = null then null else ST.StrHelper sRootBaseConstraint:>Object) );("sIntBody",(if sIntBody = null then null else ST.StrHelper sIntBody:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Null (p:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "Null_encode" [("p",p :>Object)]
    | Decode    ->
        ST.call "uper" "Null_decode" [("p",p :>Object)]

let Boolean (p:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "Boolean_encode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Boolean_decode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let Real (p:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "Real_encode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "Real_decode" [("p",p :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let uper_Enumerated_item (p:string) (sName:string) (nIndex:BigInteger) (nLastItemIndex:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Enumerated_item_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nIndex",nIndex :>Object);("nLastItemIndex",nLastItemIndex :>Object)]
    | Decode    ->
        ST.call "uper" "uper_Enumerated_item_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nIndex",nIndex :>Object);("nLastItemIndex",nLastItemIndex :>Object)]

let uper_Enumerated (p:string) (arrsItem:seq<string>) (sErrCode:string) (nLastItemIndex:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Enumerated_encode" [("p",p :>Object);("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) );("nLastItemIndex",nLastItemIndex :>Object)]
    | Decode    ->
        ST.call "uper" "uper_Enumerated_decode" [("p",p :>Object);("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) );("nLastItemIndex",nLastItemIndex :>Object)]

let ReferenceType1 (p:string) (sName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "ReferenceType1_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]
    | Decode    ->
        ST.call "uper" "ReferenceType1_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let ReferenceType2 (p:string) (sModName:string) (sName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "ReferenceType2_encode" [("p",p :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]
    | Decode    ->
        ST.call "uper" "ReferenceType2_decode" [("p",p :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let uper_Choice_child (p:string) (sChildID:string) (nChildIndex:BigInteger) (nLastItemIndex:BigInteger) (sChildContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Choice_child_encode" [("p",p :>Object);("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("nChildIndex",nChildIndex :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Choice_child_decode" [("p",p :>Object);("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("nChildIndex",nChildIndex :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]

let uper_Choice (p:string) (arrsChildren:seq<string>) (nLastItemIndex:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Choice_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Choice_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let uper_Sequence_optChild (p:string) (sChName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Sequence_optChild_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Sequence_optChild_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) )]

let uper_Sequence_optChild_always_present (p:string) (sChName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Sequence_optChild_always_present_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Sequence_optChild_always_present_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) )]

let uper_Sequence_mandatory_child (sChName:string) (sChildContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Sequence_mandatory_child_encode" [("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Sequence_mandatory_child_decode" [("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]

let uper_Sequence_optional_child (p:string) (sChName:string) (sChildContent:string) (sBitMaskName:string) (nByteIndex:BigInteger) (sAndMask:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Sequence_optional_child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nByteIndex",nByteIndex :>Object);("sAndMask",(if sAndMask = null then null else ST.StrHelper sAndMask:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Sequence_optional_child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nByteIndex",nByteIndex :>Object);("sAndMask",(if sAndMask = null then null else ST.StrHelper sAndMask:>Object) )]

let uper_Sequence_default_child (p:string) (sChName:string) (sChildContent:string) (sBitMaskName:string) (nByteIndex:BigInteger) (sAndMask:string) (sChildTypeDeclaration:string) (sDefaultValue:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Sequence_default_child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nByteIndex",nByteIndex :>Object);("sAndMask",(if sAndMask = null then null else ST.StrHelper sAndMask:>Object) );("sChildTypeDeclaration",(if sChildTypeDeclaration = null then null else ST.StrHelper sChildTypeDeclaration:>Object) );("sDefaultValue",(if sDefaultValue = null then null else ST.StrHelper sDefaultValue:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_Sequence_default_child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nByteIndex",nByteIndex :>Object);("sAndMask",(if sAndMask = null then null else ST.StrHelper sAndMask:>Object) );("sChildTypeDeclaration",(if sChildTypeDeclaration = null then null else ST.StrHelper sChildTypeDeclaration:>Object) );("sDefaultValue",(if sDefaultValue = null then null else ST.StrHelper sDefaultValue:>Object) )]

let uper_Sequence (sChildren:string) (bHasOptionalChildren:bool) (sBitMaskName:string) (nOptionalChildrenLength:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_Sequence_encode" [("sChildren",(if sChildren = null then null else ST.StrHelper sChildren:>Object) );("bHasOptionalChildren",bHasOptionalChildren :>Object);("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nOptionalChildrenLength",nOptionalChildrenLength :>Object)]
    | Decode    ->
        ST.call "uper" "uper_Sequence_decode" [("sChildren",(if sChildren = null then null else ST.StrHelper sChildren:>Object) );("bHasOptionalChildren",bHasOptionalChildren :>Object);("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nOptionalChildrenLength",nOptionalChildrenLength :>Object)]

let uper_str_FixedSize (p:string) (i:string) (sInternalItem:string) (nFixedSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_str_FixedSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object)]
    | Decode    ->
        ST.call "uper" "uper_str_FixedSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object)]

let uper_str_VarSize (p:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (sStrLen:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_str_VarSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("sStrLen",(if sStrLen = null then null else ST.StrHelper sStrLen:>Object) )]
    | Decode    ->
        ST.call "uper" "uper_str_VarSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("sStrLen",(if sStrLen = null then null else ST.StrHelper sStrLen:>Object) )]

let oct_sqf_FixedSize (p:string) (i:string) (sInternalItem:string) (nFixedSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "oct_sqf_FixedSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object)]
    | Decode    ->
        ST.call "uper" "oct_sqf_FixedSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object)]

let oct_sqf_VarSize (p:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (sCount:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "oct_sqf_VarSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) )]
    | Decode    ->
        ST.call "uper" "oct_sqf_VarSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) )]

let uper_bitString_FixSize (p:string) (nFixedSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_bitString_FixSize_encode" [("p",p :>Object);("nFixedSize",nFixedSize :>Object)]
    | Decode    ->
        ST.call "uper" "uper_bitString_FixSize_decode" [("p",p :>Object);("nFixedSize",nFixedSize :>Object)]

let uper_bitString_VarSize (p:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "uper_bitString_VarSize_encode" [("p",p :>Object);("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object)]
    | Decode    ->
        ST.call "uper" "uper_bitString_VarSize_decode" [("p",p :>Object);("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object)]

let Fragmentation_sqf (p:string) (bIsBitStringType:bool) (nLevel:BigInteger) (sInternalItem:string) (sCount:string) (nUperMax:BigInteger) (bIsAsciiString:bool) (bIsFixedSize:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "uper" "Fragmentation_sqf_encode" [("p",p :>Object);("bIsBitStringType",bIsBitStringType :>Object);("nLevel",nLevel :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("nUperMax",nUperMax :>Object);("bIsAsciiString",bIsAsciiString :>Object);("bIsFixedSize",bIsFixedSize :>Object)]
    | Decode    ->
        ST.call "uper" "Fragmentation_sqf_decode" [("p",p :>Object);("bIsBitStringType",bIsBitStringType :>Object);("nLevel",nLevel :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("nUperMax",nUperMax :>Object);("bIsAsciiString",bIsAsciiString :>Object);("bIsFixedSize",bIsFixedSize :>Object)]

let PrintDefaultAcnModule (sModName:string) (arrsTypeAssignments:seq<string>) (sAssignOperator:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "uper" "PrintDefaultAcnModule" [("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sAssignOperator",(if sAssignOperator = null then null else ST.StrHelper sAssignOperator:>Object) )]

