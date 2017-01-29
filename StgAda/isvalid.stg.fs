module isvalid_a
open System
open System.Numerics
open Ast

let Print_AlphabetCheckFunc_str () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Print_AlphabetCheckFunc_str" []

let Print_AlphabetCheckFunc (sName:string) (arrsAlphaConBody:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Print_AlphabetCheckFunc" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsAlphaConBody",(arrsAlphaConBody|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintMultipleConstraints (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "PrintMultipleConstraints" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let callAlphaFunc (sFuncName:string) (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "callAlphaFunc" [("sFuncName",(if sFuncName = null then null else ST.StrHelper sFuncName:>Object) );("p",p :>Object)]

let getStringSize (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "getStringSize" [("p",p :>Object)]

let getSizeableSize (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "getSizeableSize" [("p",p :>Object)]

let stringContainsChar (sStrVal:string) (p:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "stringContainsChar" [("sStrVal",(if sStrVal = null then null else ST.StrHelper sStrVal:>Object) );("p",p :>Object)]

let PrintReference1 (p:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "PrintReference1" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let PrintReference2 (p:string) (sModName:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "PrintReference2" [("p",p :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let SingleValContraint (p:string) (v:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "SingleValContraint" [("p",p :>Object);("v",v :>Object)]

let RangeContraint (p:string) (v1:string) (v2:string) (bMin:bool) (bMax:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "RangeContraint" [("p",p :>Object);("v1",v1 :>Object);("v2",v2 :>Object);("bMin",bMin :>Object);("bMax",bMax :>Object)]

let RangeContraint_val_MAX (p:string) (v:string) (bMin:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "RangeContraint_val_MAX" [("p",p :>Object);("v",v :>Object);("bMin",bMin :>Object)]

let RangeContraint_MIN_val (p:string) (v:string) (bMax:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "RangeContraint_MIN_val" [("p",p :>Object);("v",v :>Object);("bMax",bMax :>Object)]

let AND_Constraint (sCon1:string) (sCon2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "AND_Constraint" [("sCon1",(if sCon1 = null then null else ST.StrHelper sCon1:>Object) );("sCon2",(if sCon2 = null then null else ST.StrHelper sCon2:>Object) )]

let OR_Constraint (sCon1:string) (sCon2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "OR_Constraint" [("sCon1",(if sCon1 = null then null else ST.StrHelper sCon1:>Object) );("sCon2",(if sCon2 = null then null else ST.StrHelper sCon2:>Object) )]

let AllExceptConstraint (sCon:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "AllExceptConstraint" [("sCon",(if sCon = null then null else ST.StrHelper sCon:>Object) )]

let ExceptConstraint (sCon1:string) (sCon2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "ExceptConstraint" [("sCon1",(if sCon1 = null then null else ST.StrHelper sCon1:>Object) );("sCon2",(if sCon2 = null then null else ST.StrHelper sCon2:>Object) )]

let Emit_local_variable_SQF_Index (nI:BigInteger) (bHasInitalValue:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_local_variable_SQF_Index" [("nI",nI :>Object);("bHasInitalValue",bHasInitalValue :>Object)]

let EmitTypeAssignment (sName:string) (sTypeBody:string) (arrsAlphaCheckFunctions:seq<string>) (arrsLocalVars:seq<string>) (sAsn1TypeDefinition:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "EmitTypeAssignment" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeBody",(if sTypeBody = null then null else ST.StrHelper sTypeBody:>Object) );("arrsAlphaCheckFunctions",(arrsAlphaCheckFunctions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalVars",(arrsLocalVars|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sAsn1TypeDefinition",(if sAsn1TypeDefinition = null then null else ST.StrHelper sAsn1TypeDefinition:>Object) )]

let Emit_type (arrsConstraints:seq<string>) (sErrCodeName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_type" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sErrCodeName",(if sErrCodeName = null then null else ST.StrHelper sErrCodeName:>Object) )]

let Emit_Reference1 (p:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_Reference1" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let Emit_Reference2 (p:string) (sModName:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_Reference2" [("p",p :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let Emit_sequence_of_assert (sI:string) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_sequence_of_assert" [("sI",(if sI = null then null else ST.StrHelper sI:>Object) );("nMax",nMax :>Object)]

let Emit_sequence_of (sI:string) (sPath:string) (nMax:BigInteger) (sSizeConstraint:string) (sChildBody:string) (bFixed:bool) (arrsAssrtAnts:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_sequence_of" [("sI",(if sI = null then null else ST.StrHelper sI:>Object) );("sPath",(if sPath = null then null else ST.StrHelper sPath:>Object) );("nMax",nMax :>Object);("sSizeConstraint",(if sSizeConstraint = null then null else ST.StrHelper sSizeConstraint:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("bFixed",bFixed :>Object);("arrsAssrtAnts",(arrsAssrtAnts|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Emit_fixedSize_constraint () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_fixedSize_constraint" []

let Emit_sequence_optional_component (sParentPath:string) (sName:string) (sChildBody:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_sequence_optional_component" [("sParentPath",(if sParentPath = null then null else ST.StrHelper sParentPath:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) )]

let Emit_sequence_check_component_is_always_present_or_absent (sParentPath:string) (sName:string) (nPresOrAbs:BigInteger) (sErrCode:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_sequence_check_component_is_always_present_or_absent" [("sParentPath",(if sParentPath = null then null else ST.StrHelper sParentPath:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nPresOrAbs",nPresOrAbs :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let JoinItems (sPart:string) (bCanFail:bool) (sNestedPart:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "JoinItems" [("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("bCanFail",bCanFail :>Object);("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) )]

let Emit_choice_child (sName:string) (sChildBody:string) (sNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_choice_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let Emit_choice (sTasName:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "isvalid" "Emit_choice" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

