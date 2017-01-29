module stg_asn1
open System
open System.Numerics
open Ast

let PrintAsn1File (arrsModules:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintAsn1File" [("arrsModules",(arrsModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintModule (sName:string) (arrsTas:seq<string>) (arrsVas:seq<string>) (sExports:string) (arrsImportsFromModule:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintModule" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsTas",(arrsTas|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsVas",(arrsVas|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sExports",(if sExports = null then null else ST.StrHelper sExports:>Object) );("arrsImportsFromModule",(arrsImportsFromModule|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintModuleImportFromModule (arrsImports:seq<string>) (sModName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintModuleImportFromModule" [("arrsImports",(arrsImports|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) )]

let PrintTypeAssigment (sName:string) (sType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintTypeAssigment" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) )]

let PrintTypeAssigment2 (sID:string) (soBaseType:string option) (sName:string) (sTypeBody:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintTypeAssigment2" [("sID",(if sID = null then null else ST.StrHelper sID:>Object) );("soBaseType",(if soBaseType.IsNone then null else ST.StrHelper soBaseType.Value:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeBody",(if sTypeBody = null then null else ST.StrHelper sTypeBody:>Object) )]

let PrintValueAssigment (sName:string) (sType:string) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintValueAssigment" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let PrintType (sTypeSpecific:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "PrintType" [("sTypeSpecific",(if sTypeSpecific = null then null else ST.StrHelper sTypeSpecific:>Object) )]

let Print_Integer (sUPER:string) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Integer" [("sUPER",(if sUPER = null then null else ST.StrHelper sUPER:>Object) );("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_Real (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Real" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_IA5String (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_IA5String" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_IA5String2 (sSizeUper:string) (sAlphaUper:string) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_IA5String2" [("sSizeUper",(if sSizeUper = null then null else ST.StrHelper sSizeUper:>Object) );("sAlphaUper",(if sAlphaUper = null then null else ST.StrHelper sAlphaUper:>Object) );("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_NumericString (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_NumericString" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_OctetString (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_OctetString" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_NullType (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_NullType" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_BitString (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_BitString" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_Boolean (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Boolean" [("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_Enumerated_child (sName:string) (bHasValue:bool) (sValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Enumerated_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bHasValue",bHasValue :>Object);("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) )]

let Print_Enumerated (arrsItems:seq<string>) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Enumerated" [("arrsItems",(arrsItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_SequenceOf (sChild:string) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_SequenceOf" [("sChild",(if sChild = null then null else ST.StrHelper sChild:>Object) );("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_Sequence_child (sName:string) (sChildType:string) (bIsOptionalOrDefault:bool) (soDefValue:string option) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Sequence_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildType",(if sChildType = null then null else ST.StrHelper sChildType:>Object) );("bIsOptionalOrDefault",bIsOptionalOrDefault :>Object);("soDefValue",(if soDefValue.IsNone then null else ST.StrHelper soDefValue.Value:>Object) )]

let Print_Sequence (arrsChildren:seq<string>) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Sequence" [("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_Choice_child (sName:string) (sChildType:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Choice_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildType",(if sChildType = null then null else ST.StrHelper sChildType:>Object) )]

let Print_Choice (arrsChildren:seq<string>) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_Choice" [("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_ReferenceType1 (sName:string) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_ReferenceType1" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_ReferenceType2 (sModName:string) (sName:string) (arrsConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_ReferenceType2" [("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("arrsConstraints",(arrsConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_IntegerValue (nVal:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_IntegerValue" [("nVal",nVal :>Object)]

let Print_RealValue (dVal:double) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RealValue" [("dVal",dVal :>Object)]

let Print_StringValue (v:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_StringValue" [("v",v :>Object)]

let Print_BooleanValue (bVal:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_BooleanValue" [("bVal",bVal :>Object)]

let Print_BitStringValue (v:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_BitStringValue" [("v",v :>Object)]

let Print_OctetStringValue (arruOctets:seq<byte>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_OctetStringValue" [("arruOctets",arruOctets|>Seq.toArray :>Object)]

let Print_RefValue (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RefValue" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let Print_SeqOfValue (arrsValues:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_SeqOfValue" [("arrsValues",(arrsValues|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_SeqValue_Child (sName:string) (sChildValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_SeqValue_Child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sChildValue",(if sChildValue = null then null else ST.StrHelper sChildValue:>Object) )]

let Print_SeqValue (arrsValues:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_SeqValue" [("arrsValues",(arrsValues|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Print_ChValue (sAltName:string) (sAltValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_ChValue" [("sAltName",(if sAltName = null then null else ST.StrHelper sAltName:>Object) );("sAltValue",(if sAltValue = null then null else ST.StrHelper sAltValue:>Object) )]

let Print_NullValue () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_NullValue" []

let Print_SingleValueContraint (v:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_SingleValueContraint" [("v",v :>Object)]

let Print_RangeContraint (v1:string) (v2:string) (bMin:bool) (bMax:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RangeContraint" [("v1",v1 :>Object);("v2",v2 :>Object);("bMin",bMin :>Object);("bMax",bMax :>Object)]

let Print_RangeContraint_val_MAX (v:string) (bMin:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RangeContraint_val_MAX" [("v",v :>Object);("bMin",bMin :>Object)]

let Print_RangeContraint_MIN_val (v:string) (bMax:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RangeContraint_MIN_val" [("v",v :>Object);("bMax",bMax :>Object)]

let Print_RangeContraint_MIN_MAX () =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RangeContraint_MIN_MAX" []

let Print_TypeInclusionConstraint (sRefName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_TypeInclusionConstraint" [("sRefName",(if sRefName = null then null else ST.StrHelper sRefName:>Object) )]

let Print_SizeContraint (sInnerConstraint:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_SizeContraint" [("sInnerConstraint",(if sInnerConstraint = null then null else ST.StrHelper sInnerConstraint:>Object) )]

let Print_AlphabetContraint (sInnerConstraint:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_AlphabetContraint" [("sInnerConstraint",(if sInnerConstraint = null then null else ST.StrHelper sInnerConstraint:>Object) )]

let Print_UnionConstraint (sInnerConstraint1:string) (sInnerConstraint2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_UnionConstraint" [("sInnerConstraint1",(if sInnerConstraint1 = null then null else ST.StrHelper sInnerConstraint1:>Object) );("sInnerConstraint2",(if sInnerConstraint2 = null then null else ST.StrHelper sInnerConstraint2:>Object) )]

let Print_IntersectionConstraint (sInnerConstraint1:string) (sInnerConstraint2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_IntersectionConstraint" [("sInnerConstraint1",(if sInnerConstraint1 = null then null else ST.StrHelper sInnerConstraint1:>Object) );("sInnerConstraint2",(if sInnerConstraint2 = null then null else ST.StrHelper sInnerConstraint2:>Object) )]

let Print_AllExceptConstraint (sInnerConstraint:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_AllExceptConstraint" [("sInnerConstraint",(if sInnerConstraint = null then null else ST.StrHelper sInnerConstraint:>Object) )]

let Print_ExceptConstraint (sInnerConstraint1:string) (sInnerConstraint2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_ExceptConstraint" [("sInnerConstraint1",(if sInnerConstraint1 = null then null else ST.StrHelper sInnerConstraint1:>Object) );("sInnerConstraint2",(if sInnerConstraint2 = null then null else ST.StrHelper sInnerConstraint2:>Object) )]

let Print_RootConstraint (sInnerConstraint:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RootConstraint" [("sInnerConstraint",(if sInnerConstraint = null then null else ST.StrHelper sInnerConstraint:>Object) )]

let Print_RootConstraint2 (sInnerConstraint1:string) (sInnerConstraint2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_RootConstraint2" [("sInnerConstraint1",(if sInnerConstraint1 = null then null else ST.StrHelper sInnerConstraint1:>Object) );("sInnerConstraint2",(if sInnerConstraint2 = null then null else ST.StrHelper sInnerConstraint2:>Object) )]

let Print_WithComponentConstraint (sInnerConstraint:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_WithComponentConstraint" [("sInnerConstraint",(if sInnerConstraint = null then null else ST.StrHelper sInnerConstraint:>Object) )]

let Print_WithComponentsConstraint_child (sName:string) (sContraint:string) (sPresMark:string) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_WithComponentsConstraint_child" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sContraint",(if sContraint = null then null else ST.StrHelper sContraint:>Object) );("sPresMark",(if sPresMark = null then null else ST.StrHelper sPresMark:>Object) )]

let Print_WithComponentsConstraint (arrsInnerConstraints:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Unknown
    ST.call "ASN" "Print_WithComponentsConstraint" [("arrsInnerConstraints",(arrsInnerConstraints|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

