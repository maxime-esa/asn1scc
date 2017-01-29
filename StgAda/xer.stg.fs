module xer_a
open System
open System.Numerics
open Ast

let CHOICE_setters_body_child (sTasName:string) (sName:string) (sType:string) (sNamePresent:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "CHOICE_setters_body_child" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sType",(if sType = null then null else ST.StrHelper sType:>Object) );("sNamePresent",(if sNamePresent = null then null else ST.StrHelper sNamePresent:>Object) )]

let CHOICE_setters_body (sTasName:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "CHOICE_setters_body" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintTypeAssignment (sName:string) (sInitBody:string) (bContainsChoice:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "PrintTypeAssignment" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sInitBody",(if sInitBody = null then null else ST.StrHelper sInitBody:>Object) );("bContainsChoice",bContainsChoice :>Object)]

let PrimitiveEqual (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "PrimitiveEqual" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Integer (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Integer" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Real (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Real" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_IA5String (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_IA5String" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_NumericString (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_NumericString" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_OctetString (p1:string) (p2:string) (bFixedSize:bool) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_OctetString" [("p1",p1 :>Object);("p2",p2 :>Object);("bFixedSize",bFixedSize :>Object);("nFixedSize",nFixedSize :>Object)]

let isEqual_NullType () =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_NullType" []

let isEqual_BitString (p1:string) (p2:string) (bFixedSize:bool) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_BitString" [("p1",p1 :>Object);("p2",p2 :>Object);("bFixedSize",bFixedSize :>Object);("nFixedSize",nFixedSize :>Object)]

let isEqual_Boolean (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Boolean" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Enumerated (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Enumerated" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_SequenceOf (p1:string) (p2:string) (i:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) (sInnerType:string) (sInnerTypeName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_SequenceOf" [("p1",p1 :>Object);("p2",p2 :>Object);("i",i :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object);("sInnerType",(if sInnerType = null then null else ST.StrHelper sInnerType:>Object) );("sInnerTypeName",(if sInnerTypeName = null then null else ST.StrHelper sInnerTypeName:>Object) )]

let isEqual_Choice_Child (p1:string) (p2:string) (sCid:string) (sAsn1Id:string) (sInnerType:string) (sTasName:string) (sInnerTypeName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Choice_Child" [("p1",p1 :>Object);("p2",p2 :>Object);("sCid",(if sCid = null then null else ST.StrHelper sCid:>Object) );("sAsn1Id",(if sAsn1Id = null then null else ST.StrHelper sAsn1Id:>Object) );("sInnerType",(if sInnerType = null then null else ST.StrHelper sInnerType:>Object) );("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sInnerTypeName",(if sInnerTypeName = null then null else ST.StrHelper sInnerTypeName:>Object) )]

let isEqual_Choice (p1:string) (p2:string) (arrsChildren:seq<string>) (sTasName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Choice" [("p1",p1 :>Object);("p2",p2 :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) )]

let isEqual_Sequence_Child (p1:string) (p2:string) (bIsOptional:bool) (sChName:string) (sInnerTypeName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Sequence_Child" [("p1",p1 :>Object);("p2",p2 :>Object);("bIsOptional",bIsOptional :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sInnerTypeName",(if sInnerTypeName = null then null else ST.StrHelper sInnerTypeName:>Object) )]

let isEqual_Sequence (p1:string) (p2:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_Sequence" [("p1",p1 :>Object);("p2",p2 :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let isEqual_ReferenceType (sPtr1:string) (sPtr2:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "isEqual_ReferenceType" [("sPtr1",(if sPtr1 = null then null else ST.StrHelper sPtr1:>Object) );("sPtr2",(if sPtr2 = null then null else ST.StrHelper sPtr2:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

let PrintTypeAssignment_Equal (sName:string) (sBody:string) (arrsLocalVariables:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "xer" "PrintTypeAssignment_Equal" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sBody",(if sBody = null then null else ST.StrHelper sBody:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

