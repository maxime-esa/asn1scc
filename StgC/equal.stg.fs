module equal_c
open System
open System.Numerics
open Ast

let JoinItems (sPart:string) (soNestedPart:string option) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "JoinItems" [("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("soNestedPart",(if soNestedPart.IsNone then null else ST.StrHelper soNestedPart.Value:>Object) )]

let PrintEqualPrimitive (sFuncName:string) (sTypeDefName:string) (sContent:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "PrintEqualPrimitive" [("sFuncName",(if sFuncName = null then null else ST.StrHelper sFuncName:>Object) );("sTypeDefName",(if sTypeDefName = null then null else ST.StrHelper sTypeDefName:>Object) );("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]

let PrintEqualSequence (sFuncName:string) (sTypeDefName:string) (sContent:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "PrintEqualSequence" [("sFuncName",(if sFuncName = null then null else ST.StrHelper sFuncName:>Object) );("sTypeDefName",(if sTypeDefName = null then null else ST.StrHelper sTypeDefName:>Object) );("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]

let isEqual_Integer (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Integer" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Enumerated (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Enumerated" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Boolean (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Boolean" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_Real (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Real" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_IA5String (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_IA5String" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_NumericString (p1:string) (p2:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_NumericString" [("p1",p1 :>Object);("p2",p2 :>Object)]

let isEqual_NullType () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_NullType" []

let isEqual_BitString (p1:string) (p2:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_BitString" [("p1",p1 :>Object);("p2",p2 :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object)]

let isEqual_OctetString (p1:string) (p2:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_OctetString" [("p1",p1 :>Object);("p2",p2 :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object)]

let isEqual_Choice_Child (sCid:string) (sInnerType:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Choice_Child" [("sCid",(if sCid = null then null else ST.StrHelper sCid:>Object) );("sInnerType",(if sInnerType = null then null else ST.StrHelper sInnerType:>Object) )]

let isEqual_Choice (p1:string) (p2:string) (arrsChildren:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Choice" [("p1",p1 :>Object);("p2",p2 :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let isEqual_Sequence_child (p1:string) (p2:string) (sAcc:string) (bIsOptional:bool) (sChName:string) (soInnerStatement:string option) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_Sequence_child" [("p1",p1 :>Object);("p2",p2 :>Object);("sAcc",(if sAcc = null then null else ST.StrHelper sAcc:>Object) );("bIsOptional",bIsOptional :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("soInnerStatement",(if soInnerStatement.IsNone then null else ST.StrHelper soInnerStatement.Value:>Object) )]

let isEqual_SequenceOf (p1:string) (p2:string) (sAcc:string) (i:string) (bIsFixedSize:bool) (nFixedSize:BigInteger) (soInnerStatement:string option) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_SequenceOf" [("p1",p1 :>Object);("p2",p2 :>Object);("sAcc",(if sAcc = null then null else ST.StrHelper sAcc:>Object) );("i",i :>Object);("bIsFixedSize",bIsFixedSize :>Object);("nFixedSize",nFixedSize :>Object);("soInnerStatement",(if soInnerStatement.IsNone then null else ST.StrHelper soInnerStatement.Value:>Object) )]

let isEqual_ReferenceType (sPtr1:string) (sPtr2:string) (sName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "equal" "isEqual_ReferenceType" [("sPtr1",(if sPtr1 = null then null else ST.StrHelper sPtr1:>Object) );("sPtr2",(if sPtr2 = null then null else ST.StrHelper sPtr2:>Object) );("sName",(if sName = null then null else ST.StrHelper sName:>Object) )]

