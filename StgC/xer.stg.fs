module xer_c
open System
open System.Numerics
open Ast

let PrintTas (sName:string) (sStar:string) (arrsLocalVariables:seq<string>) (sContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "PrintTas_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]
    | Decode    ->
        ST.call "xer" "PrintTas_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]

let PrintTasWithTag (sName:string) (sStar:string) (arrsLocalVariables:seq<string>) (sContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "PrintTasWithTag_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]
    | Decode    ->
        ST.call "xer" "PrintTasWithTag_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) )]

let Integer (p:string) (sTag:string) (nLevel:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "Integer_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]
    | Decode    ->
        ST.call "xer" "Integer_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]

let BOOLEAN (p:string) (sTag:string) (nLevel:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "BOOLEAN_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]
    | Decode    ->
        ST.call "xer" "BOOLEAN_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]

let ENUMERATED_item (p:string) (sTag:string) (nLevel:BigInteger) (sItemID:string) (sXerValue:string) (bFirst:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "ENUMERATED_item_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sItemID",(if sItemID = null then null else ST.StrHelper sItemID:>Object) );("sXerValue",(if sXerValue = null then null else ST.StrHelper sXerValue:>Object) );("bFirst",bFirst :>Object)]
    | Decode    ->
        ST.call "xer" "ENUMERATED_item_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sItemID",(if sItemID = null then null else ST.StrHelper sItemID:>Object) );("sXerValue",(if sXerValue = null then null else ST.StrHelper sXerValue:>Object) );("bFirst",bFirst :>Object)]

let ENUMERATED (p:string) (sTag:string) (nLevel:BigInteger) (arrsItems:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "ENUMERATED_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("arrsItems",(arrsItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "xer" "ENUMERATED_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("arrsItems",(arrsItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let REAL (p:string) (sTag:string) (nLevel:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "REAL_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]
    | Decode    ->
        ST.call "xer" "REAL_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]

let IA5String (p:string) (sTag:string) (nLevel:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "IA5String_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]
    | Decode    ->
        ST.call "xer" "IA5String_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]

let ReferenceType (p:string) (sName:string) (sTag:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "ReferenceType_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) )]
    | Decode    ->
        ST.call "xer" "ReferenceType_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) )]

let NULL () codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "NULL_encode" []
    | Decode    ->
        ST.call "xer" "NULL_decode" []

let OctetString (p:string) (sTag:string) (nLevel:BigInteger) (sCount:string) (bIsFixedSize:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "OctetString_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("bIsFixedSize",bIsFixedSize :>Object)]
    | Decode    ->
        ST.call "xer" "OctetString_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("bIsFixedSize",bIsFixedSize :>Object)]

let BitString (p:string) (sTag:string) (nLevel:BigInteger) (sCount:string) (bIsFixedSize:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "BitString_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("bIsFixedSize",bIsFixedSize :>Object)]
    | Decode    ->
        ST.call "xer" "BitString_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("bIsFixedSize",bIsFixedSize :>Object)]

let CHOICE_child (p:string) (sChID:string) (sChildBody:string) (bFirst:bool) (sChildTag:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "CHOICE_child_encode" [("p",p :>Object);("sChID",(if sChID = null then null else ST.StrHelper sChID:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("bFirst",bFirst :>Object);("sChildTag",(if sChildTag = null then null else ST.StrHelper sChildTag:>Object) )]
    | Decode    ->
        ST.call "xer" "CHOICE_child_decode" [("p",p :>Object);("sChID",(if sChID = null then null else ST.StrHelper sChID:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("bFirst",bFirst :>Object);("sChildTag",(if sChildTag = null then null else ST.StrHelper sChildTag:>Object) )]

let CHOICE_no_tag (p:string) (arrsChildren:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "CHOICE_no_tag_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "xer" "CHOICE_no_tag_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let CHOICE (p:string) (sTag:string) (nLevel:BigInteger) (sMainBody:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "CHOICE_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) )]
    | Decode    ->
        ST.call "xer" "CHOICE_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) )]

let SequenceOf (p:string) (sTag:string) (nLevel:BigInteger) (sI:string) (sCount:string) (sChildBody:string) (bFixedSize:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "SequenceOf_encode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sI",(if sI = null then null else ST.StrHelper sI:>Object) );("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("bFixedSize",bFixedSize :>Object)]
    | Decode    ->
        ST.call "xer" "SequenceOf_decode" [("p",p :>Object);("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object);("sI",(if sI = null then null else ST.StrHelper sI:>Object) );("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("bFixedSize",bFixedSize :>Object)]

let Sequence_mandatory_child (sChName:string) (sChildContent:string) (sChildTag:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "Sequence_mandatory_child_encode" [("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sChildTag",(if sChildTag = null then null else ST.StrHelper sChildTag:>Object) )]
    | Decode    ->
        ST.call "xer" "Sequence_mandatory_child_decode" [("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sChildTag",(if sChildTag = null then null else ST.StrHelper sChildTag:>Object) )]

let Sequence_optional_child (p:string) (sChName:string) (sChildContent:string) (sChildTag:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "Sequence_optional_child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sChildTag",(if sChildTag = null then null else ST.StrHelper sChildTag:>Object) )]
    | Decode    ->
        ST.call "xer" "Sequence_optional_child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sChildTag",(if sChildTag = null then null else ST.StrHelper sChildTag:>Object) )]

let SEQUENCE_start (sTag:string) (nLevel:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "SEQUENCE_start_encode" [("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]
    | Decode    ->
        ST.call "xer" "SEQUENCE_start_decode" [("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]

let SEQUENCE_end (sTag:string) (nLevel:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "SEQUENCE_end_encode" [("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]
    | Decode    ->
        ST.call "xer" "SEQUENCE_end_decode" [("sTag",(if sTag = null then null else ST.StrHelper sTag:>Object) );("nLevel",nLevel :>Object)]

let SEQUENCE_xer (sChildren:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "xer" "SEQUENCE_xer_encode" [("sChildren",(if sChildren = null then null else ST.StrHelper sChildren:>Object) )]
    | Decode    ->
        ST.call "xer" "SEQUENCE_xer_decode" [("sChildren",(if sChildren = null then null else ST.StrHelper sChildren:>Object) )]

