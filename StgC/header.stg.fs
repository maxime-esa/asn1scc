module header_c
open System
open System.Numerics
open Ast

let PrintHeaderFile (sFileNameWithNoExtUpperCase:string) (arrsIncludedModules:seq<string>) (arrsTypeAssignments:seq<string>) (arrsValueAssignments:seq<string>) (arrsPrototypes:seq<string>) (arrsUtilityDefines:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "PrintHeaderFile" [("sFileNameWithNoExtUpperCase",(if sFileNameWithNoExtUpperCase = null then null else ST.StrHelper sFileNameWithNoExtUpperCase:>Object) );("arrsIncludedModules",(arrsIncludedModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsValueAssignments",(arrsValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsPrototypes",(arrsPrototypes|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsUtilityDefines",(arrsUtilityDefines|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Declare_Integer () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_Integer" []

let Declare_PosInteger () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "header" "Declare_PosInteger" []

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

