module body_a
open System
open System.Numerics
open Ast

let PrintMain_testCases (arrsIncludedModules:seq<string>) (arrsTestFunctions:seq<string>) (arrsUsedPackages:seq<string>) (arrsInitCalls:seq<string>) (arrsChoiceVasCalls:seq<string>) (bGenerateDatFile:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintMain_testCases" [("arrsIncludedModules",(arrsIncludedModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTestFunctions",(arrsTestFunctions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsUsedPackages",(arrsUsedPackages|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsInitCalls",(arrsInitCalls|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsChoiceVasCalls",(arrsChoiceVasCalls|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bGenerateDatFile",bGenerateDatFile :>Object)]

let PrintMain_call_codec (sTasName:string) (sModName:string) (sEnc:string) (sValue:string) (sValueAsAsn1:string) (sVasName:string) (bHasValidateFunc:bool) (bGenerateDatFile:bool) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintMain_call_codec" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sEnc",(if sEnc = null then null else ST.StrHelper sEnc:>Object) );("sValue",(if sValue = null then null else ST.StrHelper sValue:>Object) );("sValueAsAsn1",(if sValueAsAsn1 = null then null else ST.StrHelper sValueAsAsn1:>Object) );("sVasName",(if sVasName = null then null else ST.StrHelper sVasName:>Object) );("bHasValidateFunc",bHasValidateFunc :>Object);("bGenerateDatFile",bGenerateDatFile :>Object)]

let PrintMain_call_init (sTasName:string) (sModName:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintMain_call_init" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) )]

let PrintMain_call_choice_valAss (sTasName:string) (sModName:string) (sVasName:string) (sVasModule:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintMain_call_choice_valAss" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sVasName",(if sVasName = null then null else ST.StrHelper sVasName:>Object) );("sVasModule",(if sVasModule = null then null else ST.StrHelper sVasModule:>Object) )]

let PrintLineInIndexFile (sModName:string) (sOutDir:string) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintLineInIndexFile" [("sModName",(if sModName = null then null else ST.StrHelper sModName:>Object) );("sOutDir",(if sOutDir = null then null else ST.StrHelper sOutDir:>Object) )]

let PrintIndexFile (arrsModules:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintIndexFile" [("arrsModules",(arrsModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintMakeFile (arrsModuleList:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintMakeFile" [("arrsModuleList",(arrsModuleList|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

