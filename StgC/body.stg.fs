module body_c
open System
open System.Numerics
open Ast

let printSourceFile (sFileNameWithoutExtension:string) (arrsUnnamedVariables:seq<string>) (arrsValueAssignments:seq<string>) (arrsTypeAssignments:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "body" "printSourceFile" [("sFileNameWithoutExtension",(if sFileNameWithoutExtension = null then null else ST.StrHelper sFileNameWithoutExtension:>Object) );("arrsUnnamedVariables",(arrsUnnamedVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsValueAssignments",(arrsValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let printTass (soEqualFunc:string option) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "body" "printTass" [("soEqualFunc",(if soEqualFunc.IsNone then null else ST.StrHelper soEqualFunc.Value:>Object) )]

