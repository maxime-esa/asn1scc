module body_a
open System
open System.Numerics
open Ast

let PrintPackageBody (sPackageName:string) (arrsIncludedModules:seq<string>) (arrsNegativeReals:seq<string>) (arrsBoolPatterns:seq<string>) (arrsTypeAssignments:seq<string>) (arrsChoiceValueAssignments:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "PrintPackageBody" [("sPackageName",(if sPackageName = null then null else ST.StrHelper sPackageName:>Object) );("arrsIncludedModules",(arrsIncludedModules|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsNegativeReals",(arrsNegativeReals|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsBoolPatterns",(arrsBoolPatterns|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsTypeAssignments",(arrsTypeAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsChoiceValueAssignments",(arrsChoiceValueAssignments|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let printTass (soEqualFunc:string option) =
    ST.lang <- Ast.ProgrammingLanguage.Ada
    ST.call "body" "printTass" [("soEqualFunc",(if soEqualFunc.IsNone then null else ST.StrHelper soEqualFunc.Value:>Object) )]

