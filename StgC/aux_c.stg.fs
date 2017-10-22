module aux_c
open System
open System.Numerics
open CommonTypes

let PrintMakeFile (arrsFilesNoExt:seq<string>) =
    ST.lang <- CommonTypes.ProgrammingLanguage.C
    ST.call "aux_c" "PrintMakeFile" [("arrsFilesNoExt",(arrsFilesNoExt|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

