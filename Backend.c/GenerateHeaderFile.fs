module GenerateHeaderFile

open System.Numerics
open System.IO
open FsUtils
open Ast
open BackendAst



let PrintFile outDir newFileExt (f:DefinitionsFile)  =
    let content = "" //ch.PrintHeaderFile f.fileNameNoExtUpper f.includedModules tases vases protos (EnumUtils@ChoiceUtils)
    let fileName = Path.Combine(outDir, f.fileName)
    File.WriteAllText(fileName, content.Replace("\r",""))
    

let DoWork (files:DefinitionsFile list) outDir newFileExt =
    files |> Seq.iter (PrintFile outDir newFileExt)  
