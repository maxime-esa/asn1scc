module GenerateFiles
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst


let printUnit (r:DAst.AstRoot) (l:ProgrammingLanguage) outDir (programUnit:ProgramUnit) =
    let tases = programUnit.sortedTypeAssignments
    
    //header file
    let typeDefs = tases |> List.choose(fun t -> t.getTypeDefinition l)
    let defintionsContntent = ""
    //    match l with
     //   | C -> c_

    let fileName = Path.Combine(outDir, programUnit.specFileName)
    File.WriteAllText(fileName, defintionsContntent.Replace("\r",""))
        
    //sourse file
    let eqFuncs = tases |> List.choose(fun t -> t.isEqualFunc)
    let eqContntent = eqFuncs |> Seq.StrJoin "\n"
    let fileName = Path.Combine(outDir, programUnit.bodyFileName)
    File.WriteAllText(fileName, eqContntent.Replace("\r",""))

let printDAst (r:DAst.AstRoot) (l:ProgrammingLanguage) outDir =
    r.programUnits |> Seq.iter (printUnit r l outDir)


