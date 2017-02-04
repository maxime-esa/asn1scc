module GenerateFiles
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst


let printUnit (r:DAst.AstRoot) (l:BAst.ProgrammingLanguage) outDir (pu:ProgramUnit) =
    let tases = pu.sortedTypeAssignments
    
    //header file
    let typeDefs = tases |> List.choose(fun t -> t.getTypeDefinition l)
    let arrsValues = []
    let arrsPrototypes = []
    let defintionsContntent =
        match l with
        | BAst.C     -> 
            let arrsUtilityDefines = []
            header_c.PrintHeaderFile pu.name.U1 pu.importedProgramUnits typeDefs arrsValues arrsPrototypes arrsUtilityDefines
        | BAst.Ada   -> 
            let arrsPrivateChoices = []
            header_a.PrintPackageSpec pu.name pu.importedProgramUnits typeDefs arrsValues arrsPrivateChoices

    let fileName = Path.Combine(outDir, pu.specFileName)
    File.WriteAllText(fileName, defintionsContntent.Replace("\r",""))
        
    //sourse file
    let arrsTypeAssignments = 
        tases |> List.map(fun t -> 
            let eqFunc = t.isEqualFunc
            match l with
            | BAst.C     ->  body_c.printTass eqFunc
            | BAst.Ada   ->  body_a.printTass eqFunc
        )
    let eqContntent = 
        match l with
        | BAst.C     ->
            let arrsUnnamedVariables = []
            let arrsValueAssignments = []
            body_c.printSourceFile pu.name arrsUnnamedVariables arrsValueAssignments arrsTypeAssignments
        | BAst.Ada   ->
            let arrsNegativeReals = []
            let arrsBoolPatterns = []
            let arrsChoiceValueAssignments = []
            body_a.PrintPackageBody pu.name  pu.importedProgramUnits arrsNegativeReals arrsBoolPatterns arrsTypeAssignments arrsChoiceValueAssignments
    let fileName = Path.Combine(outDir, pu.bodyFileName)
    File.WriteAllText(fileName, eqContntent.Replace("\r",""))

let printDAst (r:DAst.AstRoot) (l:BAst.ProgrammingLanguage) outDir =
    r.programUnits |> Seq.iter (printUnit r l outDir)


