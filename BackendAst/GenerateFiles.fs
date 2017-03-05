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
    //let typeDefs = tases |> List.choose(fun t -> t.getTypeDefinition l)
    let typeDefs = 
        tases |> 
        List.map(fun t -> 
            let type_defintion = t.typeDefinition.completeDefinition
            let equal_def      = t.equalFunction.isEqualFuncDef
            match l with
            |BAst.C     -> header_c.Define_TAS type_defintion equal_def
            |BAst.Ada   -> header_a.Define_TAS type_defintion equal_def
        )
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
            let eqFunc = t.equalFunction.isEqualFunc
            match l with
            | BAst.C     ->  body_c.printTass eqFunc
            | BAst.Ada   ->  
                let choiceGettersBody = []
                body_a.printTass choiceGettersBody eqFunc
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
            let rtl = [body_a.rtlModuleName()]
            body_a.PrintPackageBody pu.name  (rtl@pu.importedProgramUnits) arrsNegativeReals arrsBoolPatterns arrsTypeAssignments arrsChoiceValueAssignments
    let fileName = Path.Combine(outDir, pu.bodyFileName)
    File.WriteAllText(fileName, eqContntent.Replace("\r",""))


let CreateAdaIndexFile (r:AstRoot) bGenTestCases outDir =
    let mods = r.programUnits |> Seq.map(fun x -> (ToC x.name).ToLower()) |>Seq.toList
    //let mds = match bGenTestCases with
    //            | true  -> mods @ (modules |> Seq.filter(fun x -> ModuleHasAutoCodecs x r) |> Seq.map(fun x -> (ToC x.Name.Value+"_auto_encs_decs").ToLower() ) |>Seq.toList)
    //            | false -> mods
    let mds = mods
    let fullPath = (System.IO.Path.GetFullPath outDir) + System.String(System.IO.Path.DirectorySeparatorChar,1)
    let lines = (header_a.rtlModuleName())::mds |> List.map(fun x -> aux_a.PrintLineInIndexFile x fullPath)
    let content = match bGenTestCases with
                    | true    -> aux_a.PrintIndexFile ("mainprogram    main_program  is in MainProgram.adb"::lines)
                    | false   -> aux_a.PrintIndexFile lines
    let outFileName = Path.Combine(outDir, "spark.idx")
    File.WriteAllText(outFileName, content.Replace("\r",""))

let CreateAdaMain (r:AstRoot) bGenTestCases outDir =
    let content = aux_a.PrintMain (r.programUnits |> List.map(fun x -> (ToC x.name).ToLower()) )
    let outFileName = Path.Combine(outDir, "mainprogram.adb")
    File.WriteAllText(outFileName, content.Replace("\r",""))

let printDAst (r:DAst.AstRoot) (l:BAst.ProgrammingLanguage) outDir =
    r.programUnits |> Seq.iter (printUnit r l outDir)
    //print extra such make files etc
    match l with
    | BAst.C    -> ()
    | BAst.Ada  -> 
        CreateAdaMain r false outDir
        CreateAdaIndexFile r false outDir

