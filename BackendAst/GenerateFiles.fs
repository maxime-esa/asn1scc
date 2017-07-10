module GenerateFiles
open System
open System.Numerics
open System.IO

open FsUtils
open CommonTypes
open DAst
open DAstUtilFunctions


let printValueAssignment (r:DAst.AstRoot) (l:ProgrammingLanguage) (pu:ProgramUnit) (vas:ValueAssignment) =
    let sName = vas.c_name
    let t = vas.Type
    let sTypeDecl= 
        match t.Kind with
        | Integer _
        | Real _
        | Boolean _     -> t.typeDefinition.typeDefinitionBodyWithinSeq
        | _             -> t.typeDefinition.name
    let sVal = DAstVariables.printValue r l pu vas.Type None vas.Value.kind
    match l with
    | C     -> variables_c.PrintValueAssignment sTypeDecl sName sVal
    | Ada   -> header_a.PrintValueAssignment sName sTypeDecl sVal


let rec collectEqualFuncs (t:Asn1Type) =
    seq {
        match t.Kind with
        | Integer          _
        | Real             _
        | IA5String        _
        | OctetString      _
        | NullType         _
        | BitString        _
        | Boolean          _
        | Enumerated       _ -> ()
        | SequenceOf        ch -> 
            yield! collectEqualFuncs ch.childType
        | Sequence        sq ->
            for ch in sq.children do 
                match ch with
                | Asn1Child ch  -> yield! collectEqualFuncs ch.Type
                | AcnChild  _   -> ()
        | Choice          ch ->
            for c in ch.children do 
                yield! collectEqualFuncs c.chType
        | ReferenceType     _   -> ()
        yield t.equalFunction
    } |> Seq.toList

let private printUnit (r:DAst.AstRoot) (l:ProgrammingLanguage) outDir (pu:ProgramUnit) =
    let tases = pu.sortedTypeAssignments
    
    let vases = pu.valueAssignments 
    let arrsAnonymousValues =
        pu.sortedTypeAssignments |>
        List.choose(fun z -> z.Type.isValidFunction) |>
        List.collect (fun z -> z.anonymousVariables)  |>
        Seq.distinctBy(fun z -> z.valueName) |>
        Seq.toList

    //header file
    //let typeDefs = tases |> List.choose(fun t -> t.getTypeDefinition l)
    let typeDefs = 
        tases |> 
        List.map(fun tas -> 
            let type_defintion = tas.Type.typeDefinition.completeDefinition
            let init_def        = tas.Type.initFunction.initFuncDef
            let equal_defs      = collectEqualFuncs tas.Type |> List.choose(fun ef -> ef.isEqualFuncDef)
            let isValid        = 
                match tas.Type.isValidFunction with
                | None      -> None
                | Some f    -> f.funcDef
            let uPerEncFunc = tas.Type.uperEncFunction.funcDef
            let uPerDecFunc = tas.Type.uperDecFunction.funcDef
            let acnEncFunc = match tas.Type.acnEncFunction with None -> None | Some x -> x.funcDef
            let acnDecFunc = match tas.Type.acnDecFunction with None -> None | Some x -> x.funcDef

            let allProcs = equal_defs@([init_def;isValid;uPerEncFunc;uPerDecFunc;acnEncFunc; acnDecFunc] |> List.choose id)
            match l with
            |C     -> header_c.Define_TAS type_defintion allProcs 
            |Ada   -> header_a.Define_TAS type_defintion allProcs 
        )
    let arrsValues = 
        vases |>
        List.map(fun gv -> 
            let t = gv.Type
            match l with
            | C     -> 
                match t.Kind with
                | Integer _
                | Real _
                | Boolean _     -> header_c.PrintValueAssignment (t.typeDefinition.typeDefinitionBodyWithinSeq) gv.c_name
                | _             -> header_c.PrintValueAssignment (t.typeDefinition.name) gv.c_name
            | Ada   -> printValueAssignment r l pu gv)
    let arrsHeaderAnonymousValues =
        arrsAnonymousValues |>
        List.map(fun av -> 
            match l with
            | C     -> header_c.PrintValueAssignment av.typeDefinitionName av.valueName
            | Ada   -> 
                header_a.PrintValueAssignment av.valueName av.typeDefinitionName av.valueExpresion)

    let arrsPrototypes = []
    let defintionsContntent =
        match l with
        | C     -> 
            let arrsUtilityDefines = []
            header_c.PrintHeaderFile pu.name pu.importedProgramUnits typeDefs (arrsValues@arrsHeaderAnonymousValues) arrsPrototypes arrsUtilityDefines
        | Ada   -> 
            let arrsPrivateChoices = []
            header_a.PrintPackageSpec pu.name pu.importedProgramUnits typeDefs (arrsValues@arrsHeaderAnonymousValues) arrsPrivateChoices

    let fileName = Path.Combine(outDir, pu.specFileName)
    File.WriteAllText(fileName, defintionsContntent.Replace("\r",""))
        
    //sourse file
    let arrsTypeAssignments = 
        tases |> List.map(fun t -> 
            let initialize        = t.Type.initFunction.initFunc
            //let eqFuncs = collectEqualDeffinitions t |> List.choose(fun ef -> ef.isEqualFunc)
            let eqFuncs = collectEqualFuncs t.Type |> List.choose(fun ef -> ef.isEqualFunc)
            let isValid = match t.Type.isValidFunction with None -> None | Some isVal -> isVal.func
            let uperEncDec codec         =  
                match codec with
                | CommonTypes.Encode    -> t.Type.uperEncFunction.func
                | CommonTypes.Decode    -> t.Type.uperDecFunction.func
            let ancEncDec codec         = 
                match codec with
                | CommonTypes.Encode    -> match t.Type.acnEncFunction with None -> None | Some x -> x.func
                | CommonTypes.Decode    -> match t.Type.acnDecFunction with None -> None | Some x -> x.func
            let allProcs =  eqFuncs@([initialize; isValid;(uperEncDec CommonTypes.Encode); (uperEncDec CommonTypes.Decode);(ancEncDec CommonTypes.Encode); (ancEncDec CommonTypes.Decode)] |> List.choose id)
            match l with
            | C     ->  body_c.printTass allProcs 
            | Ada   ->  body_a.printTass allProcs )
    let eqContntent = 
        match l with
        | C     ->
            let arrsUnnamedVariables = []
            let arrsValueAssignments = vases |> List.map (printValueAssignment r l pu)
            let arrsSourceAnonymousValues = 
                arrsAnonymousValues |>
                List.map (fun av -> variables_c.PrintValueAssignment av.typeDefinitionName av.valueName av.valueExpresion)
            body_c.printSourceFile pu.name arrsUnnamedVariables (arrsValueAssignments@arrsSourceAnonymousValues) arrsTypeAssignments
        | Ada   ->
            let arrsNegativeReals = []
            let arrsBoolPatterns = []
            let arrsChoiceValueAssignments = []
            let rtl = [body_a.rtlModuleName()]
            body_a.PrintPackageBody pu.name  (rtl@pu.importedProgramUnits) arrsNegativeReals arrsBoolPatterns arrsTypeAssignments arrsChoiceValueAssignments
    let fileName = Path.Combine(outDir, pu.bodyFileName)
    File.WriteAllText(fileName, eqContntent.Replace("\r",""))


let private CreateAdaIndexFile (r:AstRoot) bGenTestCases outDir =
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

let private CreateAdaMain (r:AstRoot) bGenTestCases outDir =
    let content = aux_a.PrintMain (r.programUnits |> List.map(fun x -> (ToC x.name).ToLower()) )
    let outFileName = Path.Combine(outDir, "mainprogram.adb")
    File.WriteAllText(outFileName, content.Replace("\r",""))

let generateAll outDir (r:DAst.AstRoot)   =
    r.programUnits |> Seq.iter (printUnit r r.lang outDir)
    //print extra such make files etc
    //print_debug.DoWork r outDir "debug.txt"
    match r.lang with
    | C    -> ()
    | Ada  -> 
        CreateAdaMain r false outDir
        CreateAdaIndexFile r false outDir

