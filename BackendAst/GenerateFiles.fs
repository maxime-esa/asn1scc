module GenerateFiles
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst



let printValueAssignment (r:DAst.AstRoot) (l:ProgrammingLanguage) (pu:ProgramUnit) (v:Asn1GenericValue) =
    let sName = v.getBackendName l
    let t = getValueType r v
    let sTypeDecl= t.typeDefinition.name
    let sVal = DAstVariables.printValue r l pu v
    match l with
    | C     ->variables_c.PrintValueAssignment sTypeDecl sName sVal
    | Ada   -> header_a.PrintValueAssignment sName sTypeDecl sVal


type CollectTypeKindAux = CT_REFTYPE | CT_NOREFTYPE
let collectEqualDeffinitions (t:Asn1Type)  =
    DastFold.foldAsn1Type2
        t
        0
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun o bs us -> match o.baseTypeEquivalence.typeDefinition with Some _ ->(CT_REFTYPE,[o.equalFunction]), us | None -> (CT_NOREFTYPE,[o.equalFunction]), us )
        (fun (refType, childDefs) o bs us ->
            let childCollects = match refType with CT_REFTYPE -> [] | CT_NOREFTYPE -> childDefs 
            match o.baseTypeEquivalence.typeDefinition with Some _ -> (CT_REFTYPE,childCollects@[o.equalFunction]), us | None -> (CT_NOREFTYPE,childCollects@[o.equalFunction]),us)
        //sequence
        (fun o (refType, childDefs) us -> match refType with CT_REFTYPE -> [],us | CT_NOREFTYPE -> childDefs , us)
        (fun children o bs us -> 
            let childrenCollects = children |> List.collect id
            match o.baseTypeEquivalence.typeDefinition with Some _ -> (CT_REFTYPE,childrenCollects@[o.equalFunction]), us | None -> (CT_NOREFTYPE,childrenCollects@[o.equalFunction]), us )
        //Choice
        (fun o (refType, childDefs) us -> match refType with CT_REFTYPE -> [],us | CT_NOREFTYPE -> childDefs , us)
        (fun children o bs us -> 
            let childrenCollects = children |> List.collect id
            match o.baseTypeEquivalence.typeDefinition with Some _ -> (CT_REFTYPE,childrenCollects@[o.equalFunction]), us | None -> (CT_NOREFTYPE,childrenCollects@[o.equalFunction]), us )
    |> fst |> snd

let printUnit (r:DAst.AstRoot) (l:ProgrammingLanguage) outDir (pu:ProgramUnit) =
    let tases = pu.sortedTypeAssignments
    
    let vases =
        pu.valueAssignments |>
        List.filter(fun x -> not x.childValue) |>
        List.filter(fun x -> x.isVAS || not (x.isLiteral l))

    //header file
    //let typeDefs = tases |> List.choose(fun t -> t.getTypeDefinition l)
    let typeDefs = 
        tases |> 
        List.map(fun t -> 
            let type_defintion = t.typeDefinition.completeDefinition
            let equal_defs      = collectEqualDeffinitions t |> List.choose(fun ef -> ef.isEqualFuncDef)
            let init_def        = t.initFunction.initFuncDef
            let isValid        = 
                match t.isValidFunction with
                | None      -> None
                | Some f    -> f.funcDef
            let uPerEncFunc = match t.uperEncFunction with None -> None | Some x -> x.funcDef
            let uPerDecFunc = match t.uperDecFunction with None -> None | Some x -> x.funcDef
            let ancEncDec codec         = 
                match t.acnFunction with
                | None    -> None
                | Some a  -> a.funcDef codec
            let allProcs = equal_defs@([(*init_def;*) isValid;uPerEncFunc;uPerDecFunc;(ancEncDec Ast.Encode); (ancEncDec Ast.Decode)] |> List.choose id)
            match l with
            |C     -> header_c.Define_TAS type_defintion allProcs 
            |Ada   -> header_a.Define_TAS type_defintion allProcs 
        )
    let arrsValues = 
        vases |>
        List.map(fun gv -> 
            let t = getValueType r gv
            match l with
            | C     -> header_c.PrintValueAssignment (t.typeDefinition.name) (gv.getBackendName l)
            | Ada   -> printValueAssignment r l pu gv)
    let arrsPrototypes = []
    let defintionsContntent =
        match l with
        | C     -> 
            let arrsUtilityDefines = []
            header_c.PrintHeaderFile pu.name.U1 pu.importedProgramUnits typeDefs arrsValues arrsPrototypes arrsUtilityDefines
        | Ada   -> 
            let arrsPrivateChoices = []
            header_a.PrintPackageSpec pu.name pu.importedProgramUnits typeDefs arrsValues arrsPrivateChoices

    let fileName = Path.Combine(outDir, pu.specFileName)
    File.WriteAllText(fileName, defintionsContntent.Replace("\r",""))
        
    //sourse file
    let arrsTypeAssignments = 
        tases |> List.map(fun t -> 
            let eqFuncs = collectEqualDeffinitions t |> List.choose(fun ef -> ef.isEqualFunc)

            let initialize        = t.initFunction.initFunc
            let isValid = match t.isValidFunction with None -> None | Some isVal -> isVal.func

            let uperEncDec codec         =  
                match codec with
                | Ast.Encode    -> match t.uperEncFunction with None -> None | Some x -> x.func
                | Ast.Decode    -> match t.uperDecFunction with None -> None | Some x -> x.func

            let ancEncDec codec         = 
                match t.acnFunction with
                | None    -> None
                | Some a  -> a.func codec
            let allProcs = eqFuncs@([(*initialize;*) isValid;(uperEncDec Ast.Encode); (uperEncDec Ast.Decode);(ancEncDec Ast.Encode); (ancEncDec Ast.Decode)] |> List.choose id)
            match l with
            | C     ->  body_c.printTass allProcs 
            | Ada   ->  body_a.printTass allProcs )
    let eqContntent = 
        match l with
        | C     ->
            let arrsUnnamedVariables = []
            let arrsValueAssignments = vases |> List.map (printValueAssignment r l pu)
            body_c.printSourceFile pu.name arrsUnnamedVariables arrsValueAssignments arrsTypeAssignments
        | Ada   ->
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

let printDAst (r:DAst.AstRoot) (l:ProgrammingLanguage) outDir =
    r.programUnits |> Seq.iter (printUnit r l outDir)
    //print extra such make files etc
    print_debug.DoWork r outDir "debug.txt"
    match l with
    | C    -> ()
    | Ada  -> 
        CreateAdaMain r false outDir
        CreateAdaIndexFile r false outDir

