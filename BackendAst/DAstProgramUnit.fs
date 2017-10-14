module DAstProgramUnit
open System
open System.Numerics
open System.IO

open FsUtils
open CommonTypes

open DAst
open DAstUtilFunctions



let private getTypeDependencies (t:Asn1Type) : (TypeAssignmentInfo list )  
    =
    let prms = t.acnParameters |> List.choose(fun z -> match z.asn1Type with Asn1AcnAst.AcnPrmRefType (mdName,tsName) -> Some ({TypeAssignmentInfo.modName = mdName.Value; tasName = tsName.Value}) | _ -> None )    
    DastFold.foldAsn1Type
        t
        ()
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o newBase us -> prms)
        (fun o sqo child ->  child@prms)
        (fun _ _ ch newChild -> newChild@prms, ())
        (fun _ _ _ _ -> prms, ())
        (fun o sq (children,_) -> (children |> List.collect id)@prms)
        (fun _ _ ch newChild -> newChild@prms, ())
        (fun o ch (children, _) -> (children|> List.collect id)@prms)
        (fun o ref baseType -> (ref.AsTypeAssignmentInfo::baseType)@prms)
        (fun o newKind  -> newKind@prms)


        

let private sortTypes (typesToSort: Asn1Type list) (imports :TypeAssignmentInfo list) =
    let allNodes = 
        typesToSort |> 
        List.choose( fun tas -> 
            match tas.tasInfo with
            | Some tasInfo  -> Some ( (tasInfo, getTypeDependencies tas ))
            | None          -> raise (BugErrorException "All TypeAssignemts must have tasInfo") )
    let independentNodes = allNodes |> List.filter(fun (_,list) -> List.isEmpty list) |> List.map(fun (n,l) -> n)
    let dependentNodes = allNodes |> List.filter(fun (_,list) -> not (List.isEmpty list) )
    let sortedTypeAss = 
        DoTopologicalSort (imports @ independentNodes) dependentNodes 
            (fun c -> 
            SemanticError
                (emptyLocation, 
                 sprintf 
                     "Recursive types are not compatible with embedded systems.\nASN.1 grammar has cyclic dependencies: %A" 
                     c))
    sortedTypeAss

let internal createProgramUnits (files: Asn1File list)  (l:ProgrammingLanguage) =
    match l with
    | C     -> 
        files |>
        List.map(fun f -> 
            let modulesSet = f.Modules |> List.map(fun x -> x.Name.Value) |> Set.ofList
            let fileTases = 
                seq {
                    for m in f.Modules do
                        for tas in m.TypeAssignments do
                            yield (tas.AsTypeAssignmentInfo m.Name.Value, tas)
                } |> Seq.toList
            let fileValueAssignments = f.Modules |> List.collect(fun m -> m.ValueAssignments)
            let tasSet = Map.ofList fileTases
            let fileTypes = fileTases |> List.map snd |> List.map(fun t -> t.Type)
            let valueAssignments = f.Modules |> Seq.collect(fun v -> v.ValueAssignments) 
            let thisFileModules = f.Modules |> List.map(fun x -> x.Name.Value)
            let importedModules =
                f.Modules |> 
                Seq.collect(fun m -> m.Imports) |>
                Seq.filter(fun m -> not (thisFileModules |> Seq.exists ((=) m.Name.Value) )) |>
                Seq.toList

            let importedProgramUnits =
                importedModules |>
                List.map(fun imp ->
                    let impFile = files |> Seq.find(fun f -> f.Modules |> Seq.exists (fun md -> md.Name.Value = imp.Name.Value) )
                    impFile.FileNameWithoutExtension) |> 
                Seq.distinct |> Seq.toList

            let importedTypes = 
                importedModules |>
                Seq.collect(fun imp -> imp.Types |> List.map (fun impType ->{TypeAssignmentInfo.modName = imp.Name.Value; tasName = impType.Value}  )) |> 
                Seq.distinct |> Seq.toList

            let soretedTypes = sortTypes fileTypes importedTypes |> List.map(fun ref -> tasSet.[ref])
            let specFileName = f.FileNameWithoutExtension+"."+l.SpecExtention
            let bodyFileName = f.FileNameWithoutExtension+"."+l.BodyExtention
            {ProgramUnit.name = f.FileNameWithoutExtension; specFileName = specFileName; bodyFileName=bodyFileName; sortedTypeAssignments = soretedTypes; valueAssignments = fileValueAssignments; importedProgramUnits = importedProgramUnits})
    | Ada   -> 

        files |>
        List.collect(fun f -> f.Modules |> List.map (fun m -> f,m)) |>
        List.map(fun (f,m) ->
            let typesMap = m.TypeAssignments |> List.map(fun tas -> tas.AsTypeAssignmentInfo m.Name.Value, tas) |> Map.ofList
            let moduTypes = m.TypeAssignments |> List.map(fun x -> x.Type)
            let valueAssignments = m.ValueAssignments
            let importedTypes = 
                m.Imports |>
                Seq.collect(fun imp -> imp.Types |> List.map (fun impType ->{TypeAssignmentInfo.modName = imp.Name.Value; tasName = impType.Value})) |> 
                Seq.distinct |> Seq.toList        
            let soretedTypes = sortTypes moduTypes importedTypes |> List.map(fun ref -> typesMap.[ref])
            let specFileName = m.Name.Value+"."+l.SpecExtention
            let bodyFileName = m.Name.Value+"."+l.BodyExtention
            let importedProgramUnits = m.Imports |> List.map (fun im -> ToC im.Name.Value)
            {ProgramUnit.name = m.Name.Value; specFileName = specFileName; bodyFileName=bodyFileName; sortedTypeAssignments = soretedTypes; valueAssignments = valueAssignments; importedProgramUnits = importedProgramUnits})


