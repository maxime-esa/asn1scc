module DAstProgramUnit
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst



let getTypeDependencies (t:Asn1Type) (us: ReferenceToType list) 
    =
    let add (us: ReferenceToType list) ref = match ref with Some r  -> r::us | None -> us
    DastFold.foldAsn1Type
        t
        us
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun o newBase us -> o.id, add us newBase)
        id
        (fun child o newBase us -> o.id, add us newBase)
        id
        (fun o newChild us -> newChild, us)
        (fun children o newBase us -> o.id, add us newBase)
        id
        (fun o newChild us -> newChild, us)
        (fun children o newBase us -> o.id, add us newBase)
        id
        

let sortTypes (typesToSort: Asn1Type list) (imports :ReferenceToType list) =
    let allNodes = 
        typesToSort |> 
        List.choose( fun tas -> 
            match tas.tasInfo with
            | Some tasInfo  -> Some (getTypeDependencies tas [])
            | None          -> None)
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

let createProgramUnits (files: Asn1File list) (typesMap : Map<ReferenceToType, Asn1Type>) (typeAssignments : Asn1Type list) (valueAssignments  : Asn1GenericValue list) (l:ProgrammingLanguage) =
    match l with
    | C     -> 
        files |>
        List.map(fun f -> 
            let modulesSet = f.Modules |> List.map(fun x -> x.Name) |> Set.ofList
            let fileTypes = typeAssignments |> List.filter(fun x -> modulesSet.Contains x.id.ModName)
            let valueAssignments = valueAssignments |> List.filter(fun x -> modulesSet.Contains x.id.ModName)
            let thisFileModules = f.Modules |> List.map(fun x -> x.Name)
            let importedModules =
                f.Modules |> 
                Seq.collect(fun m -> m.Imports) |>
                Seq.filter(fun m -> not (thisFileModules |> Seq.exists ((=) m.Name.Value) )) |>
                Seq.toList

            let importedProgramUnits =
                importedModules |>
                List.map(fun imp ->
                    let impFile = files |> Seq.find(fun f -> f.Modules |> Seq.exists (fun md -> md.Name = imp.Name.Value) )
                    impFile.FileNameWithoutExtension) |> 
                Seq.distinct |> Seq.toList

            let importedTypes = 
                importedModules |>
                Seq.collect(fun imp -> imp.Types |> List.map (fun impType ->ReferenceToType.createFromAcnAbsPath [imp.Name.Value; impType.Value])) |> 
                Seq.distinct |> Seq.toList

            let soretedTypes = sortTypes fileTypes importedTypes |> List.map(fun ref -> typesMap.[ref])
            let specFileName = f.FileNameWithoutExtension+"."+l.SpecExtention
            let bodyFileName = f.FileNameWithoutExtension+"."+l.BodyExtention
            {ProgramUnit.name = f.FileNameWithoutExtension; specFileName = specFileName; bodyFileName=bodyFileName; sortedTypeAssignments = soretedTypes; valueAssignments = valueAssignments; importedProgramUnits = importedProgramUnits})
    | Ada   -> 
        files |>
        List.collect(fun f -> f.Modules |> List.map (fun m -> f,m)) |>
        List.map(fun (f,m) ->
            let moduTypes = typeAssignments |> List.filter(fun x -> x.id.ModName = m.Name)
            let valueAssignments = valueAssignments |> List.filter(fun x -> x.id.ModName = m.Name)
            let importedTypes = 
                m.Imports |>
                Seq.collect(fun imp -> imp.Types |> List.map (fun impType ->ReferenceToType.createFromAcnAbsPath [imp.Name.Value; impType.Value])) |> 
                Seq.distinct |> Seq.toList        
            let soretedTypes = sortTypes moduTypes importedTypes |> List.map(fun ref -> typesMap.[ref])
            let specFileName = m.Name+"."+l.SpecExtention
            let bodyFileName = m.Name+"."+l.BodyExtention
            let importedProgramUnits = m.Imports |> List.map (fun im -> ToC im.Name.Value)
            {ProgramUnit.name = m.Name; specFileName = specFileName; bodyFileName=bodyFileName; sortedTypeAssignments = soretedTypes; valueAssignments = valueAssignments; importedProgramUnits = importedProgramUnits})


