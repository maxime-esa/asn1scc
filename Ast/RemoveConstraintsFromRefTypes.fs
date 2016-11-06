module RemoveConstraintsFromRefTypes

open FsUtils
open Ast
open System
open CloneTree
open AcnTypes


type NewTas = {
    ModName:string
    TasName:string
    Type:Asn1Type
    originalTypePath:AbsPath
}

type State = {
            //* modName, newRefName, Asn1Type
    //refs : list<string*string*Asn1Type>
    newTases : list<NewTas>
    acn : AcnAstResolved
    Count : int
}


let ApplyAlwaysPresent ast =
    let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<unit>) (state:unit) =
        let CloneChild (parenConstraints:list<Asn1Constraint>) s (ch:ChildInfo) =
            let chooseOptionality = function
                | WithComponentsConstraint(namedItems) -> 
                    match namedItems |> Seq.tryFind(fun ni -> ni.Name.Value = ch.Name.Value) with
                    | Some(item)    -> 
                        match item.Mark with
                        | NoMark        -> ch.Optionality
                        | MarkPresent   -> Some(AlwaysPresent)
                        | MarkAbsent    -> Some(AlwaysAbsent)
                        | MarkOptional  -> ch.Optionality
                    | _             -> None
                | _                                   -> None
            let newOptionality = 
                match parenConstraints |> List.choose chooseOptionality with
                | []    -> ch.Optionality
                | x::xs -> Some x
            let t,ns = cons.cloneType ch.Type m (key@[ch.Name.Value]) cons s
            {ch with Type = t; Optionality = newOptionality},ns
        match old.Kind with
        | Sequence(children)  -> 
            let newChildren, finalState = children |> foldMap (CloneChild old.Constraints) state
            {
                Kind = Sequence(newChildren)
                Constraints = old.Constraints |> List.filter (fun c -> match c with WithComponentsConstraint _ -> false | _ -> true)
                Location = old.Location
                AcnProperties = old.AcnProperties
            }, finalState
        | _             -> defaultConstructors.cloneType old m key cons state


    CloneTree ast {defaultConstructors with cloneType =  CloneType; } () |> fst



let DoWork ast acn =
    let GetAcnProperties (ast:AcnAst) absPath =
        match ast.Types |> List.tryFind(fun x -> x.TypeID = absPath) with
        | Some(acnType)     -> acnType.Properties
        | None              -> []

    let MoveAcnPropsToNewType (ast:AcnAst) oldTypeAbsPath newTypeAbsPath =
        let ChangeTypeID (acnType:AcnType) =
            match acnType.TypeID = oldTypeAbsPath with
            | false -> [acnType]
            | true  -> [{acnType with Properties=[]}; {acnType with TypeID = newTypeAbsPath}]
        {ast with Types = ast.Types |> List.collect ChangeTypeID}

    let CloneType (old:Asn1Type) (m:Ast.Asn1Module) (key:list<string>) (cons:Constructors<State>) (state:State) =
        let moveableLongReference (x:LongReferenceResolved) = match x.Kind with SizeDeterminant | ChoiceDeteterminant -> true | _ ->false
        let acnProps = 
            old.AcnProperties |> 
            List.filter(fun x -> 
                match x with 
                | Aligment _ -> false
                | _          -> true)
        let moveLongRefs = state.acn.References |> List.filter(fun x -> x.decType.AbsPath =  key && moveableLongReference x)
        match old.Kind with
        |ReferenceType(mn,nm, bTab)   when not(Seq.isEmpty old.Constraints)  || not(Seq.isEmpty acnProps) || not(Seq.isEmpty moveLongRefs)  -> 
            let mdName, newRefTypeName = 
                match key with
                | modName::restKey -> modName, (restKey@[state.Count.ToString()]).StrJoin("-")
                | []               -> raise(BugErrorException("Invalid type key"))
            let baseType = GetBaseType old ast
            let typeToReturn = {old with Kind = ReferenceType(m.Name,newRefTypeName.AsLoc, bTab); Constraints=[]; AcnProperties=[]}
            let newType = {baseType with Constraints=(baseType.Constraints @ old.Constraints); AcnProperties=old.AcnProperties}

            let newTas = {NewTas.ModName = m.Name.Value; TasName=newRefTypeName;Type=newType; originalTypePath=key}

            let newState = {state with State.newTases = newTas::state.newTases; Count = state.Count+1; }
            typeToReturn, newState
        | _             -> defaultConstructors.cloneType old m key cons state

    let AcnHouseKeeping (oldAsn1:AstRoot) (acn:AcnAstResolved) (tas:NewTas) : AcnAstResolved =
        let GetParameterNameByReference (r:LongReferenceResolved) =
            match r.Kind with
            | SizeDeterminant      -> "nSize"
            | ChoiceDeteterminant  -> "choiceID"
            | _                    -> raise(BugErrorException "")

        //1 entries in the References table with kind SizeDeterminant and ChoiceDeteterminant should become RefTypeArgument
        let changedRefs = seq {
                            for r in acn.References do
                                if r.decType.AbsPath = tas.originalTypePath then
                                    match r.Kind with
                                    | SizeDeterminant   | ChoiceDeteterminant -> yield {r with Kind = RefTypeArgument (GetParameterNameByReference r) }
                                    | _                                       -> yield r
                                else yield r} |> Seq.toList
        //2 create new Parameters
        let newParams = seq {
                            for r in acn.References do
                                if r.decType.AbsPath = tas.originalTypePath then
                                    match r.Kind with
                                    | SizeDeterminant     -> yield {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = "nSize";    Asn1Type = Integer; Mode=DecodeMode; Location = emptyLocation}
                                    | ChoiceDeteterminant -> 
                                        let targetType = Ast.GetTypeByAbsPath r.determinant.AbsPath oldAsn1
                                        let asn1acnType = match targetType.Kind with
                                                          | ReferenceType(m,t, _) -> RefTypeCon(m,t)
                                                          | _                     -> raise(BugErrorException "")

                                        yield {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = "choiceID"; Asn1Type = asn1acnType; Mode=DecodeMode; Location = emptyLocation}
                                    | _     -> ()
                        } |> Seq.toList
        //3 Add References To Parameters
        let newRefs = seq {
                            for r in acn.References do
                                if r.decType.AbsPath = tas.originalTypePath then
                                    let decType = TypePoint [tas.ModName;tas.TasName]
                                    match r.Kind with
                                    | SizeDeterminant     ->
                                        let determinant = ParamPoint [tas.ModName;tas.TasName; "nSize"]
                                        yield {LongReferenceResolved.decType = decType; determinant=determinant; Kind= r.Kind}
                                    | ChoiceDeteterminant -> 
                                        let determinant = ParamPoint [tas.ModName;tas.TasName; "choiceID"]
                                        yield {LongReferenceResolved.decType = decType; determinant=determinant; Kind= r.Kind}
                                    | _     -> ()
                      } |> Seq.toList
        {acn with Parameters = acn.Parameters@newParams; References = changedRefs@newRefs}
            
    let CloneModule (oldAsn1:AstRoot) (old:Asn1Module) (cons:Constructors<State>) (state:State)  = 
        let thisModuleTases = state.newTases |>List.filter(fun newTas ->  newTas.ModName = old.Name.Value) 
        let restState = {state with newTases = state.newTases |>List.filter(fun newTas -> newTas.ModName <> old.Name.Value) }
        let newTasses = thisModuleTases |> List.map (fun newTas -> {TypeAssignment.Name = newTas.TasName.AsLoc; c_name = ToC2 newTas.TasName; ada_name = ToC2 newTas.TasName; Type = newTas.Type;  Comments = [||]} )
        let newAcn = thisModuleTases |> Seq.fold(fun curAcn tas -> AcnHouseKeeping oldAsn1 curAcn tas) restState.acn
        defaultConstructors.createModule oldAsn1 {old with TypeAssignments = old.TypeAssignments @ newTasses} cons {restState with acn=newAcn  }

    let rec CloneTreeMulti ast (state:State) = 
        let RecursionFinished (s:State) =
            Seq.isEmpty s.newTases
        let rec CopySingleTree ast (state:State) = 
            CloneTree ast {defaultConstructors with cloneType =  CloneType; createModule = CloneModule} state
        let newTree, newState = CopySingleTree ast state
        match  RecursionFinished newState with
        | true -> newTree, newState.acn
        | false  -> CloneTreeMulti newTree newState
    let newAsn1Ast, newAcnAst = CloneTreeMulti ast {State.newTases=[]; Count=1; acn=acn}
    let newAsn1Ast = ApplyAlwaysPresent newAsn1Ast
    newAsn1Ast, newAcnAst


let CheckReferences (asn1:AstRoot) (acn:AcnAstResolved) =
    let CheckPoint  = function
        | TypePoint(p)  ->
            let t = Acn.aux.GetTypeByAbsPath asn1 p
            true
        | ParamPoint(p) ->
            match p with
            | modName::tasName::prmName::[]  ->
                acn.Parameters |> Seq.exists(fun x -> x.ModName=modName && x.TasName=tasName && x.Name=prmName)
            | _   -> 
                Console.WriteLine("invalid parameter {0}", (p.StrJoin "."))
                false
        | TempPoint(p) ->
            match p with
            | modName::tasName::prmName::[]  ->
                acn.TmpTypes |> Seq.exists(fun x -> x.ModName=modName && x.TasName=tasName && x.Name=prmName)
            | _   -> 
                Console.WriteLine("invalid temp point {0}", (p.StrJoin "."))
                false
    let CheckReference (r:LongReferenceResolved) =
        let ret1 = (CheckPoint r.decType) 
        let ret2 = (CheckPoint r.determinant)
        let ret = (CheckPoint r.decType) && (CheckPoint r.determinant)
        if not(ret1) then
            Console.WriteLine(sprintf "1 %A" r)
        if not(ret2) then
            Console.WriteLine(sprintf "2 %A" r)
        ret
    let dummy = acn.References |> List.map(fun x -> CheckReference x)
    dummy |> List.fold (&&) true





