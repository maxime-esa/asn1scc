module CheckLongReferences


open System
open System.Numerics
open System.IO
open System.Xml.Linq
open FsUtils
open CommonTypes
open Asn1AcnAst
open Asn1Fold
open Asn1AcnAstUtilFunctions



let private addParameter (cur:AcnInsertedFieldDependencies) (asn1Type:Asn1Type) (p:AcnParameter) (d:AcnDependencyKind) =
    {cur with acnDependencies = {AcnDependency.asn1Type = asn1Type.id; determinant = p.id; dependencyKind = d}::cur.acnDependencies }

let private addAcnChild (cur:AcnInsertedFieldDependencies) (asn1Type:Asn1Type) (acnRefId:ReferenceToType) (d:AcnDependencyKind) =
    {cur with acnDependencies = {AcnDependency.asn1Type = asn1Type.id; determinant = acnRefId; dependencyKind = d}::cur.acnDependencies }

let private checkRelativePath (curState:AcnInsertedFieldDependencies) (parents: Asn1Type list) (asn1TypeWithDependency:Asn1Type ) (visibleParameters:(ReferenceToType*AcnParameter) list) (RelativePath path : RelativePath) checkParameter checkAcnType =
    match path with
    | []        -> raise (BugErrorException("Invalid Argument"))
    | x1::[]    ->
        match visibleParameters |> Seq.tryFind(fun (ref, p) -> p.name = x1.Value) with
        | Some  (rf,p)   -> 
            //x1 is a parameter
            let d = checkParameter p
            addParameter curState asn1TypeWithDependency p d
        | None      -> 
            //x1 is silbing child
            match parents |> List.rev with
            | []    -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" x1.Value)))
            | parent::_ ->
                match parent.Kind with
                | Sequence seq ->
                    match seq.children |> Seq.tryFind(fun (c:SeqChildInfo) -> c.Name = x1) with
                    | Some ch   -> 
                        match ch with
                        | Asn1Child ch  -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s' to ASN.1 type. ACN references must point to ACN inserted types or parameters" x1.Value)))
                        | AcnChild ch  -> 
                            let d = checkAcnType ch
                            addAcnChild curState asn1TypeWithDependency ch.id d
                    | None      -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" x1.Value)))
                | _                 -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" x1.Value)))
    | x1::_  -> 
            //x1 may be a silbing child or a child to one of my parents
            // so, find the first parent that has a child x1

        let parSeq = 
            let rec findSeq p =
                match p.Kind with
                | Sequence seq      -> seq.children |> Seq.exists(fun c -> c.Name = x1) 
                | ReferenceType ref ->findSeq ref.baseType
                | _            -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" (path |> Seq.StrJoin "."))))
            parents |> List.rev |>  Seq.tryFind findSeq
        let rec checkSeqWithPath (seq:Asn1Type) (path : StringLoc list)=   
            match seq.Kind with
            | Sequence seq -> 
                match path with
                | []       -> raise(BugErrorException "111")
                | x1::[]   ->
                    match seq.children |> Seq.tryFind(fun c -> c.Name = x1) with
                    | None -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" (path |> Seq.StrJoin "."))))
                    | Some ch -> 
                        match ch with
                        | Asn1Child ch  -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s' to ASN.1 type. ACN references must point to ACN inserted types or parameters" x1.Value)))
                        | AcnChild ch  -> 
                            let d = checkAcnType ch
                            addAcnChild curState asn1TypeWithDependency ch.id d
                | x1::xs     ->
                    match seq.children |> Seq.tryFind(fun c -> c.Name = x1) with
                    | None -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" (path |> Seq.StrJoin "."))))
                    | Some ch -> 
                        match ch with
                        | Asn1Child ch -> checkSeqWithPath ch.Type xs
                        | _            -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" (path |> Seq.StrJoin "."))))
            | ReferenceType ref -> checkSeqWithPath ref.baseType path
            | _            -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" (path |> Seq.StrJoin "."))))

        match parSeq with
        | None  -> raise(SemanticError(x1.Location, (sprintf "Invalid reference '%s'" (path |> Seq.StrJoin "."))))
        | Some p -> 
            checkSeqWithPath p path

let sizeReference (curState:AcnInsertedFieldDependencies) (parents: Asn1Type list) (t:Asn1Type) (visibleParameters:(ReferenceToType*AcnParameter) list)  (rp :RelativePath  option) (d:AcnDependencyKind) =
    match rp with
    | None      -> curState
    | Some (RelativePath path) -> 
        let loc = path.Head.Location
        let checkParameter (p:AcnParameter) = 
            match p.asn1Type with
            | AcnPrmInteger _ -> d
            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (p.asn1Type.ToString()))))
        let checkAcnType (c:AcnChild) =
            match c.Type with
            | AcnInteger    _ -> d
            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (c.Type.AsString))))
        checkRelativePath curState parents t visibleParameters   (RelativePath path) checkParameter checkAcnType

let choiceEnumReference (r:AstRoot) (curState:AcnInsertedFieldDependencies) (parents: Asn1Type list) (t:Asn1Type) (children  : ChChildInfo list) (visibleParameters:(ReferenceToType*AcnParameter) list)  (rp :RelativePath  option)  =
    let checkEnumNamesConsistency loc (nmItems:NamedItem list) =
        match children.Length <> nmItems.Length with
        | true  -> raise(SemanticError(loc, (sprintf "Enum determinant items do not match with choice alternative names " )))
        | false ->
            let allNamesMatch = List.zip (children |> List.map(fun z -> z.Name.Value)) (nmItems |> List.map(fun z -> z.Name.Value)) |> Seq.forall(fun (x1,x2) -> x1 = x2)
            match allNamesMatch with
            | true  -> ()
            | false -> raise(SemanticError(loc, (sprintf "Enum determinant items do not match with choice alternative names " )))

    match rp with
    | None      -> curState
    | Some (RelativePath path) -> 
        let loc = path.Head.Location
        let checkParameter (p:AcnParameter) = 
            match p.asn1Type with
            | AcnPrmRefType (md,ts) -> 
                let actType = GetActualTypeByName r md ts 
                match actType.Kind with
                | Enumerated enm  -> 
                    checkEnumNamesConsistency ts.Location enm.items
                    AcnDepChoiceDeteterminant enm
                | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting ENUMERATED got %s "  (p.asn1Type.ToString()))))
            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting ENUMERATED got %s "  (p.asn1Type.ToString()))))
        let checkAcnType (c:AcnChild) =
            match c.Type with
            | AcnReferenceToEnumerated    enm -> 
                checkEnumNamesConsistency c.Name.Location enm.enumerated.items
                AcnDepChoiceDeteterminant enm.enumerated
            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting ENUMERATED got %s "  (c.Type.AsString))))
        checkRelativePath curState parents t visibleParameters   (RelativePath path) checkParameter checkAcnType

let rec private checkType (r:AstRoot) (parents: Asn1Type list) (curentPath : ScopeNode list) (t:Asn1Type) (curState:AcnInsertedFieldDependencies) = 
    //the visible parameters of a type are this type parameters if type has parameters or the 
    //next parent with parameters
    let visibleParameters = 
        match parents@[t] |> List.rev |> List.filter(fun x -> not x.acnParameters.IsEmpty) with
        | []    -> []
        | p1::_ -> p1.acnParameters |> List.map(fun p -> (p1.id, p))
    match t.Kind with
    | Integer        _
    | Real           _
    | NullType       _
    | Boolean        _
    | Enumerated     _      -> curState
    | IA5String      a
    | NumericString  a      ->
        match a.acnProperties.sizeProp with
        | Some (StrExternalField   relPath)    ->
            sizeReference curState parents t visibleParameters (Some relPath) AcnDepSizeDeterminant
        | _          -> curState
    | OctetString    a      -> 
        sizeReference curState parents t visibleParameters a.acnProperties.sizeProp AcnDepSizeDeterminant
    | BitString      a      -> 
        sizeReference curState parents t visibleParameters a.acnProperties.sizeProp AcnDepSizeDeterminant
    | SequenceOf   seqOf    ->
        let ns = sizeReference curState (parents@[t]) t visibleParameters seqOf.acnProperties.sizeProp AcnDepSizeDeterminant
        checkType r (parents@[t]) (curentPath@[SQF]) seqOf.child ns
    | Sequence   seq        ->
        seq.children |>
        List.choose (fun c -> match c with Asn1Child ac -> Some ac | AcnChild _ -> None) |>
        List.fold (fun ns ac -> 
            let ns1 = 
                match ac.Optionality with
                | Some (Optional opt)   -> 
                    match opt.acnPresentWhen with
                    | None  -> ns
                    | Some   (PresenceWhenBool (RelativePath path)) ->
                        let loc = path.Head.Location
                        let checkParameter (p:AcnParameter) = 
                            match p.asn1Type with
                            | AcnPrmBoolean _ -> AcnDepPresenceBool
                            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting BOOLEAN got %s "  (p.asn1Type.ToString()))))
                        let rec checkAcnType (c:AcnChild) =
                            match c.Type with
                            | AcnBoolean    _ -> AcnDepPresenceBool
                            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting BOOLEAN got %s "  (c.Type.AsString))))
                        checkRelativePath ns parents ac.Type visibleParameters   (RelativePath path)  checkParameter checkAcnType 
                | _                     -> ns
            checkType r (parents@[t]) (curentPath@[SEQ_CHILD ac.Name.Value])  ac.Type ns1
        ) curState
    | Choice ch ->
        let ns = choiceEnumReference r curState (parents@[t]) t ch.children visibleParameters ch.acnProperties.enumDeterminant
        ch.children |>
        List.fold (fun ns ch -> 
            let checkAcnPresentWhenConditionChoiceChild (curState:AcnInsertedFieldDependencies) (a:AcnPresentWhenConditionChoiceChild) =
                match a with
                | PresenceInt   ((RelativePath path),intVal) -> 
                    let loc = path.Head.Location
                    let checkParameter (p:AcnParameter) = 
                        match p.asn1Type with
                        | AcnPrmInteger _ -> AcnDepPresenceInt intVal.Value
                        | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (p.asn1Type.ToString()))))
                    let rec checkAcnType (c:AcnChild) =
                        match c.Type with
                        | AcnInteger    _ -> AcnDepPresenceInt intVal.Value
                        | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (c.Type.AsString))))
                    checkRelativePath curState parents t visibleParameters   (RelativePath path)  checkParameter checkAcnType
                | PresenceStr   ((RelativePath path), strVal)-> 
                    let loc = path.Head.Location
                    let checkParameter (p:AcnParameter) = 
                        match p.asn1Type with
                        | AcnPrmRefType _ -> AcnDepPresenceStr strVal.Value
                        | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting STRING got %s "  (p.asn1Type.ToString()))))
                    let rec checkAcnType (c:AcnChild) =
                        match c.Type with
                        | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting STRING got %s "  (c.Type.AsString))))
                    checkRelativePath curState parents ch.Type visibleParameters   (RelativePath path)  checkParameter checkAcnType
            
            let ns1 = ch.acnPresentWhenConditions |> List.fold (fun ns x -> checkAcnPresentWhenConditionChoiceChild ns x) ns
            checkType r (parents@[t]) (curentPath@[CH_CHILD ch.Name.Value])  ch.Type ns1) ns
    | ReferenceType ref -> 
        let checkArgument (curState:AcnInsertedFieldDependencies) ((RelativePath path : RelativePath), (prm:AcnParameter)) =
            let loc = path.Head.Location
            let checkParameter (p:AcnParameter) = 
                match p.asn1Type = prm.asn1Type with
                | true  -> AcnDepRefTypeArgument prm
                | false -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting %s got %s " (prm.asn1Type.ToString()) (p.asn1Type.ToString()))))
            let rec checkAcnType (c:AcnChild) =
                match c.Type, prm.asn1Type with
                | AcnInteger    _, AcnPrmInteger _   -> AcnDepRefTypeArgument prm
                | AcnNullType   _, AcnPrmNullType _  -> AcnDepRefTypeArgument prm
                | AcnBoolean    _, AcnPrmBoolean _   -> AcnDepRefTypeArgument prm
                | _             , AcnPrmRefType (md,ts)    -> AcnDepRefTypeArgument prm    //WARNING NOT CHECKED
                | _                                  -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting %s got %s " (prm.asn1Type.ToString()) (c.Type.AsString))))
            checkRelativePath curState parents t visibleParameters   (RelativePath path)  checkParameter checkAcnType

        match ref.acnArguments.Length = ref.baseType.acnParameters.Length with
        | true  -> ()
        | false -> raise(SemanticError(t.Location, (sprintf "Expecting %d arguments, provide %d" ref.acnArguments.Length ref.baseType.acnParameters.Length)))
        let ziped = List.zip ref.acnArguments ref.baseType.acnParameters
        let ns = ziped |> List.fold(fun s c -> checkArgument s c) curState
        checkType r parents curentPath ref.baseType ns


let checkAst (r:AstRoot) =
    let emptyState = {AcnInsertedFieldDependencies.acnDependencies=[]}

    r.Files |>
        List.collect (fun f -> f.Modules) |>
        List.map (fun m -> m.TypeAssignments |> List.map(fun tas -> (m,tas)) ) |>
        List.collect id |>
        List.fold (fun ns (m,tas) -> checkType r [] [MD m.Name.Value; TA tas.Name.Value] tas.Type ns) emptyState


