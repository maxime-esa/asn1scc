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
(*

type private State = {
    curentPath : ScopeNode list
}

type private ASN1_OR_ACN_TYPE =
    | ASN1_TYPE of Asn1Type
    | ACN_TYPE  of AcnInsertedType

let rec private visitType (curentPath : ScopeNode list) (t:Asn1Type) = 
    seq {
        match t.Kind with
        | Integer        _
        | Real           _
        | IA5String      _
        | NumericString  _
        | OctetString    _
        | NullType       _
        | BitString      _
        | Boolean        _
        | Enumerated     _      -> yield (ReferenceToType curentPath, ASN1_TYPE t)
        | SequenceOf   seqOf    ->
            yield (ReferenceToType curentPath, ASN1_TYPE t)
            yield! (visitType (curentPath@[SQF]) seqOf.child )
        | Sequence   seq        ->
            yield (ReferenceToType curentPath, ASN1_TYPE t)
            for a in seq.children do
                match a with
                | Asn1Child ac-> yield! (visitType (curentPath@[SEQ_CHILD ac.Name.Value])  ac.Type)
                | AcnChild ac -> yield (ReferenceToType (curentPath@[SEQ_CHILD ac.Name.Value]), ACN_TYPE ac.Type)
        | Choice ch ->
            yield (ReferenceToType curentPath, ASN1_TYPE t)
            for a in ch.children do
                yield! (visitType (curentPath@[CH_CHILD a.Name.Value])  a.Type)
        | ReferenceType ref -> yield! visitType curentPath ref.baseType
    } |> Seq.toList
*)

let private checkRelativePath (parents: Asn1Type list) (visibleParameters:AcnParameter list) (RelativePath path : RelativePath) checkParameter checkAcnType =
    match path with
    | []        -> raise (BugErrorException("Invalid Argument"))
    | x1::[]    ->
        match visibleParameters |> Seq.tryFind(fun p -> p.name = x1.Value) with
        | Some  p   -> 
            //x1 is a parameter
            checkParameter p
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
                        | AcnChild ch  -> checkAcnType ch
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
                        | AcnChild ch  -> checkAcnType ch
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
        | Some p -> checkSeqWithPath p path

let sizeReference (parents: Asn1Type list) (visibleParameters:AcnParameter list)  (rp :RelativePath  option) =
    match rp with
    | None      -> ()
    | Some (RelativePath path) -> 
        let loc = path.Head.Location
        let checkParameter (p:AcnParameter) = 
            match p.asn1Type with
            | AcnPrmInteger _ -> ()
            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (p.asn1Type.ToString()))))
        let rec checkAcnType (c:AcnChild) =
            match c.Type with
            | AcnInteger    _ -> ()
            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (c.Type.AsString))))
        checkRelativePath parents visibleParameters   (RelativePath path) checkParameter checkAcnType

let rec private checkType (parents: Asn1Type list) (curentPath : ScopeNode list) (t:Asn1Type) = 
    //the visible parameters of a type are this type parameters if type has parameters or the 
    //next parent with parameters
    let visibleParameters = 
        match parents@[t] |> List.rev |> List.filter(fun x -> not x.acnParameters.IsEmpty) with
        | []    -> []
        | p1::_ -> p1.acnParameters
    match t.Kind with
    | Integer        _
    | Real           _
    | IA5String      _
    | NumericString  _
    | NullType       _
    | Boolean        _
    | Enumerated     _      -> ()
    | OctetString    a      -> sizeReference parents visibleParameters a.acnProperties.sizeProp
    | BitString      a      -> sizeReference parents visibleParameters a.acnProperties.sizeProp
    | SequenceOf   seqOf    ->
        sizeReference (parents@[t]) visibleParameters seqOf.acnProperties.sizeProp
        checkType (parents@[t]) (curentPath@[SQF]) seqOf.child 
    | Sequence   seq        ->
        for a in seq.children do
            match a with
            | Asn1Child ac-> 
                match ac.Optionality with
                | Some (Optional opt)   -> 
                    match opt.acnPresentWhen with
                    | None  -> ()
                    | Some   (PresenceWhenBool (RelativePath path)) ->
                        let loc = path.Head.Location
                        let checkParameter (p:AcnParameter) = 
                            match p.asn1Type with
                            | AcnPrmBoolean _ -> ()
                            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting BOOLEAN got %s "  (p.asn1Type.ToString()))))
                        let rec checkAcnType (c:AcnChild) =
                            match c.Type with
                            | AcnBoolean    _ -> ()
                            | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting BOOLEAN got %s "  (c.Type.AsString))))
                        checkRelativePath (parents@[t]) visibleParameters   (RelativePath path) checkParameter checkAcnType
                | _                     -> ()
                checkType (parents@[t]) (curentPath@[SEQ_CHILD ac.Name.Value])  ac.Type
            | AcnChild ac -> ()
    | Choice ch ->
        for a in ch.children do
            let checkAcnPresentWhenConditionChoiceChild (a:AcnPresentWhenConditionChoiceChild) =
                match a with
                | PresenceInt   ((RelativePath path),_) -> 
                    let loc = path.Head.Location
                    let checkParameter (p:AcnParameter) = 
                        match p.asn1Type with
                        | AcnPrmInteger _ -> ()
                        | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (p.asn1Type.ToString()))))
                    let rec checkAcnType (c:AcnChild) =
                        match c.Type with
                        | AcnInteger    _ -> ()
                        | _              -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting INTEGER got %s "  (c.Type.AsString))))
                    checkRelativePath (parents@[t]) visibleParameters   (RelativePath path) checkParameter checkAcnType
                | PresenceStr   ((RelativePath path),_ )-> ()
            a.acnPresentWhenConditions |> List.iter checkAcnPresentWhenConditionChoiceChild
            checkType (parents@[t]) (curentPath@[CH_CHILD a.Name.Value])  a.Type
    | ReferenceType ref -> 
        let checkArgument ((RelativePath path : RelativePath), (prm:AcnParameter)) =
            let loc = path.Head.Location
            let checkParameter (p:AcnParameter) = 
                match p.asn1Type = prm.asn1Type with
                | true  -> ()
                | false -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting %s got %s " (prm.asn1Type.ToString()) (p.asn1Type.ToString()))))
            let rec checkAcnType (c:AcnChild) =
                match c.Type, prm.asn1Type with
                | AcnInteger    _, AcnPrmInteger _   -> ()
                | AcnNullType   _, AcnPrmNullType _  -> ()
                | AcnBoolean    _, AcnPrmBoolean _   -> ()
                | _             , AcnPrmRefType (md,ts)    -> ()    //WARNING NOT CHECKED
                | _                                  -> raise(SemanticError(loc, (sprintf "Invalid argument type. Expecting %s got %s " (prm.asn1Type.ToString()) (c.Type.AsString))))
            checkRelativePath parents visibleParameters   (RelativePath path) checkParameter checkAcnType

        match ref.acnArguments.Length = ref.baseType.acnParameters.Length with
        | true  -> ()
        | false -> raise(SemanticError(t.Location, (sprintf "Expecting %d arguments, provide %d" ref.acnArguments.Length ref.baseType.acnParameters.Length)))
        let ziped = List.zip ref.acnArguments ref.baseType.acnParameters
        ziped |> List.iter checkArgument
        checkType parents curentPath ref.baseType


let checkAst (r:AstRoot) =
(*
    let typesMap = 
        seq {
            for f in r.Files do
                for m in f.Modules do
                    for tas in m.TypeAssignments do
                        yield! (visitType [MD m.Name.Value; TA tas.Name.Value] tas.Type)
        } |> Map.ofSeq
*)
    for f in r.Files do
        for m in f.Modules do
            for tas in m.TypeAssignments do
                checkType [] [MD m.Name.Value; TA tas.Name.Value] tas.Type

