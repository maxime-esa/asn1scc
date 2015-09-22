module ReplaceInnerTypes

open FsUtils
open AcnTypes
open Ast
open System
open CloneTree
open VisitTree

                //ModuleName*RefTypeName*Asn1Type

type NewTas = {
    ModName:string
    TasName:string
    Type:Asn1Type
    originalTypePath:AbsPath
}

type State = {
    newTases : list<NewTas>
    acn : AcnAstResolved
}

//type State = list<string*string*Asn1Type>

let CloneTypePriv (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) (icdGenerator:bool) =
    let ShouldTabularized (t:Asn1Type) =
        match t.Kind with
        | Sequence(_) | Choice(_) | SequenceOf(_)       -> true
        | Enumerated(_) -> if icdGenerator then false else true 
        | IA5String | NumericString | OctetString | BitString(_)        -> if icdGenerator then false else true 
        | Integer | Real |  Boolean                                     -> 
            match icdGenerator with
            | true  -> false
            | false -> if (Seq.isEmpty t.Constraints) then false else true
        | ReferenceType(_)  | NullType                                  -> false
    let MakeRefType (modName:string) (refName:string) =
        { Asn1Type.Kind = ReferenceType( modName.AsLoc, refName.AsLoc, true); Constraints=[]; Location = emptyLocation; AcnProperties=[] }
    let HandleChildType (s:State) child varName =
        let chKey = key @ [varName]
        match ShouldTabularized child with
        | false -> cons.cloneType child m chKey cons s
        | true  -> 
            let modName, newRefName = match chKey with 
                                      |modNam::restPath -> modNam, (restPath.StrJoin "-").Replace("#","elm")
                                      |[]               -> raise(BugErrorException("Invalid type path"))
            let retState = {state with newTases = {NewTas.ModName = modName; TasName = newRefName; Type=child; originalTypePath= chKey}::s.newTases}
            MakeRefType modName newRefName, retState        
    let CloneChild (s:State) (ch:ChildInfo) =
        let t,ns = HandleChildType s ch.Type ch.Name.Value
        {ch with Type = t},ns
    let newKind, newState = 
        match old.Kind with
        | Sequence(children)  -> 
            let newChildren, finalState = children |> foldMap CloneChild state
            Sequence(newChildren), finalState
        | Choice(children)    -> 
            let newChildren, finalState = children |> foldMap CloneChild state
            Choice(newChildren), finalState
        | SequenceOf(child)   -> 
            let nch,ns = HandleChildType state child "#"
            SequenceOf(nch),ns
        | _                   -> old.Kind, state
        
    {
        Kind = newKind
        Constraints = old.Constraints
        Location = old.Location
        AcnProperties = old.AcnProperties
    }, newState


type ReferenceOrParamOrTemp =
    | AcnParam of AcnParameter
    | AcnTemp  of AcnTempType
    | AcnRef   of LongReferenceResolved

let AcnHouseKeeping (oldAsn1:AstRoot) (acn:AcnAstResolved) (tas:NewTas) : AcnAstResolved =
    let p0 = tas.originalTypePath
    let p1 = [tas.ModName; tas.TasName]
    let moveableLongReference (x:LongReferenceResolved) = 
        if x.decType.AbsPath = p0 then        
            match x.Kind with 
            | SizeDeterminant | ChoiceDeteterminant -> true 
            | _ ->false
        else
            match x.Kind with 
            | RefTypeArgument(_) -> false 
            | _                  -> true
    let GetParameterNameByReference (r:LongReferenceResolved) =
        match r.Kind with
        | SizeDeterminant      -> "nSize"
        | ChoiceDeteterminant  -> "choiceID"
        | PresenceInt(_) | PresenceStr(_) | PresenceBool   -> r.determinant.AbsPath |> List.rev |> List.head
        | _                    -> raise(BugErrorException "")
    let CreateParameterByReference (r:LongReferenceResolved) =
        match r.Kind with
        | SizeDeterminant     -> 
            [AcnParam {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = (GetParameterNameByReference r); Asn1Type = AcnTypes.Integer; Mode=DecodeMode; Location = emptyLocation}]
        | ChoiceDeteterminant -> 
            let targetType = Ast.GetTypeByAbsPath r.determinant.AbsPath oldAsn1
            let md, ts = match targetType.Kind with
                         | ReferenceType(m,t,_) -> m,t
                         | _                  -> raise(BugErrorException "")
            [AcnParam {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = (GetParameterNameByReference r); Asn1Type = RefTypeCon(md, ts); Mode=DecodeMode; Location = emptyLocation}]
        | PresenceInt(_)      ->
            [AcnParam {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = (GetParameterNameByReference r); Asn1Type = AcnTypes.Integer; Mode=DecodeMode; Location = emptyLocation}]
        | PresenceStr(_)      ->
            let targetType = Ast.GetTypeByAbsPath r.determinant.AbsPath oldAsn1
            let md, ts = match targetType.Kind with
                         | ReferenceType(m,t,_) -> m,t
                         | _                  -> raise(BugErrorException "")
            [AcnParam {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = (GetParameterNameByReference r); Asn1Type = RefTypeCon(md, ts); Mode=DecodeMode; Location = emptyLocation}]
        | PresenceBool        ->
            [AcnParam {AcnParameter.ModName = tas.ModName; TasName = tas.TasName; Name = (GetParameterNameByReference r); Asn1Type = AcnTypes.Boolean; Mode=DecodeMode; Location = emptyLocation}]
        | _     -> []
    let CreateRefToParamByReference  (r:LongReferenceResolved) decType =
        [AcnRef {r with decType = decType; determinant=ParamPoint [tas.ModName;tas.TasName; (GetParameterNameByReference r)]}]

    let newAcn = seq {
            for r in acn.References do
                if (moveableLongReference r) && (r.decType.AbsPath |> List.StartsWith p0) then
                    if r.determinant.AbsPath |> List.StartsWith p0 then
                        let decTypePath = r.decType.AbsPath |> List.Replace p0 p1
                        let determPath = r.determinant.AbsPath |> List.Replace p0 p1
                        let newR = {r with decType = r.decType.ReplacePath decTypePath;  determinant = r.determinant.ReplacePath determPath}
                        yield AcnRef newR
                    else
                        if r.decType.AbsPath = p0 then 
                            //change kind in original reference
                            yield AcnRef {r with Kind = RefTypeArgument (GetParameterNameByReference r)}
                            //Add Parameter
                            yield! CreateParameterByReference r 
                            //Add References To Parameters
                            let decType = TypePoint p1
                            yield! CreateRefToParamByReference r decType
                        else
                            let newR = {r with decType = r.decType.ReplacePath p0;  Kind = RefTypeArgument (GetParameterNameByReference r)}
                            yield AcnRef newR
                            //Add Parameter
                            yield! CreateParameterByReference r 
                            //Add References To Parameters
                            let decType = TypePoint (r.decType.AbsPath |> List.Replace p0 p1)
                            yield! CreateRefToParamByReference r decType
                            
                else
                    yield AcnRef r
                    
        }

    let newParams = newAcn |> Seq.choose(fun x -> match x with AcnParam(p) -> Some p | _ -> None) |> Seq.distinct |> Seq.toList 
    let newRefs = newAcn |> Seq.choose(fun x -> match x with AcnRef(p) -> Some p | _ -> None) |> Seq.distinct |> Seq.toList
    {acn with Parameters = acn.Parameters@newParams; References = newRefs}

let CloneModule (oldAsn1:AstRoot) (old:Asn1Module) (cons:Constructors<State>) (state:State)  = 
    let thisModTasses = state.newTases |>List.filter(fun tas -> tas.ModName = old.Name.Value) 
    let restState = {state with newTases = state.newTases|>List.filter(fun tas -> tas.ModName <> old.Name.Value) }
    let newTasses = thisModTasses |> List.map (fun tas -> {TypeAssignment.Name = tas.TasName.AsLoc ; c_name = ToC2 tas.TasName; ada_name = ToC2 tas.TasName; Type = tas.Type; Comments = [||]} )
    let newAcn = thisModTasses |> List.fold(fun curAcn tas -> AcnHouseKeeping oldAsn1 curAcn tas) restState.acn
    defaultConstructors.createModule oldAsn1 {old with TypeAssignments = old.TypeAssignments @ newTasses} cons {restState with acn=newAcn  }    
    

let DoWork ast acn (icdGenerator:bool) =
    let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) =
        CloneTypePriv old m key cons state icdGenerator
    let rec CloneTreeMulti ast (state:State) = 
        let rec CopySingleTree ast (state:State) = 
            CloneTree ast {defaultConstructors with cloneType =  CloneType; createModule = CloneModule} state
        let newTree, newState = CopySingleTree ast state
        match  Seq.isEmpty newState.newTases with
        | true -> newTree, newState.acn
        | false  -> CloneTreeMulti newTree newState
    CloneTreeMulti ast {State.newTases = []; acn=acn}
    

