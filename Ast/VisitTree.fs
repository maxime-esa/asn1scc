module VisitTree

open Ast
open FsUtils

type Assignment =
    | ValueAssignment of ValueAssignment
    | TypeAssignment    of TypeAssignment

type ConstraintType =
    | Same        of Asn1Type
    | LengthOf    of Asn1Type
    | AlphabetOf  of Asn1Type
    member x.Type = match x with Same(t) | LengthOf(t) | AlphabetOf(t)  -> t


type Visitors<'state> = {
    visitFile: Asn1File -> 'state -> 'state
    visitModule: Asn1Module -> 'state -> 'state
    visitTypeAssignment: TypeAssignment -> Asn1Module -> 'state -> 'state
    visitValueAssignment:ValueAssignment -> Asn1Module -> 'state -> 'state
    visitType : Asn1Type -> list<string> -> option<Asn1Type> -> Assignment -> Asn1Module -> AstRoot -> 'state -> 'state
    visitValue : Asn1Value -> Asn1Type -> Asn1Module -> AstRoot -> 'state -> 'state
    visitConstraint : Asn1Constraint -> ConstraintType -> list<string> -> Asn1Module -> AstRoot -> 'state -> 'state
}

let rec VisitTree (r:AstRoot) vis state =
        r.Files |> Seq.fold (fun s f -> VisitFile f r vis s) state


and VisitFile (f:Asn1File) (r:AstRoot) vis state =
    let s1 = f.Modules |> Seq.fold (fun s m -> VisitModule m r vis s) state
    vis.visitFile f s1

and VisitModule (m:Asn1Module) (r:AstRoot) vis state = 
    let s0 = vis.visitModule m state
    let s1 = m.TypeAssignments |> Seq.fold (fun s x -> VisitTypeAssignment x m r vis s) s0
    m.ValueAssignments |> Seq.fold (fun s x -> VisitValueAssignment x m r vis s) s1

and VisitTypeAssignment (t:TypeAssignment) (m:Asn1Module) (r:AstRoot) vis state = 
    let s0 = vis.visitTypeAssignment t m state
    VisitType t.Type [m.Name.Value; t.Name.Value] None (TypeAssignment t)  m r vis s0

and VisitValueAssignment (vas:ValueAssignment) (m:Asn1Module) (r:AstRoot) vis state = 
    let s0 = vis.visitValueAssignment vas m state
    let ts = VisitType vas.Type [m.Name.Value; vas.Name.Value] None (ValueAssignment vas) m r vis s0
    VisitValue vas.Value vas.Type m r vis ts

and VisitType (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) vis state = 
    let s0 = vis.visitType t path parent ass m r state
    let s1 = t.Constraints |> Seq.fold(fun s c -> VisitConstraint c (Same t) path m r vis s) s0
    match t.Kind with
    | SequenceOf(child) -> VisitType child (path@["#"]) (Some t) ass m r vis s1
    | Sequence(children) | Choice(children) ->
        children |> Seq.fold (fun s ch -> VisitType ch.Type (path@[ch.Name.Value]) (Some t) ass m r vis s) s1
    | _                 -> s1
        
and VisitValue (v:Asn1Value) (t:Asn1Type) m (r:AstRoot) vis state =
    let s0 = vis.visitValue v t m r state
    match v.Kind with
    | SeqValue(values) ->
        let actType = GetActualType t r
        match actType.Kind with
        | Sequence(children)  ->
            values |> Seq.fold(fun s (chname,chval) -> VisitValue chval (getChildType chname children) m r vis s) s0
        | _                   ->    raise(SemanticError(v.Location, "Unexpected sequence value"))
    | ChValue(nm,chval)     ->
        let actType = GetActualType t r
        match actType.Kind with
        | Choice(children)  ->   VisitValue chval (getChildType nm children) m r vis s0
        | _                 ->    raise(SemanticError(v.Location, "Unexpected choice value"))
    | SeqOfValue(values) ->
        let actType = GetActualType t r
        match actType.Kind with
        | SequenceOf(chType)    -> values |> Seq.fold(fun s chv -> VisitValue chv chType m r vis s) s0
        | _                 ->    raise(SemanticError(v.Location, "Unexpected Sequence Of value"))
    | _                 -> s0
            
and VisitConstraint (c:Asn1Constraint) (ct:ConstraintType) path m (r:AstRoot) vis state =
    let s0 = vis.visitConstraint c ct path m r state
    let t = match ct with Same(a) | LengthOf(a) | AlphabetOf(a) -> a
    match c with
    | SingleValueContraint(v)   -> VisitValue v t m r vis s0
    | RangeContraint(v1,v2,_,_)     -> 
        let s1 = VisitValue v1 t m r vis s0
        VisitValue v2 t m r vis s1
    | RangeContraint_val_MAX(v,_) -> VisitValue v t m r vis s0
    | RangeContraint_MIN_val(v,_) -> VisitValue v t m r vis s0
    | RangeContraint_MIN_MAX    -> s0
    | TypeInclusionConstraint(_)    -> s0
    | SizeContraint(c)          -> VisitConstraint c (LengthOf t) path m r vis s0
    | AlphabetContraint(c)      -> VisitConstraint c (AlphabetOf t) path m r vis s0
    | UnionConstraint(c1,c2,_)    
    | IntersectionConstraint(c1,c2)
    | ExceptConstraint(c1,c2)
    | RootConstraint2(c1,c2)    -> 
        let s1 = VisitConstraint c1 (Same t) path m r vis s0
        VisitConstraint c2 (Same t) path m r vis s1
    | AllExceptConstraint(c)    
    | RootConstraint(c)         -> VisitConstraint c (Same t) path m r vis s0
    | WithComponentConstraint(c)->
        let actType = GetActualType t r
        match actType.Kind with
        | SequenceOf(chType)    -> VisitConstraint c (Same chType) (path @ ["#"])m r vis s0
        | _                     -> raise(SemanticError(t.Location, "Unexpected constraint type"))
    | WithComponentsConstraint(ncs) ->
        let actType = GetActualType t r
        match actType.Kind with
        | Sequence(children) | Choice(children) ->
            ncs |> Seq.fold(fun s nc -> 
                                match nc.Contraint with
                                | Some(c) ->  VisitConstraint c (Same (getChildType nc.Name children)) (path @ [nc.Name.Value]) m r vis s 
                                | None    ->  s ) s0
        | _       -> raise(SemanticError(t.Location, "Unexpected constraint type"))
        
        

        
let DefaultVisitors  = 
    {
        visitFile = (fun f s -> s)
        visitModule = (fun m s -> s)
        visitTypeAssignment = (fun t m s -> s)
        visitValueAssignment = (fun v m s -> s)
        visitType = (fun t path par ass m r s-> s)
        visitValue = (fun v t m r s -> s)
        visitConstraint = (fun c t p m r s -> s)
    }
    



//////////////////////////////////////////////////////////
(*
let DefaultVisitors  = 
    {
        visitFile = VisitFile
        visitModule = VisitModule
    }



type collectedState = {
    mm : seq<int>
    m2 : seq<string>
}



let VisitModule2 (m:Asn1Module) vis (state:collectedState) = state

let dummy (r:AstRoot) =
    let initialState = {collectedState.mm = []; m2=[]}
    let visitors = {DefaultVisitors with visitModule = VisitModule2}
    let colState = VisitTree r DefaultVisitors initialState
    colState
    

*)