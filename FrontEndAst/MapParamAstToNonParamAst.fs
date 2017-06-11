(*
* Copyright (c) 2008-2012 Semantix and (c) 2012-2015 Neuropublic
*
* This file is part of the ASN1SCC tool.
*
* Licensed under the terms of GNU General Public Licence as published by
* the Free Software Foundation.
*
*  For more informations see License.txt file
*)

module MapParamAstToNonParamAst

open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils




let getModuleByName = ParameterizedAsn1Ast.getModuleByName

let getTasByName  = ParameterizedAsn1Ast.getTasByName



let rec getSequenceChildren (r:ParameterizedAsn1Ast.AstRoot) (input:list<ParameterizedAsn1Ast.SequenceChild>) : list<ParameterizedAsn1Ast.ChildInfo> =
    seq {
        for ch in input do
        match ch with
        | ParameterizedAsn1Ast.ChildInfo ch  -> yield ch
        | ParameterizedAsn1Ast.ComponentsOf (md,ts) ->
            let tas = ParameterizedAsn1Ast.getTypeAssigment r md ts
            match tas.Type.Kind with
            | ParameterizedAsn1Ast.Sequence(children)    ->
                 yield! getSequenceChildren r children
            | _                                          -> raise(SemanticError(ts.Location, "Expecting SEQUENCE type"))    
            }|> Seq.toList

let rec getActualKind r kind =
    match kind with
    | ParameterizedAsn1Ast.ReferenceType(md, ts,_) -> 
        let newTas = ParameterizedAsn1Ast.getTypeAssigment r md ts
        getActualKind r newTas.Type.Kind
    | _                                            -> kind


let rec MapAsn1Value (r:ParameterizedAsn1Ast.AstRoot) (kind: ParameterizedAsn1Ast.Asn1TypeKind) (v:ParameterizedAsn1Ast.Asn1Value) :Asn1Ast.Asn1Value =
    let rec getActualKindAndModule r kind =
        let rec getActualaux r kind modName=
            match kind with
            | ParameterizedAsn1Ast.ReferenceType(md, ts,_) -> 
                let mdl = ParameterizedAsn1Ast.getModuleByName  r md
                let newTas = ParameterizedAsn1Ast.getTypeAssigment r md ts
                getActualaux r newTas.Type.Kind (Some mdl.Name)
            | _                                            -> kind, modName
        getActualaux r kind None

    let MapAsn1ValueKind (r:ParameterizedAsn1Ast.AstRoot) (kind: ParameterizedAsn1Ast.Asn1TypeKind) (vk:ParameterizedAsn1Ast.Asn1ValueKind) :Asn1Ast.Asn1ValueKind =
        let actKind = getActualKind r kind
        match vk with
        |ParameterizedAsn1Ast.IntegerValue(v)       -> Asn1Ast.IntegerValue v
        |ParameterizedAsn1Ast.RealValue(v)          -> Asn1Ast.RealValue v
        |ParameterizedAsn1Ast.StringValue(v)        -> Asn1Ast.StringValue v
        |ParameterizedAsn1Ast.BooleanValue(v)       -> Asn1Ast.BooleanValue v
        |ParameterizedAsn1Ast.BitStringValue(v)     -> Asn1Ast.BitStringValue v
        |ParameterizedAsn1Ast.OctetStringValue v    -> Asn1Ast.OctetStringValue v
        |ParameterizedAsn1Ast.RefValue(v1,v2)       -> 
            let actKind, mdName = getActualKindAndModule r kind
            match actKind with
            | ParameterizedAsn1Ast.Enumerated(items)    ->  
                match mdName with
                | None  ->  Asn1Ast.RefValue(v1,v2)
                | Some(s)   -> Asn1Ast.RefValue(s,v2)
            | _                                         ->  Asn1Ast.RefValue(v1,v2)
        |ParameterizedAsn1Ast.SeqOfValue(vals)      -> 
            match actKind with
            | ParameterizedAsn1Ast.SequenceOf(ch)    -> Asn1Ast.SeqOfValue(vals |> List.map (MapAsn1Value r ch.Kind))
            | _                                      -> raise(SemanticError(v.Location, "Expecting a SEQUENCE OF value"))
        |ParameterizedAsn1Ast.SeqValue(vals)        -> 
            match actKind with
            |ParameterizedAsn1Ast.Sequence(children) ->
                let children = getSequenceChildren r children
                let mapChildVal (nm:StringLoc, chv:ParameterizedAsn1Ast.Asn1Value) =
                    match children |> Seq.tryFind(fun ch -> ch.Name=nm) with
                    | Some(child)   -> (nm, MapAsn1Value r child.Type.Kind chv)
                    | _             -> raise(SemanticError(nm.Location, sprintf "Unknown component name '%s'" nm.Value))
                Asn1Ast.SeqValue(vals |> List.map mapChildVal)
            | _                 -> raise(SemanticError(v.Location, "Expecting a SEQUENCE value"))
        |ParameterizedAsn1Ast.ChValue(n,v)          -> 
            match actKind with
            |ParameterizedAsn1Ast.Choice(children) ->
                match children |> Seq.tryFind(fun x -> x.Name=n) with
                | Some(child)   -> Asn1Ast.ChValue(n, MapAsn1Value r child.Type.Kind v)
                | None          -> raise(SemanticError(n.Location, sprintf "Unknown alternative name '%s'" n.Value))
            | _                 -> raise(SemanticError(v.Location, "Expecting a CHOICE value"))
            
        |ParameterizedAsn1Ast.NullValue             -> Asn1Ast.NullValue
        |ParameterizedAsn1Ast.EmptyList             ->
            match actKind with
            |ParameterizedAsn1Ast.Sequence(_)       -> Asn1Ast.SeqValue []
            |ParameterizedAsn1Ast.SequenceOf(_)     -> Asn1Ast.SeqOfValue []
            | _                                     -> raise(SemanticError(v.Location, "Unexpected value"))
    {
        Asn1Ast.Asn1Value.Kind = MapAsn1ValueKind r kind v.Kind
        Location = v.Location
    }




and MapAsn1Optionality (r:ParameterizedAsn1Ast.AstRoot) (kind: ParameterizedAsn1Ast.Asn1TypeKind) (o:ParameterizedAsn1Ast.Asn1Optionality) :Asn1Ast.Asn1Optionality =
    match o with
    | ParameterizedAsn1Ast.AlwaysAbsent     -> Asn1Ast.AlwaysAbsent
    | ParameterizedAsn1Ast.AlwaysPresent    -> Asn1Ast.AlwaysPresent
    | ParameterizedAsn1Ast.Optional         -> Asn1Ast.Optional ({Asn1Ast.Optional.defaultValue = None})
    | ParameterizedAsn1Ast.Default(v)       -> Asn1Ast.Optional ({Asn1Ast.Optional.defaultValue = Some (MapAsn1Value r kind  v)})

and MapChildInfo (r:ParameterizedAsn1Ast.AstRoot)  (c:ParameterizedAsn1Ast.ChildInfo) :Asn1Ast.ChildInfo =
    {
        Asn1Ast.ChildInfo.Name = c.Name
        ada_name = ToC2 c.Name.Value
        c_name = ToC2 c.Name.Value
        present_when_name = ToC2 c.Name.Value
        Type = MapAsn1Type r c.Type
        Optionality = match c.Optionality with
                      |None -> None
                      |Some(x) -> Some (MapAsn1Optionality r c.Type.Kind x)
        Comments = c.Comments
    }

and MapNamedItem (r:ParameterizedAsn1Ast.AstRoot)  (n:ParameterizedAsn1Ast.NamedItem) :Asn1Ast.NamedItem =
    {
        Asn1Ast.NamedItem.Name = n.Name
        c_name = n.Name.Value
        ada_name = n.Name.Value
        _value = match n._value with
                 | None -> None
                 | Some(x)  -> Some (MapAsn1Value r ParameterizedAsn1Ast.Integer x)
        Comments = n.Comments
    }



and MapNamedConstraint (r:ParameterizedAsn1Ast.AstRoot) (kind: ParameterizedAsn1Ast.Asn1TypeKind) (x:ParameterizedAsn1Ast.NamedConstraint) :Asn1Ast.NamedConstraint =
    let childKind = match getActualKind r kind with
                    | ParameterizedAsn1Ast.Choice(children)     ->
                        match children |> Seq.tryFind(fun ch -> ch.Name = x.Name) with
                        | None      -> raise(SemanticError(x.Name.Location, sprintf "Unknown component name '%s'" x.Name.Value))
                        | Some(child)   -> child.Type.Kind

                    | ParameterizedAsn1Ast.Sequence(children)   ->
                        let children = getSequenceChildren r children
                        match children |> Seq.tryFind(fun ch -> ch.Name = x.Name) with
                        | None      -> raise(SemanticError(x.Name.Location, sprintf "Unknown component name '%s'" x.Name.Value))
                        | Some(child)   -> child.Type.Kind
                    | _                                         -> raise(SemanticError(x.Name.Location, sprintf "Unexpected constraint type" ))
    {
        Asn1Ast.NamedConstraint.Name = x.Name; 
        Mark = match x.Mark with
                | ParameterizedAsn1Ast.NoMark        -> Asn1Ast.NoMark
                | ParameterizedAsn1Ast.MarkPresent   -> Asn1Ast.MarkPresent
                | ParameterizedAsn1Ast.MarkAbsent    -> Asn1Ast.MarkAbsent
                | ParameterizedAsn1Ast.MarkOptional  -> Asn1Ast.MarkOptional
        Contraint = match x.Contraint with
                    | None  -> None
                    | Some(cc)  -> Some (MapAsn1Constraint r childKind cc)
    }

and MapAsn1Constraint (r:ParameterizedAsn1Ast.AstRoot) (kind: ParameterizedAsn1Ast.Asn1TypeKind) (c:ParameterizedAsn1Ast.Asn1Constraint) :Asn1Ast.Asn1Constraint =
    match c with
    | ParameterizedAsn1Ast.SingleValueContraint(v)          -> Asn1Ast.SingleValueContraint (MapAsn1Value r kind v)
    | ParameterizedAsn1Ast.RangeContraint(v1,v2,b1,b2)      -> Asn1Ast.RangeContraint(MapAsn1Value r kind v1,MapAsn1Value r kind v2,b1,b2)
    | ParameterizedAsn1Ast.RangeContraint_val_MAX(v,b)        -> Asn1Ast.RangeContraint_val_MAX (MapAsn1Value r kind v, b)
    | ParameterizedAsn1Ast.RangeContraint_MIN_val(v,b)        -> Asn1Ast.RangeContraint_MIN_val (MapAsn1Value r kind v, b)
    | ParameterizedAsn1Ast.TypeInclusionConstraint(s1,s2)   -> Asn1Ast.TypeInclusionConstraint(s1,s2)
    | ParameterizedAsn1Ast.SizeContraint(c)                 -> Asn1Ast.SizeContraint(MapAsn1Constraint r ParameterizedAsn1Ast.Integer c)
    | ParameterizedAsn1Ast.AlphabetContraint(c)             -> Asn1Ast.AlphabetContraint(MapAsn1Constraint r ParameterizedAsn1Ast.IA5String c)
    | ParameterizedAsn1Ast.UnionConstraint(c1,c2, b)           -> Asn1Ast.UnionConstraint(MapAsn1Constraint r kind c1, MapAsn1Constraint r kind c2, b)
    | ParameterizedAsn1Ast.IntersectionConstraint(c1,c2)    -> Asn1Ast.IntersectionConstraint(MapAsn1Constraint r kind c1, MapAsn1Constraint r kind c2)
    | ParameterizedAsn1Ast.AllExceptConstraint(c)           -> Asn1Ast.AllExceptConstraint(MapAsn1Constraint r kind c)
    | ParameterizedAsn1Ast.ExceptConstraint(c1,c2)          -> Asn1Ast.ExceptConstraint(MapAsn1Constraint r kind c1, MapAsn1Constraint r kind c2)
    | ParameterizedAsn1Ast.RootConstraint(c1)               -> Asn1Ast.RootConstraint(MapAsn1Constraint r kind c1)
    | ParameterizedAsn1Ast.RootConstraint2(c1,c2)           -> Asn1Ast.RootConstraint2(MapAsn1Constraint r kind c1, MapAsn1Constraint r kind c2)
    | ParameterizedAsn1Ast.WithComponentConstraint(c)       -> 
        match getActualKind r kind with
        | ParameterizedAsn1Ast.SequenceOf(child)    ->        Asn1Ast.WithComponentConstraint(MapAsn1Constraint r child.Kind c)
        | _                                         ->        raise(SemanticError(emptyLocation,"Unexpected constraint type"))
    | ParameterizedAsn1Ast.WithComponentsConstraint(ncs)    -> 
        Asn1Ast.WithComponentsConstraint(ncs|> List.map (MapNamedConstraint r kind))


and MapAsn1Type (r:ParameterizedAsn1Ast.AstRoot) (t:ParameterizedAsn1Ast.Asn1Type) :Asn1Ast.Asn1Type =
    let aux kind : Asn1Ast.Asn1Type=
        {
            Asn1Ast.Asn1Type.Kind = kind
            Constraints = t.Constraints |> List.map (MapAsn1Constraint r t.Kind)
            Location = t.Location
        }        
    match t.Kind with
    | ParameterizedAsn1Ast.Integer          -> aux Asn1Ast.Integer
    | ParameterizedAsn1Ast.Real             -> aux Asn1Ast.Real
    | ParameterizedAsn1Ast.IA5String        -> aux Asn1Ast.IA5String
    | ParameterizedAsn1Ast.NumericString    -> aux Asn1Ast.NumericString
    | ParameterizedAsn1Ast.OctetString      -> aux Asn1Ast.OctetString
    | ParameterizedAsn1Ast.NullType         -> aux Asn1Ast.NullType
    | ParameterizedAsn1Ast.BitString        -> aux Asn1Ast.BitString
    | ParameterizedAsn1Ast.Boolean          -> aux Asn1Ast.Boolean
    | ParameterizedAsn1Ast.Enumerated(items)-> aux (Asn1Ast.Enumerated(items |> List.map (MapNamedItem r)))
    | ParameterizedAsn1Ast.SequenceOf(child)-> aux (Asn1Ast.SequenceOf(MapAsn1Type r child))
    | ParameterizedAsn1Ast.Sequence(children)   -> 
        let children = getSequenceChildren r children
        aux (Asn1Ast.Sequence(children |> List.map (MapChildInfo r) ))
    | ParameterizedAsn1Ast.Choice(children)     -> aux (Asn1Ast.Choice(children |> List.map (MapChildInfo r) ))
    | ParameterizedAsn1Ast.ReferenceType(mdName,ts, args)   ->
        match args with
        | []    ->  aux (Asn1Ast.ReferenceType({Asn1Ast.ReferenceType.modName = mdName; tasName = ts; tabularized = false}))
        | _     ->  raise(BugErrorException "")

    

let MapTypeAssignment (r:ParameterizedAsn1Ast.AstRoot) (tas:ParameterizedAsn1Ast.TypeAssignment) :Asn1Ast.TypeAssignment =
    {
        Asn1Ast.TypeAssignment.Name = tas.Name
        Type = MapAsn1Type r tas.Type
        c_name = ToC2 tas.Name.Value
        ada_name = ToC2 tas.Name.Value
        Comments = tas.Comments
    }

let MapValueAssignment (r:ParameterizedAsn1Ast.AstRoot) (vas:ParameterizedAsn1Ast.ValueAssignment) :Asn1Ast.ValueAssignment =
    
    {
        Asn1Ast.ValueAssignment.Name = vas.Name
        Type = MapAsn1Type r vas.Type
        Value = MapAsn1Value r  vas.Type.Kind vas.Value
        //Scope = 
        //    match vas.Scope with
        //    | ParameterizedAsn1Ast.GlobalScope      ->  Asn1Ast.GlobalScope
        //    | ParameterizedAsn1Ast.TypeScope(m,t)   ->  Asn1Ast.TypeScope(m,t)
        c_name = vas.c_name
        ada_name = vas.ada_name
    }


let MapModule (r:ParameterizedAsn1Ast.AstRoot) (m:ParameterizedAsn1Ast.Asn1Module) :Asn1Ast.Asn1Module =
    let DoImportedModule (x:ParameterizedAsn1Ast.ImportedModule) : Asn1Ast.ImportedModule option =
        let types = x.Types |> List.choose(fun ts -> 
                                            let tas = getModuleByName r x.Name |> getTasByName ts
                                            match tas.Parameters with
                                            | []    -> Some ts
                                            | _     -> None     //Paramterized Import, so remove it
                                       )
        match types with
        | []    -> None
        | _     -> Some  { Asn1Ast.ImportedModule.Name = x.Name; Types = types; Values = x.Values}
    {
        Asn1Ast.Asn1Module.Name = m.Name
        TypeAssignments = m.TypeAssignments |> List.filter(fun x -> x.Parameters.Length = 0) |> List.map (MapTypeAssignment r)
        ValueAssignments = m.ValueAssignments |> List.map (MapValueAssignment r)
        Imports = m.Imports |> List.choose DoImportedModule
        Exports  = match m.Exports with
                   | ParameterizedAsn1Ast.All               -> Asn1Ast.All
                   | ParameterizedAsn1Ast.OnlySome(lst)     -> Asn1Ast.OnlySome(lst)
        Comments = m.Comments
    }

let MapFile (r:ParameterizedAsn1Ast.AstRoot) (f:ParameterizedAsn1Ast.Asn1File) :Asn1Ast.Asn1File =
    {
        Asn1Ast.Asn1File.FileName = f.FileName
        Tokens = f.Tokens
        Modules = f.Modules |> List.map (MapModule r)
    }



let DoWork (r:ParameterizedAsn1Ast.AstRoot) : Asn1Ast.AstRoot =
    let r = RemoveParamterizedTypes.DoWork r
    {
        Asn1Ast.AstRoot.Files = r.Files |> List.map (MapFile r)
        args = r.args
    
    }
    