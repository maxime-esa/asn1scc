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

module Asn1Ast
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils
open CommonTypes


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ASN1 VALUES DEFINITION    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type Asn1Value = {
    Kind:Asn1ValueKind
    Location: SrcLoc
}


and Asn1ValueKind =
    |   IntegerValue        of IntLoc
    |   RealValue           of DoubleLoc
    |   StringValue         of StringLoc
    |   BooleanValue        of BoolLoc
    |   BitStringValue      of StringLoc
    |   OctetStringValue    of list<ByteLoc>
    |   RefValue            of StringLoc*StringLoc
    |   SeqOfValue          of list<Asn1Value>
    |   SeqValue            of list<StringLoc*Asn1Value>
    |   ChValue             of StringLoc*Asn1Value
    |   NullValue




type NamedConstraintMark =
    | NoMark
    | MarkPresent
    | MarkAbsent
    | MarkOptional


type Asn1Constraint = 
    | SingleValueContraint              of Asn1Value             
    | RangeContraint                    of Asn1Value*Asn1Value*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX            of Asn1Value*bool         //min, InclusiveMin(=true)
    | RangeContraint_MIN_val            of Asn1Value*bool         //max, InclusiveMax(=true)
    | RangeContraint_MIN_MAX            
    | TypeInclusionConstraint           of StringLoc*StringLoc     
    | SizeContraint                     of Asn1Constraint               
    | AlphabetContraint                 of Asn1Constraint           
    | UnionConstraint                   of Asn1Constraint*Asn1Constraint*bool //left,righ, virtual constraint
    | IntersectionConstraint            of Asn1Constraint*Asn1Constraint
    | AllExceptConstraint               of Asn1Constraint
    | ExceptConstraint                  of Asn1Constraint*Asn1Constraint
    | RootConstraint                    of Asn1Constraint
    | RootConstraint2                   of Asn1Constraint*Asn1Constraint
    | WithComponentConstraint           of Asn1Constraint
    | WithComponentsConstraint          of list<NamedConstraint>

and NamedConstraint = {
    Name:StringLoc;
    Contraint:Asn1Constraint option
    Mark:NamedConstraintMark
}


type uperRange<'a> =
    | Concrete      of 'a*'a    //[a, b]
    | NegInf        of 'a               //(-inf, b]
    | PosInf        of 'a               //[a, +inf)
    | Empty
    | Full                                      // (-inf, +inf)

type Asn1Size<'a> =
    | Bounded of   'a
    | Infinite


type INTTYPE =
    | UINT      // declared as unsigned integer
    | SINT      // declared as signed integer



type NamedItem = {
    Name:StringLoc
    c_name:string
    ada_name:string
    _value:Asn1Value option
    Comments: string array
}

type Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of Asn1Value



type Asn1Type = {
    Kind            : Asn1TypeKind;
    Constraints     : Asn1Constraint list
    Location        : SrcLoc //Line no, Char pos
}


and Asn1TypeKind =
    | Integer
    | Real
    | IA5String
    | NumericString
    | OctetString 
    | NullType
    | BitString
    | Boolean 
    | Enumerated        of list<NamedItem>
    | SequenceOf        of Asn1Type
    | Sequence          of list<ChildInfo>
    | Choice            of list<ChildInfo>
    | ReferenceType     of ReferenceType

and ReferenceType = {
    modName     : StringLoc
    tasName     : StringLoc
    tabularized : bool
}


and ChildInfo = {
    Name                        : StringLoc;
    c_name                      : string
    ada_name                    : string                     
    present_when_name           : string // used only by choices. Does not contain the "_PRESENT". Not to be used directly by backends.
    Type                        : Asn1Type
    Optionality                 : Asn1Optionality option
    Comments                    : string array
}


type TypeAssignment = {
    Name:StringLoc
    c_name:string
    ada_name:string
    Type:Asn1Type
    Comments: string array
}

type ValueAssignment = {
    Name:StringLoc
    c_name:string
    ada_name:string
    Type:Asn1Type
    Value:Asn1Value
}

type Exports =
    | All
    | OnlySome of list<string>

type  ImportedModule = {
    Name:StringLoc
    Types:list<StringLoc>
    Values:list<StringLoc>
}

type Asn1Module = {
    Name : StringLoc
    TypeAssignments : list<TypeAssignment>
    ValueAssignments : list<ValueAssignment>
    Imports : list<ImportedModule>
    Exports : Exports
    Comments : string array
}

type Asn1File = {
    FileName:string;
    Tokens: IToken array
    Modules : list<Asn1Module>
}

type AstRoot = {
    Files: list<Asn1File>
    args:CommandLineSettings
}




type AstRoot with
    member r.Modules = r.Files |> List.collect(fun f -> f.Modules)
    member r.GetModuleByName(name:StringLoc)  = 
        let (n,loc) = name.AsTupple
        match r.Modules |> Seq.tryFind( fun m -> m.Name = name)  with
        | Some(m) -> m
        | None    -> raise(SemanticError(loc, sprintf "No Module Defined with name: %s" n ))

type Asn1Module with
    member this.ExportedTypes =
        match this.Exports with
        | All   -> 
            let importedTypes = this.Imports |> List.collect(fun imp -> imp.Types) |> List.map(fun x -> x.Value)
            (this.TypeAssignments |> List.map(fun x -> x.Name.Value))@importedTypes
        | OnlySome(typesAndVars)    ->
            typesAndVars |> List.filter(fun x -> System.Char.IsUpper (x.Chars 0))
    member this.ExportedVars =
        match this.Exports with
        | All   -> this.ValueAssignments |> List.map(fun x -> x.Name.Value)
        | OnlySome(typesAndVars)    ->
            typesAndVars |> List.filter(fun x -> not (System.Char.IsUpper (x.Chars 0)))
    member m.TryGetTypeAssignmentByName name (r:AstRoot) =
        match m.TypeAssignments|> Seq.tryFind(fun x -> x.Name = name) with
        | Some t   -> Some t
        | None      -> 
            let othMods = m.Imports |> Seq.filter(fun imp -> imp.Types |> Seq.exists((=) name)) 
                                |> Seq.map(fun imp -> imp.Name) |> Seq.toList
            match othMods with
            | firstMod::_   -> 
                match r.Modules |> Seq.tryFind( fun m -> m.Name = firstMod)  with
                | Some(m) -> m.TryGetTypeAssignmentByName name r
                | None    -> None
            | []            -> None

    member m.GetTypeAssignmentByName name (r:AstRoot) =
        match m.TypeAssignments|> Seq.tryFind(fun x -> x.Name = name) with
        | Some(t)   -> t
        | None      -> 
            let othMods = m.Imports |> Seq.filter(fun imp -> imp.Types |> Seq.exists((=) name)) 
                                |> Seq.map(fun imp -> imp.Name) |> Seq.toList
            match othMods with
            | firstMod::tail   -> r.GetModuleByName(firstMod).GetTypeAssignmentByName name r
            | []               ->            
                let (n,loc) = name.AsTupple
                raise(SemanticError(loc, sprintf "No Type Assignment with name: %s is defined in Module %s" n m.Name.Value))
    member m.GetValueAsigByName(name:StringLoc) (r:AstRoot) =
        let (n,loc) = name.AsTupple
        let value = m.ValueAssignments |> Seq.tryFind(fun x -> x.Name = name) 
        match value with
        | Some(v)       -> v
        | None          ->
            let othMods = m.Imports 
                          |> Seq.filter(fun imp -> imp.Values |> Seq.exists(fun vname -> vname = name)) 
                          |> Seq.map(fun imp -> imp.Name) |> Seq.toList
            match othMods with
            | firstMod::tail   -> r.GetModuleByName(firstMod).GetValueAsigByName name r
            | []               -> raise (SemanticError(loc, sprintf "No value assignment with name '%s' exists" n))



let rec GetActualType (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType ref ->
        let newmod = r.GetModuleByName(ref.modName)
        let tas = newmod.GetTypeAssignmentByName ref.tasName r
        GetActualType tas.Type r
    | _                         -> t


let GetBaseType (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType ref ->
        let newmod = r.GetModuleByName(ref.modName)
        let tas = newmod.GetTypeAssignmentByName ref.tasName r
        tas.Type
    | _                         -> t

let GetBaseTypeByName modName tasName (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let tas = mdl.GetTypeAssignmentByName tasName r
    tas.Type

let GetBaseTypeConsIncluded (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType ref ->
        let newmod = r.GetModuleByName(ref.modName)
        let tas = newmod.GetTypeAssignmentByName ref.tasName r
        let baseType = tas.Type
        {baseType with Constraints = baseType.Constraints@t.Constraints}
    | _                         -> t

let GetActualTypeByName modName tasName (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let tas = mdl.GetTypeAssignmentByName tasName r
    GetActualType tas.Type r

let GetBaseValue  modName vasName  (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let vas = mdl.GetValueAsigByName vasName r
    vas.Value

let rec GetActualValue modName vasName  (r:AstRoot) =
    let baseVal = GetBaseValue  modName vasName  r
    match baseVal.Kind with
    |RefValue(newModName, newVasName)   -> GetActualValue newModName newVasName r
    | _                                 -> baseVal


let rec GetValueAsInt (v:Asn1Value) r=
    match v.Kind with
    | IntegerValue(a)                       -> a.Value
    | RefValue(modName,valName)             -> GetValueAsInt (GetActualValue modName valName r) r
    | _                                     -> raise(SemanticError (v.Location, sprintf "Expecting Integer value"))

let GetActualTypeAllConsIncluded t (r:AstRoot) =
    let rec GetActualTypeAux (t:Asn1Type) (addionalConstraints:list<Asn1Constraint>)   =
        match t.Kind with
        | ReferenceType ref ->
            let newmod = r.GetModuleByName(ref.modName)
            let tas = newmod.GetTypeAssignmentByName ref.tasName r
            GetActualTypeAux tas.Type (t.Constraints@addionalConstraints) 
        | _                         -> {t with Constraints = (t.Constraints@addionalConstraints)}
    GetActualTypeAux t [] 

let GetActualTypeByNameAllConsIncluded modName tasName (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let tas = mdl.GetTypeAssignmentByName tasName r
    GetActualTypeAllConsIncluded tas.Type r
