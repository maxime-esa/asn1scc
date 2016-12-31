module Constraints

open System
open System.Numerics
open FsUtils
open Antlr.Runtime


type Asn1TypeName = {
    moduName    : string
    tasName     : string
}

type Asn1ValueName = {
    moduName    : string
    vasName     : string
}



type ReferenceToType = 
    | ReferenceToType of GenericFold2.ScopeNode list
    with
        override this.ToString() =
            match this with
            | ReferenceToType path -> path |> Seq.StrJoin "."
        member this.ModName =
            match this with
            | ReferenceToType path -> 
                match path with
                | (GenericFold2.MD modName)::_    -> modName
                | _                               -> raise(BugErrorException "Did not find module at the begining of the scope path")
            
type ReferenceToValue = 
    | ReferenceToValue of (GenericFold2.ScopeNode list)*(GenericFold2.VarScopNode list)
    with
        member this.ModName =
            match this with
            | ReferenceToValue (path,_) -> 
                match path with
                | (GenericFold2.MD modName)::_    -> modName
                | _                               -> raise(BugErrorException "Did not find module at the begining of the scope path")



type Asn1Module = {
    Name : string
    Imports : list<Ast.ImportedModule>
    Exports : Ast.Exports
    Comments : string array
}

type Asn1File = {
    FileName:string;
    Tokens: IToken array
    Modules : list<Asn1Module>
}


type LiteralOrReference =
    | Literal
    | ReferenceToAsn1NamedValue  of Asn1ValueName

type Asn1ValueTemplate<'v> = {
    id          : ReferenceToValue
    litOrRef    : LiteralOrReference
    refToType   : ReferenceToType
    Value       :'v
}


type IntegerValue         = Asn1ValueTemplate<BigInteger>
type RealValue            = Asn1ValueTemplate<double>
type StringValue          = Asn1ValueTemplate<string>
type BooleanValue         = Asn1ValueTemplate<bool>
type BitStringValue       = Asn1ValueTemplate<string>
type OctetStringValue     = Asn1ValueTemplate<list<byte>>
type EnumValue            = Asn1ValueTemplate<string>
type NullValue            = Asn1ValueTemplate<unit>
type SeqOfValue           = Asn1ValueTemplate<list<Asn1GenericValue>>
and SeqValue              = Asn1ValueTemplate<list<NamedValue>>
and ChValue               = Asn1ValueTemplate<NamedValue>

and NamedValue = {
    name        : string
    Value       : Asn1GenericValue
}

and Asn1GenericValue =
    | IntegerValue          of IntegerValue    
    | RealValue             of RealValue       
    | StringValue           of StringValue     
    | BooleanValue          of BooleanValue    
    | BitStringValue        of BitStringValue  
    | OctetStringValue      of OctetStringValue
    | EnumValue             of EnumValue       
    | SeqOfValue            of SeqOfValue      
    | SeqValue              of SeqValue        
    | ChValue               of ChValue         
    | NullValue             of NullValue
with 
    member this.id = 
        match this with
        | IntegerValue     v    -> v.id
        | RealValue        v    -> v.id
        | StringValue      v    -> v.id
        | BooleanValue     v    -> v.id
        | BitStringValue   v    -> v.id
        | OctetStringValue v    -> v.id
        | EnumValue        v    -> v.id
        | SeqOfValue       v    -> v.id
        | SeqValue         v    -> v.id
        | ChValue          v    -> v.id
        | NullValue        v    -> v.id
    member this.refToType = 
        match this with
        | IntegerValue     v    -> v.refToType
        | RealValue        v    -> v.refToType
        | StringValue      v    -> v.refToType
        | BooleanValue     v    -> v.refToType
        | BitStringValue   v    -> v.refToType
        | OctetStringValue v    -> v.refToType
        | EnumValue        v    -> v.refToType
        | SeqOfValue       v    -> v.refToType
        | SeqValue         v    -> v.refToType
        | ChValue          v    -> v.refToType
        | NullValue        v    -> v.refToType



type AstRootTemplate<'ASN1TYPE> = {
    Files: list<Asn1File>
    Encodings:list<Ast.Asn1Encoding>
    GenerateEqualFunctions:bool
    TypePrefix:string
    AstXmlAbsFileName:string
    IcdUperHtmlFileName:string
    IcdAcnHtmlFileName:string
    CheckWithOss:bool
    mappingFunctionsModule : string option
    valsMap : Map<ReferenceToValue, Asn1GenericValue>
    typesMap : Map<ReferenceToType, 'ASN1TYPE>
    TypeAssignments : list<'ASN1TYPE>
    ValueAssignments : list<Asn1GenericValue>
}


(*
These constraints are interim.
*)
type Asn1AnyConstraint = 
    | AnySingleValueContraint              of Asn1GenericValue             
    | AnyRangeContraint                    of Asn1GenericValue*Asn1GenericValue*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | AnyRangeContraint_val_MAX            of Asn1GenericValue*bool         //min, InclusiveMin(=true)
    | AnyRangeContraint_MIN_val            of Asn1GenericValue*bool         //max, InclusiveMax(=true)
    | AnySizeContraint                     of Asn1AnyConstraint               
    | AnyAlphabetContraint                 of Asn1AnyConstraint           
    | AnyUnionConstraint                   of Asn1AnyConstraint*Asn1AnyConstraint*bool //left,righ, virtual constraint
    | AnyIntersectionConstraint            of Asn1AnyConstraint*Asn1AnyConstraint
    | AnyAllExceptConstraint               of Asn1AnyConstraint
    | AnyExceptConstraint                  of Asn1AnyConstraint*Asn1AnyConstraint
    | AnyRootConstraint                    of Asn1AnyConstraint
    | AnyRootConstraint2                   of Asn1AnyConstraint*Asn1AnyConstraint


type GenericConstraint<'v> =
    | UnionConstraint                   of GenericConstraint<'v>*GenericConstraint<'v>*bool //left,righ, virtual constraint
    | IntersectionConstraint            of GenericConstraint<'v>*GenericConstraint<'v>
    | AllExceptConstraint               of GenericConstraint<'v>
    | ExceptConstraint                  of GenericConstraint<'v>*GenericConstraint<'v>
    | RootConstraint                    of GenericConstraint<'v>
    | RootConstraint2                   of GenericConstraint<'v>*GenericConstraint<'v>
    | SingleValueConstraint             of 'v*ReferenceToValue option

type RangeTypeConstraint<'v1,'v2>  = 
    | RangeUnionConstraint               of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>*bool //left,righ, virtual constraint
    | RangeIntersectionConstraint        of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>
    | RangeAllExceptConstraint           of RangeTypeConstraint<'v1,'v2>
    | RangeExceptConstraint              of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>
    | RangeRootConstraint                of RangeTypeConstraint<'v1,'v2>
    | RangeRootConstraint2               of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>
    | RangeSingleValueConstraint         of 'v2*ReferenceToValue option
    | RangeContraint                     of ('v1*ReferenceToValue option) *('v1*ReferenceToValue  option)*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX             of ('v1*ReferenceToValue option) *bool            //min, InclusiveMin(=true)
    | RangeContraint_MIN_val             of ('v1*ReferenceToValue option) *bool            //max, InclusiveMax(=true)

type IntegerTypeConstraint  = RangeTypeConstraint<BigInteger, BigInteger>
type PosIntTypeConstraint   = RangeTypeConstraint<UInt32, UInt32>
type CharTypeConstraint     = RangeTypeConstraint<char, string>
    
type RealTypeConstraint     = RangeTypeConstraint<double, double>


type SizableTypeConstraint<'v>  = 
    | SizeUnionConstraint               of SizableTypeConstraint<'v>*SizableTypeConstraint<'v>*bool //left,righ, virtual constraint
    | SizeIntersectionConstraint        of SizableTypeConstraint<'v>*SizableTypeConstraint<'v>
    | SizeAllExceptConstraint           of SizableTypeConstraint<'v>
    | SizeExceptConstraint              of SizableTypeConstraint<'v>*SizableTypeConstraint<'v>
    | SizeRootConstraint                of SizableTypeConstraint<'v>
    | SizeRootConstraint2               of SizableTypeConstraint<'v>*SizableTypeConstraint<'v>
    | SizeSingleValueConstraint         of 'v*ReferenceToValue  option
    | SizeContraint                     of PosIntTypeConstraint               

type IA5StringConstraint = 
    | StrUnionConstraint               of IA5StringConstraint*IA5StringConstraint*bool //left,righ, virtual constraint
    | StrIntersectionConstraint        of IA5StringConstraint*IA5StringConstraint
    | StrAllExceptConstraint           of IA5StringConstraint
    | StrExceptConstraint              of IA5StringConstraint*IA5StringConstraint
    | StrRootConstraint                of IA5StringConstraint
    | StrRootConstraint2               of IA5StringConstraint*IA5StringConstraint
    | StrSingleValueConstraint         of string*ReferenceToValue option
    | StrSizeContraint                 of PosIntTypeConstraint               
    | AlphabetContraint                of CharTypeConstraint           

type OctetStringConstraint  =    SizableTypeConstraint<list<byte>>
type BitStringConstraint    =    SizableTypeConstraint<string>
type BoolConstraint         =    GenericConstraint<bool>
type EnumConstraint         =    GenericConstraint<string>


type SequenceOfConstraint   =     SizableTypeConstraint<list<ReferenceToValue>>
type SequenceConstraint     =     GenericConstraint<list<string*ReferenceToValue>>
type ChoiceConstraint       =     GenericConstraint<string*ReferenceToValue>


let foldGenericConstraint unionFunc intersectionFunc allExceptFunc exceptFunc rootFunc rootFunc2 singleValueFunc 
    (c:GenericConstraint<'v>) 
    (s:'UserState) =
    let rec loopRecursiveConstraint (c:GenericConstraint<'v>) (s0:'UserState) =
        match c with
        | UnionConstraint(c1,c2,b)         -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            unionFunc nc1 nc2 b s2
        | IntersectionConstraint(c1,c2)    -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            intersectionFunc nc1 nc2 s2
        | AllExceptConstraint(c1)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            allExceptFunc nc1 s1
        | ExceptConstraint(c1,c2)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            exceptFunc nc1 nc2 s2
        | RootConstraint(c1)               -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            rootFunc nc1 s1
        | RootConstraint2(c1,c2)           -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            rootFunc2 nc1 nc2 s2
        | SingleValueConstraint (v, rv)    -> singleValueFunc v rv s0
    loopRecursiveConstraint c s


let foldRangeTypeConstraint unionFunc intersectionFunc allExceptFunc exceptFunc rootFunc rootFunc2 singleValueFunc 
    rangeFunc range_val_max_func range_min_val_func
    (c:RangeTypeConstraint<'v,'vr>) 
    (s:'UserState) =
    let rec loopRecursiveConstraint (c:RangeTypeConstraint<'v,'vr>) (s0:'UserState) =
        match c with
        | RangeUnionConstraint(c1,c2,b)         -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            unionFunc nc1 nc2 b s2
        | RangeIntersectionConstraint(c1,c2)    -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            intersectionFunc nc1 nc2 s2
        | RangeAllExceptConstraint(c1)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            allExceptFunc nc1 s1
        | RangeExceptConstraint(c1,c2)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            exceptFunc nc1 nc2 s2
        | RangeRootConstraint(c1)               -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            rootFunc nc1 s1
        | RangeRootConstraint2(c1,c2)           -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            rootFunc2 nc1 nc2 s2
        | RangeSingleValueConstraint (v, rv)            -> singleValueFunc v rv s0
        | RangeContraint((v1,rv1), (v2,rv2), b1,b2)     -> rangeFunc v1 v2 b1 b2 s
        | RangeContraint_val_MAX ((v,rv), b)            -> range_val_max_func v b s
        | RangeContraint_MIN_val ((v,rv), b)            -> range_min_val_func v b s
    loopRecursiveConstraint c s

let foldSizableTypeConstraint unionFunc intersectionFunc allExceptFunc exceptFunc rootFunc rootFunc2 singleValueFunc 
    sunionFunc sintersectionFunc sallExceptFunc sexceptFunc srootFunc srootFunc2 ssingleValueFunc 
    srangeFunc srange_val_max_func srange_min_val_func
    (c:SizableTypeConstraint<'v>) 
    (s:'UserState) =
    let rec loopRecursiveConstraint (c:SizableTypeConstraint<'v>) (s0:'UserState) =
        match c with
        | SizeUnionConstraint(c1,c2,b)         -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            unionFunc nc1 nc2 b s2
        | SizeIntersectionConstraint(c1,c2)    -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            intersectionFunc nc1 nc2 s2
        | SizeAllExceptConstraint(c1)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            allExceptFunc nc1 s1
        | SizeExceptConstraint(c1,c2)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            exceptFunc nc1 nc2 s2
        | SizeRootConstraint(c1)               -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            rootFunc nc1 s1
        | SizeRootConstraint2(c1,c2)           -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            rootFunc2 nc1 nc2 s2
        | SizeSingleValueConstraint (v, rv)    -> singleValueFunc v rv s0
        | SizeContraint    intCon   -> foldRangeTypeConstraint sunionFunc sintersectionFunc sallExceptFunc sexceptFunc srootFunc srootFunc2 ssingleValueFunc srangeFunc srange_val_max_func srange_min_val_func intCon s
    loopRecursiveConstraint c s

let foldSizableTypeConstraint2 unionFunc intersectionFunc allExceptFunc exceptFunc rootFunc rootFunc2 singleValueFunc 
    foldRangeTypeConstraint
    (c:SizableTypeConstraint<'v>) 
    (s:'UserState) =
    let rec loopRecursiveConstraint (c:SizableTypeConstraint<'v>) (s0:'UserState) =
        match c with
        | SizeUnionConstraint(c1,c2,b)         -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            unionFunc nc1 nc2 b s2
        | SizeIntersectionConstraint(c1,c2)    -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            intersectionFunc nc1 nc2 s2
        | SizeAllExceptConstraint(c1)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            allExceptFunc nc1 s1
        | SizeExceptConstraint(c1,c2)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            exceptFunc nc1 nc2 s2
        | SizeRootConstraint(c1)               -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            rootFunc nc1 s1
        | SizeRootConstraint2(c1,c2)           -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            rootFunc2 nc1 nc2 s2
        | SizeSingleValueConstraint (v, rv)    -> singleValueFunc v rv s0
        | SizeContraint    intCon   -> foldRangeTypeConstraint intCon s0
    loopRecursiveConstraint c s


let foldStringTypeConstraint unionFunc intersectionFunc allExceptFunc exceptFunc rootFunc rootFunc2 singleValueFunc 
    sunionFunc sintersectionFunc sallExceptFunc sexceptFunc srootFunc srootFunc2 ssingleValueFunc srangeFunc srange_val_max_func srange_min_val_func
    aunionFunc aintersectionFunc aallExceptFunc aexceptFunc arootFunc arootFunc2 asingleValueFunc arangeFunc arange_val_max_func arange_min_val_func 
    (c:IA5StringConstraint) 
    (s:'UserState) =
    let rec loopRecursiveConstraint (c:IA5StringConstraint) (s0:'UserState) =
        match c with
        | StrUnionConstraint(c1,c2,b)         -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            unionFunc nc1 nc2 b s2
        | StrIntersectionConstraint(c1,c2)    -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            intersectionFunc nc1 nc2 s2
        | StrAllExceptConstraint(c1)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            allExceptFunc nc1 s1
        | StrExceptConstraint(c1,c2)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            exceptFunc nc1 nc2 s2
        | StrRootConstraint(c1)               -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            rootFunc nc1 s1
        | StrRootConstraint2(c1,c2)           -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            rootFunc2 nc1 nc2 s2
        | StrSingleValueConstraint (v, rv)    -> singleValueFunc v rv s0
        | StrSizeContraint        intCon   -> foldRangeTypeConstraint sunionFunc sintersectionFunc sallExceptFunc sexceptFunc srootFunc srootFunc2 ssingleValueFunc srangeFunc srange_val_max_func srange_min_val_func intCon s
        | AlphabetContraint       alphaCon -> foldRangeTypeConstraint aunionFunc aintersectionFunc aallExceptFunc aexceptFunc arootFunc arootFunc2 asingleValueFunc arangeFunc arange_val_max_func arange_min_val_func alphaCon s        
    loopRecursiveConstraint c s


let foldStringTypeConstraint2 unionFunc intersectionFunc allExceptFunc exceptFunc rootFunc rootFunc2 singleValueFunc 
    foldRangeSizeConstraint foldRangeAlphaConstraint
    (c:IA5StringConstraint) 
    (s:'UserState) =
    let rec loopRecursiveConstraint (c:IA5StringConstraint) (s0:'UserState) =
        match c with
        | StrUnionConstraint(c1,c2,b)         -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            unionFunc nc1 nc2 b s2
        | StrIntersectionConstraint(c1,c2)    -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            intersectionFunc nc1 nc2 s2
        | StrAllExceptConstraint(c1)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            allExceptFunc nc1 s1
        | StrExceptConstraint(c1,c2)          -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            exceptFunc nc1 nc2 s2
        | StrRootConstraint(c1)               -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            rootFunc nc1 s1
        | StrRootConstraint2(c1,c2)           -> 
            let nc1, s1 = loopRecursiveConstraint c1 s0
            let nc2, s2 = loopRecursiveConstraint c2 s1
            rootFunc2 nc1 nc2 s2
        | StrSingleValueConstraint (v, rv)    -> singleValueFunc v rv s0
        | StrSizeContraint        intCon   -> foldRangeSizeConstraint  intCon s
        | AlphabetContraint       alphaCon -> foldRangeAlphaConstraint alphaCon s        
    loopRecursiveConstraint c s
        


// Calcualate uPER range 

