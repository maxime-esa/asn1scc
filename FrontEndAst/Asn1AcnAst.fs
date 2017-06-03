module Asn1AcnAst

open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils
open CommonTypes






/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ACN PROPERTIES DEFINITION ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type RelativePath = 
    | RelativePath of string list


type AcnEndianness =
    | LittleEndianness
    | BigEndianness            

type AcnAligment = 
    | NextByte
    | NextWord
    | NextDWord

// present when property defintion
// this property is not part of the ACN type itself but part of the AcnChildInfo
type AcnPresentWhenConditionSeqChild =
    | PresenceBool  of RelativePath                         

type AcnPresentWhenConditionChoiceChild =
    | PresenceInt   of RelativePath*BigInteger              
    | PresenceStr   of RelativePath*string                  

// Integer acn properties
type AcnIntSizeProperty =
    | Fixed                 of BigInteger
    | IntNullTerminated     of byte      //termination character when encoding is ASCII

type AcnIntEncoding =
    | PosInt
    | TwosComplement
    | IntAscii
    | BCD


type IntegerAcnProperties = {
    encodingProp    : AcnIntEncoding        option
    sizeProp        : AcnIntSizeProperty    option
    endiannessProp  : AcnEndianness         option
}

type EnumeratedRedefinedValue = {
    enumName    : string
    enumValue   : BigInteger
}

type EnumeratedAcnProperties = {
    encodingProp    : AcnIntEncoding            option
    sizeProp        : AcnIntSizeProperty        option
    endiannessProp  : AcnEndianness             option
    encodeValues    : bool                      option
    redefinedValues : (EnumeratedRedefinedValue  list) option
}


// Real acn properties
type AcnRealEncoding =
    | IEEE754_32
    | IEEE754_64

type RealAcnProperties = {
    encodingProp    : AcnRealEncoding       option
    endiannessProp  : AcnEndianness         option
}

// String acn properties
type AcnStringSizeProperty =
    | StrExternalField   of RelativePath
    | StrNullTerminated  of byte      //termination character when encoding is ASCII

type AcnStringEncoding =
    | StrAscii

type StringAcnProperties = {
    encodingProp    : AcnStringEncoding     option
    sizeProp        : AcnStringSizeProperty option
}


type SizeableAcnProperties = {
    sizeProp        : RelativePath          option
}


type NullTypeAcnProperties = {
    encodingPattern     : StringLoc             option
}

type AcnBooleanEncoding =
    | TrueValue    of StringLoc    
    | FalseValue   of StringLoc

type BooleanAcnProperties = {
    encodingPattern     : AcnBooleanEncoding    option
}

type ChoiceAcnProperties = {
    enumDeterminant     : RelativePath              option
}


(*
type GenericTypeAcnProperties =
    | IntegerAcnProperties          of IntegerAcnProperties    
    | EnumeratedAcnProperties       of EnumeratedAcnProperties
    | RealAcnProperties             of RealAcnProperties
    | StringAcnProperties           of StringAcnProperties
    | OctetStringAcnProperties      of SizeableAcnProperties
    | BitStringAcnProperties        of SizeableAcnProperties
    | NullTypeAcnProperties         of NullTypeAcnProperties
    | BooleanAcnProperties          of BooleanAcnProperties
    | SequenceOfAcnProperties       of SizeableAcnProperties
    | ChoiceAcnProperties           of ChoiceAcnProperties
    | SequenceAcnProperties         of SequenceAcnProperties
    | ReferenceTypeAcnProperties    of GenericTypeAcnProperties*(ChildInfoAcnProperties list)

and ChildInfoAcnProperties = {
    name                : string
    presentWhen         : AcnPresentWhenCondition   list
    prop                : GenericTypeAcnProperties
}     
*)

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ACN PARAMETERS DEFINITION ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type AcnAsn1Type =
    | AcnInteger    of SrcLoc
    | AcnBoolean    of SrcLoc
    | AcnNullType   of SrcLoc
    | AcnRefType    of StringLoc*StringLoc

type AcnParameter = {
    name        : string
    asn1Type    : AcnAsn1Type
    loc         : SrcLoc
}

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
    | SizeContraint                     of Asn1Constraint               
    | AlphabetContraint                 of Asn1Constraint           
    | UnionConstraint                   of Asn1Constraint*Asn1Constraint*bool //left,righ, virtual constraint
    | IntersectionConstraint            of Asn1Constraint*Asn1Constraint
    | AllExceptConstraint               of Asn1Constraint
    | ExceptConstraint                  of Asn1Constraint*Asn1Constraint
    | RootConstraint                    of Asn1Constraint
    | RootConstraint2                   of Asn1Constraint*Asn1Constraint

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



/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ASN1 WITH ACN INFORMATION  DEFINITION    /////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type Integer = {
    acnProperties   : IntegerAcnProperties
}

type Real = {
    acnProperties   : RealAcnProperties
}

type IA5String = {
    acnProperties   : StringAcnProperties
}

type NumericString = {
    acnProperties   : StringAcnProperties
}

type OctetString = {
    acnProperties   : SizeableAcnProperties
}

type BitString = {
    acnProperties   : SizeableAcnProperties
}

type NullType = {
    acnProperties   : NullTypeAcnProperties
}

type Boolean = {    
    acnProperties   : BooleanAcnProperties
}

type Asn1Type = {
    Kind            : Asn1TypeKind;
    Constraints     : Asn1Constraint list
    acnAligment     : AcnAligment           option
    Location        : SrcLoc //Line no, Char pos
}


and Asn1TypeKind =
    | Integer           of Integer
    | Real              of Real
    | IA5String         of IA5String
    | NumericString     of NumericString
    | OctetString       of OctetString
    | NullType          of NullType
    | BitString         of BitString
    | Boolean           of Boolean
    | Enumerated        of list<NamedItem>
    | SequenceOf        of Asn1Type
    | Sequence          of SeqChildInfo list
    | Choice            of ChChildInfo list
    | ReferenceType     of ReferenceType

and SequenceOf = {
    child           : Asn1Type
    acnProperties   : SizeableAcnProperties
}

and Sequence = {
    children        : SeqChildInfo list
}

and SeqChildInfo = {
    Name                        : StringLoc
    c_name                      : string
    ada_name                    : string                     
    Type                        : Asn1Type
    Optionality                 : Asn1Optionality option
    acnPresentWhenConditions    : AcnPresentWhenConditionSeqChild list
    AcnInsertedField            : bool
    Comments                    : string array
}

and Choice = {
    acnProperties   : ChoiceAcnProperties
}

and ChChildInfo = {
    Name                        : StringLoc
    c_name                      : string
    ada_name                    : string                     
    present_when_name           : string // Does not contain the "_PRESENT". Not to be used directly by backends.
    Type                        : Asn1Type
    acnPresentWhenConditions    : AcnPresentWhenConditionChoiceChild list
    Comments                    : string array
}

and ReferenceType = {
    modName     : StringLoc
    tasName     : StringLoc
    tabularized : bool
    acnArguments: RelativePath list
    baseType    : Asn1Type
}


type TypeAssignment = {
    Name:StringLoc
    c_name:string
    ada_name:string
    Type:Asn1Type
    Comments: string array
    acnParameters   : AcnParameter list

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
    acnConstants : Map<string, BigInteger>
    args:CommandLineSettings
}


(*

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
*)