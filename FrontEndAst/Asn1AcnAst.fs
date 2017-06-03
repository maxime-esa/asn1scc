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
    | PresenceInt   of RelativePath*IntLoc
    | PresenceStr   of RelativePath*StringLoc

// Integer acn properties
type AcnIntSizeProperty =
    | Fixed                 of IntLoc
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


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ACN PARAMETERS DEFINITION ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type AcnParamType =
    | AcnPrmInteger    of SrcLoc
    | AcnPrmBoolean    of SrcLoc
    | AcnPrmNullType   of SrcLoc
    | AcnPrmRefType    of StringLoc*StringLoc

type AcnParameter = {
    name        : string
    asn1Type    : AcnParamType
    loc         : SrcLoc
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ASN1 VALUES DEFINITION    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type Asn1Value = Asn1Ast.Asn1Value

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
    definitionValue : BigInteger          // the value in the header file
    
    // the value encoded by ACN. It can (a) the named item index (i.e. like uper), (b) The definition value, (c) The redefined value from acn properties
    acnEncodeValue  : BigInteger                
    Comments: string array
}

type Asn1Optionality = Asn1Ast.Asn1Optionality



/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ASN1 WITH ACN INFORMATION  DEFINITION    /////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////




type Integer = {
    acnProperties   : IntegerAcnProperties
    constraints     : Asn1Constraint list
}

type Real = {
    acnProperties   : RealAcnProperties
    constraints     : Asn1Constraint list
}

type StringType = {
    acnProperties   : StringAcnProperties
    constraints     : Asn1Constraint list
}


type OctetString = {
    acnProperties   : SizeableAcnProperties
    constraints     : Asn1Constraint list
}

type BitString = {
    acnProperties   : SizeableAcnProperties
    constraints     : Asn1Constraint list
}

type NullType = {
    acnProperties   : NullTypeAcnProperties
    constraints     : Asn1Constraint list
}

type Boolean = {    
    acnProperties   : BooleanAcnProperties
    constraints     : Asn1Constraint list
}

type Enumerated = {
    items           : NamedItem list
    acnProperties   : IntegerAcnProperties
    constraints     : Asn1Constraint list
}

type AcnInsertedType = 
    | AcnInteger           of IntegerAcnProperties   *(AcnAligment option)
    | AcnNullType          of NullTypeAcnProperties  *(AcnAligment option)
    | AcnBoolean           of BooleanAcnProperties   *(AcnAligment option)

type AcnChild = {
    Name                        : StringLoc
    Type                        : AcnInsertedType
}


type Asn1Type = {
    Kind            : Asn1TypeKind
    acnAligment     : AcnAligment option
    Location        : SrcLoc //Line no, Char pos
}


and Asn1TypeKind =
    | Integer           of Integer
    | Real              of Real
    | IA5String         of StringType
    | NumericString     of StringType
    | OctetString       of OctetString
    | NullType          of NullType
    | BitString         of BitString
    | Boolean           of Boolean
    | Enumerated        of Enumerated
    | SequenceOf        of SequenceOf
    | Sequence          of Sequence
    | Choice            of Choice
    | ReferenceType     of ReferenceType

and SequenceOf = {
    child           : Asn1Type
    acnProperties   : SizeableAcnProperties
    constraints     : Asn1Constraint list
}

and Sequence = {
    children        : SeqChildInfo list
    constraints     : Asn1Constraint list
}


and SeqChildInfo = 
    | Asn1Child of Asn1Child
    | AcnChild  of AcnChild

and Asn1Child = {
    Name                        : StringLoc
    c_name                      : string
    ada_name                    : string                     
    Type                        : Asn1Type
    Optionality                 : Asn1Optionality option
    acnPresentWhenConditions    : AcnPresentWhenConditionSeqChild list
    Comments                    : string array
}




and Choice = {
    children        : ChChildInfo list
    acnProperties   : ChoiceAcnProperties
    constraints     : Asn1Constraint list
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


type Asn1Module = {
    Name : StringLoc
    TypeAssignments : list<TypeAssignment>
    ValueAssignments : list<Asn1Ast.ValueAssignment>
    Imports : list<Asn1Ast.ImportedModule>
    Exports : Asn1Ast.Exports
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