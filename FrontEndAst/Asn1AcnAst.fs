module Asn1AcnAst

open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open System
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

type IntegerValue         = IntLoc
type RealValue            = DoubleLoc
type StringValue          = StringLoc
type BooleanValue         = BoolLoc
type BitStringValue       = StringLoc
type OctetStringValue     = list<ByteLoc>
type EnumValue            = StringLoc
type SeqOfValue           = list<Asn1Value>
and SeqValue              = list<NamedValue>
and ChValue               = NamedValue
and RefValue              = ((StringLoc*StringLoc)*Asn1Value)

and NamedValue = {
    name        : StringLoc
    Value       : Asn1Value
}

and Asn1Value =
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
    | NullValue             
    | RefValue              of RefValue   


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ASN1 CONSTRAINTS DEFINITION    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


type GenericConstraint<'v> =
    | UnionConstraint                   of GenericConstraint<'v>*GenericConstraint<'v>*bool //left,righ, virtual constraint
    | IntersectionConstraint            of GenericConstraint<'v>*GenericConstraint<'v>
    | AllExceptConstraint               of GenericConstraint<'v>
    | ExceptConstraint                  of GenericConstraint<'v>*GenericConstraint<'v>
    | RootConstraint                    of GenericConstraint<'v>
    | RootConstraint2                   of GenericConstraint<'v>*GenericConstraint<'v>
    | SingleValueConstraint             of 'v

type RangeTypeConstraint<'v1,'v2>  = 
    | RangeUnionConstraint               of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>*bool //left,righ, virtual constraint
    | RangeIntersectionConstraint        of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>
    | RangeAllExceptConstraint           of RangeTypeConstraint<'v1,'v2>
    | RangeExceptConstraint              of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>
    | RangeRootConstraint                of RangeTypeConstraint<'v1,'v2>
    | RangeRootConstraint2               of RangeTypeConstraint<'v1,'v2>*RangeTypeConstraint<'v1,'v2>
    | RangeSingleValueConstraint         of 'v2
    | RangeContraint                     of ('v1) *('v1)*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX             of ('v1) *bool            //min, InclusiveMin(=true)
    | RangeContraint_MIN_val             of ('v1) *bool            //max, InclusiveMax(=true)

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
    | SizeSingleValueConstraint         of 'v
    | SizeContraint                     of PosIntTypeConstraint               

type IA5StringConstraint = 
    | StrUnionConstraint               of IA5StringConstraint*IA5StringConstraint*bool //left,righ, virtual constraint
    | StrIntersectionConstraint        of IA5StringConstraint*IA5StringConstraint
    | StrAllExceptConstraint           of IA5StringConstraint
    | StrExceptConstraint              of IA5StringConstraint*IA5StringConstraint
    | StrRootConstraint                of IA5StringConstraint
    | StrRootConstraint2               of IA5StringConstraint*IA5StringConstraint
    | StrSingleValueConstraint         of string
    | StrSizeContraint                 of PosIntTypeConstraint               
    | AlphabetContraint                of CharTypeConstraint           

type OctetStringConstraint  =    SizableTypeConstraint<OctetStringValue>
type BitStringConstraint    =    SizableTypeConstraint<BitStringValue>
type BoolConstraint         =    GenericConstraint<bool>
type EnumConstraint         =    GenericConstraint<string>


type SequenceOfConstraint   =     SizableTypeConstraint<SeqOfValue>
type SequenceConstraint     =     GenericConstraint<SeqValue>
type ChoiceConstraint       =     GenericConstraint<ChValue>


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
    cons            : IntegerTypeConstraint list
    withcons        : IntegerTypeConstraint list
}

type Real = {
    acnProperties   : RealAcnProperties
    cons                : RealTypeConstraint list
    withcons            : RealTypeConstraint list
}

type StringType = {
    acnProperties   : StringAcnProperties
    cons                : IA5StringConstraint list
    withcons            : IA5StringConstraint list
}


type OctetString = {
    acnProperties   : SizeableAcnProperties
    cons                : OctetStringConstraint list
    withcons            : OctetStringConstraint list
}

type BitString = {
    acnProperties   : SizeableAcnProperties
    cons                : BitStringConstraint list
    withcons            : BitStringConstraint list
}

type NullType = {
    acnProperties   : NullTypeAcnProperties
}

type Boolean = {    
    acnProperties   : BooleanAcnProperties
    cons                : BoolConstraint list
    withcons            : BoolConstraint list
}

type Enumerated = {
    items           : NamedItem list
    acnProperties   : IntegerAcnProperties
    cons                : EnumConstraint list
    withcons            : EnumConstraint list
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
    cons                : SequenceOfConstraint list
    withcons            : SequenceOfConstraint list
}

and Sequence = {
    children        : SeqChildInfo list
    cons                : SequenceConstraint list
    withcons            : SequenceConstraint list
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
    cons            : ChoiceConstraint list
    withcons        : ChoiceConstraint list
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


type Asn1Module = {
    Name : StringLoc
    TypeAssignments : list<TypeAssignment>
    ValueAssignments : list<ValueAssignment>
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



let rec getASN1Name  (t:Asn1Type) =
    match t.Kind with
    | Integer       _  -> "INTEGER"
    | Real          _  -> "REAL"
    | IA5String     _  -> "IA5String"
    | NumericString _  -> "NumericString"
    | OctetString   _  -> "OCTET STRING"
    | NullType      _  -> "NULL"
    | BitString     _  -> "BIT STRING"
    | Boolean       _  -> "BOOLEAN"
    | Enumerated    _  -> "ENUMERATED"
    | SequenceOf    _  -> "SEQUENCE OF"
    | Sequence      _  -> "SEQUENCE"
    | Choice        _  -> "CHOICE"
    | ReferenceType r  -> getASN1Name r.baseType
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