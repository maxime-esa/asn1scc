module CAst
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils


type ReferenceToValue       = BAst.ReferenceToValue
type ReferenceToType        = BAst.ReferenceToType
type ReferenceToAcnParam    = string*string*string
type ReferenceToAcnTempType = string*string*string

type GenericReference       =
    | RefToType             of GenericFold2.ScopeNode list
    | RefToAcnParam         of string*string*string
    | RefToAcnTempType      of string*string*string



type AcnParameter = {
    id : ReferenceToAcnParam
    Asn1Type: AcnTypes.AcnAsn1Type
    Mode    : AcnTypes.ParamMode
}

type AcnTempType = {
    id : ReferenceToAcnTempType
    Asn1Type: AcnTypes.AcnAsn1Type
}

type AcnLinkKind = AcnTypes.LongReferenceKind
type AcnLink = {
    decType      : GenericReference
    determinant  : GenericReference
    Kind : AcnLinkKind
}

type Asn1Optionality        = BAst.Asn1Optionality
type AcnAligment            = AcnTypes.aligment
type AcnBooleanEncoding     = AcnTypes.booleanEncoding
type AcnNullEncodingPattern = AcnNullEncodingPattern of string
type AcnEndianness          = AcnTypes.endianness



type ChildInfo = {
    Name                    : string;
    refToType               : ReferenceToType;
    Optionality             : Asn1Optionality option
    AcnInsertedField        : bool
    Comments                : string array
}

(*INTEGER*)

type AcnIntEncoding         = 
    | PosInt
    | TwosComplement
    | Ascii
    | BCD
type AcnIntSize =
    | Fixed             of BigInteger
    | NullTerminated    of byte      //termination character

type UperIntRange           = Ast.uperRange<BigInteger>

type IntegerType = {
    uperRange               : UperIntRange
    acnEndianness           : AcnEndianness
    acnIntEncoding          : AcnIntEncoding
    acnIntSize              : AcnIntSize
}

(* REAL *)
type AcnRealEncoding        = 
    | IEEE754_32
    | IEEE754_64
type UperDblRange           = Ast.uperRange<double>
type RealType = {
    uperRange               : UperDblRange
    acnEndianness           : AcnEndianness 
    acnRealEncoding         : AcnRealEncoding option
}


(* ENUMERATED *)
type EnumItem = {
    name                    : string
    asn1value               : BigInteger    // the value provided (or implied) in the ASN.1 grammar. This value is used in the type definition.
    uperValue               : BigInteger    // the value encoded by uPER    - this is always the index of the enum item
    acnValue                : BigInteger    // the value encoded by ACN. This value is calculated as follows:     
                                            //    if acn attribute ENCODE_VALUES is NOT present then 
                                            //        this the uPER value (i.e. index of the enum item
                                            //    else 
                                            //        if value is redefined in ACN the redefined values else the ASN.1 value
    comments                : string list
}

type EnumeratedType = {
    acnEndianness           : AcnEndianness
    acnIntEncoding          : AcnIntEncoding
    acnIntSize              : AcnIntSize
    acnEncodeValues         : bool      //if true values are encoded, not indexes
    items                   : EnumItem list

    hasAsn1Values           : bool  //if hasAsn1Values=false then the ASN.1 defintion had no int values associated with the items. e.g. ENUMERATED {red,gren} and not ENUMERATED {red(10),gren(20)}
}


type Asn1TypeKind =
    | Integer           of IntegerType
    | Real              of RealType
    | NullType          of AcnNullEncodingPattern     
    | Boolean           of AcnBooleanEncoding
    | Enumerated        of EnumeratedType
    | IA5String
    | OctetString 
    | BitString
    | SequenceOf        of ReferenceToType
    | Sequence          of list<ChildInfo>
    | Choice            of list<ChildInfo>


type Asn1Constraint = 
    | SingleValueContraint              of ReferenceToValue             
    | RangeContraint                    of ReferenceToValue*ReferenceToValue*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX            of ReferenceToValue*bool         //min, InclusiveMin(=true)
    | RangeContraint_MIN_val            of ReferenceToValue*bool         //max, InclusiveMax(=true)
    | SizeContraint                     of Asn1Constraint               
    | AlphabetContraint                 of Asn1Constraint           
    | UnionConstraint                   of Asn1Constraint*Asn1Constraint*bool //left,righ, virtual constraint
    | IntersectionConstraint            of Asn1Constraint*Asn1Constraint
    | AllExceptConstraint               of Asn1Constraint
    | ExceptConstraint                  of Asn1Constraint*Asn1Constraint
    | RootConstraint                    of Asn1Constraint
    | RootConstraint2                   of Asn1Constraint*Asn1Constraint


type Asn1Type = {
    asn1Name : string option
    id : ReferenceToType
    baseTypeId : ReferenceToType option     // base type
    Kind:Asn1TypeKind
    Constraints:list<Asn1Constraint>;
    FromWithCompConstraints:list<Asn1Constraint>
    acnAligment : AcnAligment option
}
