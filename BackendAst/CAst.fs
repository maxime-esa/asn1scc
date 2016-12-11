module CAst
open System
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
    acnIntEncoding          : AcnIntEncoding option
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


type Asn1Constraint = BAst.Asn1Constraint


type Asn1Type = {
    asn1Name : string option
    id : ReferenceToType
    baseTypeId : ReferenceToType option     // base type
    Kind:Asn1TypeKind
    Constraints:list<Asn1Constraint>;
    FromWithCompConstraints:list<Asn1Constraint>
    acnAligment : AcnAligment option
}

type Asn1File = BAst.Asn1File
type Asn1Value = BAst.Asn1Value

type AstRoot = {
    Files: list<Asn1File>
    Encodings:list<Ast.Asn1Encoding>
    GenerateEqualFunctions:bool
    TypePrefix:string
    AstXmlAbsFileName:string
    IcdUperHtmlFileName:string
    IcdAcnHtmlFileName:string
    CheckWithOss:bool
    mappingFunctionsModule : string option
    valsMap : Map<ReferenceToValue, Asn1Value>
    typesMap : Map<ReferenceToType, Asn1Type>
    TypeAssignments : list<Asn1Type>
    ValueAssignments : list<Asn1Value>
}


let mapBastToCast0 (r:BAst.AstRoot) (c:AcnTypes.AcnAst) : unit=
    printfn "ASN1"
    r.TypeAssignments |> List.map(fun s -> s.id.ToString()) |> Seq.iter (printfn "%s")
    printfn "ACN TYPES"
    c.Types|> List.map(fun s -> s.TypeID |> Seq.StrJoin ".") |> Seq.iter (printfn "%s")
    
    (*
let createInteger (acnProps:AcnTypes.AcnProperty list) =
    {
        IntegerType.uperRange   = uperRange
        acnEndianness           = Acn.GetEndianess acnProps
        acnIntEncoding          = 
            match Acn.GetEncodingProperty acnProps with
            | None          -> None
            | Some (AcnTypes.encoding.PosInt)   -> Some PosInt
            | Some (AcnTypes.encoding.TwosComplement)   -> Some TwosComplement
            | Some (AcnTypes.encoding.BCD)   -> Some BCD
            | Some (AcnTypes.encoding.Ascii)   -> Some Ascii
            | Some (AcnTypes.encoding.IEEE754_32)   -> Some Ascii
            | Some (AcnTypes.encoding.IEEE754_64)   -> Some Ascii


        acnIntSize              = acnIntSize
    }
    *)
let mapBastToCast (r:BAst.AstRoot) (c:AcnTypes.AcnAst): AstRoot=
    let acnMap = c.Types |> List.map(fun s -> s.TypeID |> Seq.StrJoin ".", s) |> Map.ofList
    let mapType (t:BAst.Asn1Type) : Asn1Type =
        let acnProps = 
            match acnMap.TryFind (t.id.ToString()) with
            | None  -> []
            | Some acnT -> acnT.Properties
        raise(Exception "")
    let newTypes = r.TypeAssignments |> List.map mapType
    {
        AstRoot.Files = r.Files
        Encodings = r.Encodings
        GenerateEqualFunctions = r.GenerateEqualFunctions
        TypePrefix = r.TypePrefix
        AstXmlAbsFileName = r.AstXmlAbsFileName
        IcdUperHtmlFileName = r.IcdUperHtmlFileName
        IcdAcnHtmlFileName = r.IcdUperHtmlFileName
        CheckWithOss = r.CheckWithOss
        mappingFunctionsModule = r.mappingFunctionsModule
        valsMap = r.valsMap
        typesMap = newTypes |> List.map(fun x -> x.id, x) |> Map.ofList
        TypeAssignments = newTypes
        ValueAssignments = r.ValueAssignments
    }    