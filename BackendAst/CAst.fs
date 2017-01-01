module CAst
open System
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils
open Constraints
open uPER2


type AcnAsn1Type =
    | AcnInteger
    | AcnBoolean

type ParamMode =
    | DecodeMode
    | EncodeDecodeMode

type AcnTempType = {                // this type is not encoded decoded. It is declared locally at the tas level
                                    // and it is used for passing values
    modName     : string
    tasName     : string
    mame        : string
    asn1Type    : AcnAsn1Type
}

type AcnParameter = {
    modName : string
    tasName : string
    name    : string
    asn1Type: AcnAsn1Type
    mode    : ParamMode
    location : SrcLoc
}

type Integer = {
    //bast inherrited properties
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : IntegerTypeConstraint list
    withcons            : IntegerTypeConstraint list
    uperRange           : uperRange<BigInteger>
    baseType            : Integer option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    acnEncodingClass    : Acn.IntEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

type Real = {
    //bast inherrited properties
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : RealTypeConstraint list
    withcons            : RealTypeConstraint list
    uperRange           : uperRange<double>
    baseType            : Real option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    acnEncodingClass    : Acn.RealEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons


type StringEncodingClassKind =
    | Acn_Enc_String_Ascii_FixSize                                            //
    | Acn_Enc_String_Ascii_Null_Teminated                   of byte           //null character
    | Acn_Enc_String_Ascii_External_Field_Determinant       of AcnTypes.Point //external field
    | Acn_Enc_String_Ascii_Internal_Field_Determinant                         // this case is like uPER except that the ASCII value (8 bits) of the character is encoded and also no fragmentation
    | Acn_Enc_String_CharIndex_FixSize                      
    | Acn_Enc_String_CharIndex_External_Field_Determinant   of AcnTypes.Point //external field
    | Acn_Enc_String_CharIndex_Internal_Field_Determinant                     // this case is almost like uPER (except of fragmentation)


type StringType = {
    //bast inherrited properties
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : IA5StringConstraint list
    withcons            : IA5StringConstraint list
    minSize             : int
    maxSize             : int
    charSet             : char array
    baseType            : StringType option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

type EnumItem = {
    name        : string
    Value       : BigInteger
    comments    : string list
}

type Enumerated = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    items               : EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : EnumConstraint list
    withcons            : EnumConstraint list
    baseType            : Enumerated option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons
        

type Boolean = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : BoolConstraint list
    withcons            : BoolConstraint list
    baseType            : Boolean option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons
 

type OctetString = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : OctetStringConstraint list
    withcons            : OctetStringConstraint list
    minSize             : int
    maxSize             : int
    baseType            : OctetString option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons

type NullType = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    baseType            : NullType option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}

type BitString = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : BitStringConstraint list
    withcons            : BitStringConstraint list
    minSize             : int
    maxSize             : int
    baseType            : BitString option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons

type Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of Asn1GenericValue

type SequenceOf = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    childType           : Asn1Type
    cons                : SequenceOfConstraint list
    withcons            : SequenceOfConstraint list
    minSize             : int
    maxSize             : int
    baseType            : SequenceOf option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons

and ChildInfo = {
    Name                :string
    chType              :Asn1Type
    Optionality         :Asn1Optionality option
    Comments            :string list
}

and Sequence = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    children            : ChildInfo list
    cons                : SequenceConstraint list
    withcons            : SequenceConstraint list
    baseType            : Sequence option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons

and Choice = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    children            : ChildInfo list
    cons                : ChoiceConstraint list
    withcons            : ChoiceConstraint list
    baseType            : Choice option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons



and Asn1Type =
    | Integer           of Integer
    | Real              of Real
    | IA5String         of StringType
    | OctetString       of OctetString
    | NullType          of NullType
    | BitString         of BitString
    | Boolean           of Boolean
    | Enumerated        of Enumerated
    | SequenceOf        of SequenceOf
    | Sequence          of Sequence
    | Choice            of Choice
with
    member this.id =
        match this with
        | Integer      t -> t.id
        | Real         t -> t.id
        | IA5String    t -> t.id
        | OctetString  t -> t.id
        | NullType     t -> t.id
        | BitString    t -> t.id
        | Boolean      t -> t.id
        | Enumerated   t -> t.id
        | SequenceOf   t -> t.id
        | Sequence     t -> t.id
        | Choice       t -> t.id
    member this.baseType =
        match this with
        | Integer      t -> t.baseType |> Option.map Integer     
        | Real         t -> t.baseType |> Option.map Real        
        | IA5String    t -> t.baseType |> Option.map IA5String   
        | OctetString  t -> t.baseType |> Option.map OctetString 
        | NullType     t -> t.baseType |> Option.map NullType    
        | BitString    t -> t.baseType |> Option.map BitString   
        | Boolean      t -> t.baseType |> Option.map Boolean     
        | Enumerated   t -> t.baseType |> Option.map Enumerated  
        | SequenceOf   t -> t.baseType |> Option.map SequenceOf  
        | Sequence     t -> t.baseType |> Option.map Sequence    
        | Choice       t -> t.baseType |> Option.map Choice      
    member this.uperMaxSizeInBits =
        match this with
        | Integer      t -> t.uperMaxSizeInBits
        | Real         t -> t.uperMaxSizeInBits
        | IA5String    t -> t.uperMaxSizeInBits
        | OctetString  t -> t.uperMaxSizeInBits
        | NullType     t -> t.uperMaxSizeInBits
        | BitString    t -> t.uperMaxSizeInBits
        | Boolean      t -> t.uperMaxSizeInBits
        | Enumerated   t -> t.uperMaxSizeInBits
        | SequenceOf   t -> t.uperMaxSizeInBits
        | Sequence     t -> t.uperMaxSizeInBits
        | Choice       t -> t.uperMaxSizeInBits
    member this.uperMinSizeInBits =
        match this with
        | Integer      t -> t.uperMinSizeInBits
        | Real         t -> t.uperMinSizeInBits
        | IA5String    t -> t.uperMinSizeInBits
        | OctetString  t -> t.uperMinSizeInBits
        | NullType     t -> t.uperMinSizeInBits
        | BitString    t -> t.uperMinSizeInBits
        | Boolean      t -> t.uperMinSizeInBits
        | Enumerated   t -> t.uperMinSizeInBits
        | SequenceOf   t -> t.uperMinSizeInBits
        | Sequence     t -> t.uperMinSizeInBits
        | Choice       t -> t.uperMinSizeInBits

    member this.asn1Name = 
        match this.id with
        | ReferenceToType((GenericFold2.MD _)::(GenericFold2.TA tasName)::[])   -> Some tasName
        | _                                                                     -> None




(*
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
*)
    
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

(*
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
*)

type AstRoot = AstRootTemplate<Asn1Type>


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
        integerSizeInBytes = r.integerSizeInBytes
    }    
