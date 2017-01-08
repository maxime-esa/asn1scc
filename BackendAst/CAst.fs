module CAst
open System
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils
open Constraints
open uPER2


type IntParamType =
    | Asn1Integer   of Asn1TypeName
    | AcnInteger    

type BooleanParamType =
    | Asn1Boolean   of Asn1TypeName
    | AcnBoolean    

type StringParamType =
    | Asn1String   of Asn1TypeName

type EnumeratedParamType =
    | Asn1Enumerated   of Asn1TypeName

type ParameterTemplate<'T> = {
    name        : string
    prmType     : 'T
}

type IntParameter           = ParameterTemplate<IntParamType>
type BooleanParameter       = ParameterTemplate<BooleanParamType>
type StringParameter        = ParameterTemplate<StringParamType>
type EnumeratedParameter    = ParameterTemplate<EnumeratedParamType>

type GenericParameter = 
    | IntParameter          of IntParameter
    | BoolParameter         of BooleanParamType
    | StringParameter       of StringParameter
    | EnumeratedParameter   of EnumeratedParameter


type DeterminantTypeTemplate<'ASN1TYPE, 'PRMTYPE> = 
    | AcnIntroducedType   of 'ASN1TYPE
    | AcnPrmType          of 'PRMTYPE


type ArgumentTemplate<'DETTYPE> = {
    prmName         : string
    determinant     : 'DETTYPE
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



type EnumAcnEncodingClass =
    | EncodeIndexes     of     Acn.IntEncodingClass
    | EncodeValues      of     Acn.IntEncodingClass 


type Enumerated = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    items               : BAst.EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : EnumConstraint list
    withcons            : EnumConstraint list
    baseType            : Enumerated option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    enumEncodingClass   : EnumAcnEncodingClass
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


type BolleanAcnEncodingClass = {
    truePattern         : byte list
    falsePattern        : byte list
    patternSizeInBits   : int
    encodingValueIsTrue : bool
}

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
    acnEncodingClass    : BolleanAcnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons



type NullAcnEncodingClass = {
    encodePattern       : byte list
    patternSizeInBits   : int
}

type NullType = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    baseType            : NullType option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    acnEncodingClass    : NullAcnEncodingClass
}



type IntegerDeterminant = DeterminantTypeTemplate<Integer,IntParameter>
type IntArgument = ArgumentTemplate<IntegerDeterminant>



type StringAcnEncodingClass =
    | Acn_Enc_String_Ascii_FixSize                          of int             //Fix size ASCII string with size int, the size is provided by maxSize which is equal with minSize
    | Acn_Enc_String_Ascii_Null_Teminated                   of byte            //null character
    | Acn_Enc_String_Ascii_External_Field_Determinant       of IntegerDeterminant //external field
    | Acn_Enc_String_Ascii_Internal_Field_Determinant                          // this case is like uPER except that the ASCII value (8 bits) of the character is encoded and also no fragmentation
    | Acn_Enc_String_CharIndex_FixSize                      of int
    | Acn_Enc_String_CharIndex_External_Field_Determinant   of IntegerDeterminant //external field
    | Acn_Enc_String_CharIndex_Internal_Field_Determinant                      // this case is almost like uPER (except of fragmentation)


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
    acnEncodingClass    : StringAcnEncodingClass
    ancParameters       : IntParameter list
    acnArguments        : IntArgument list
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons


        

 

type SizeableAcnEncodingClass =
    | FixedSize         of int                                  // Fix size, size is equal to minSize which is equal to maxSize 
    | AutoSize                                                  // like uPER but without fragmentation
    | ExternalField     of IntegerDeterminant                                             

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
    acnEncodingClass    : SizeableAcnEncodingClass
    ancParameters       : IntParameter list
    acnArguments        : IntArgument list
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons



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
    acnEncodingClass    : SizeableAcnEncodingClass
    ancParameters       : IntParameter list
    acnArguments        : IntArgument list
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

type BooleanDeterminant = DeterminantTypeTemplate<Boolean,BooleanParameter>
type BooleanArgument = ArgumentTemplate<BooleanDeterminant>

type EnumeratedDeterminant = DeterminantTypeTemplate<Enumerated,EnumeratedParameter>
type EnumeratedArgument = ArgumentTemplate<EnumeratedDeterminant>

type StringDeterminant = DeterminantTypeTemplate<StringType,StringParameter>
type StringArgument = ArgumentTemplate<StringDeterminant>


type GenericArgument =
    | IntArgument           of IntArgument
    | BooleanArgument       of BooleanArgument
    | EnumeratedArgument    of EnumeratedArgument
    | StringArgument        of StringArgument

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
    acnEncodingClass    : SizeableAcnEncodingClass
    ancParameters       : GenericParameter list
    acnArguments        : GenericArgument list
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons



and OptionalalityEncodingClass = 
    | OptionLikeUper
    | OptionExtField    of BooleanDeterminant

and Optional = {
    defaultValue        : Asn1GenericValue
    ancEncodingClass    : OptionalalityEncodingClass
}

and Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional          of Optional


and SeqChildInfo = {
    name                :string
    chType              :Asn1Type
    optionality         :Asn1Optionality option
    acnInsertetField    :bool
    comments            :string list
}


and Sequence = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    children            : SeqChildInfo list
    cons                : SequenceConstraint list
    withcons            : SequenceConstraint list
    baseType            : Sequence option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    ancParameters       : GenericParameter list
    acnArguments        : GenericArgument list
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons




and ChoiceAcnEncClass =
    | EmbededChoiceIndexLikeUper
    | EnumDeterminant               of EnumeratedDeterminant
    | PresentWhenOnChildren

and ChoiceChildPresentCondition = 
    | PresentWhenBool   of BooleanDeterminant 
    | PresentWhenInt    of (IntegerDeterminant*BigInteger)
    | PresentWhenString of (StringDeterminant*string)

and ChChildInfo = {
    name                :string
    chType              :Asn1Type
    presentConditions   :ChoiceChildPresentCondition list
    comments            :string list
}

and Choice = {
    id                  : ReferenceToType
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    children            : ChChildInfo list
    cons                : ChoiceConstraint list
    withcons            : ChoiceConstraint list
    baseType            : Choice option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    acnEncodingClass    : ChoiceAcnEncClass
    ancParameters       : GenericParameter list
    acnArguments        : GenericArgument list
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
