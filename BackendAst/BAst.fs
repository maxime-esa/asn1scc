module BAst

open System
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open Constraints
open FsUtils


type Integer = {
    cons                : (bool*IntegerTypeConstraint) list
    uperRange           : uperRange<BigInteger>
}

type Real = {
    cons                : (bool*RealTypeConstraint) list
    uperRange           : uperRange<double>
}

type StringType = {
    cons                : (bool*IA5StringConstraint) list
    sizeUperRange       : uperRange<UInt32>
    charUperRange       : uperRange<char>
}

type EnumItem = {
    name        : string
    Value       : BigInteger
    comments    : string list
}

type Enumerated = {
    items               : EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : (bool*EnumConstraint) list
}

type Boolean = {
    cons                : (bool*BoolConstraint) list
}

type SequenceOf = {
    childTypeRef        : ReferenceToType
    cons                : (bool*SequenceOfConstraint) list
    sizeUperRange       : uperRange<UInt32>
}
 

type OctetString = {
    cons                : (bool*OctetStringConstraint) list
    sizeUperRange       : uperRange<UInt32>
}

type BitString = {
    cons                : (bool*BitStringConstraint) list
    sizeUperRange       : uperRange<UInt32>
}

type Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of Asn1GenericValue


and ChildInfo = {
    Name:string;
    refToType:ReferenceToType;
    Optionality:Asn1Optionality option
    Comments: string array
}

and Sequence = {
    children : ChildInfo list
    cons     : (bool*SequenceConstraint) list
}

and Choice = {
    children : ChildInfo list
    cons     : (bool*ChoiceConstraint) list
}



and Asn1TypeKind =
    | Integer           of Integer
    | Real              of Real
    | IA5String         of StringType
    | OctetString       of OctetString
    | NullType
    | BitString         of BitString
    | Boolean           of Boolean
    | Enumerated        of Enumerated
    | SequenceOf        of SequenceOf
    | Sequence          of Sequence
    | Choice            of Choice


and Asn1Type = {
    asn1Name : string option
    id : ReferenceToType
    baseTypeId : ReferenceToType option     // base type
    Kind:Asn1TypeKind;
    Location: SrcLoc   //Line no, Char pos
}


type AstRoot = AstRootTemplate<Asn1Type>

