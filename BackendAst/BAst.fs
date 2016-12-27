module BAst

open System
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open Constraints
open FsUtils


type Integer = {
    id                  : ReferenceToType
    cons                : (bool*IntegerTypeConstraint) list
    uperRange           : uperRange<BigInteger>
    baseType            : Integer option
    Location            : SrcLoc   
}

type Real = {
    id                  : ReferenceToType
    cons                : (bool*RealTypeConstraint) list
    uperRange           : uperRange<double>
    baseType            : Real option
    Location            : SrcLoc   
}

type StringType = {
    id                  : ReferenceToType
    cons                : (bool*IA5StringConstraint) list
    sizeUperRange       : uperRange<UInt32>
    charUperRange       : uperRange<char>
    baseType            : StringType option
    Location            : SrcLoc   
}

type EnumItem = {
    name        : string
    Value       : BigInteger
    comments    : string list
}

type Enumerated = {
    id                  : ReferenceToType
    items               : EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : (bool*EnumConstraint) list
    baseType            : Enumerated option
    Location            : SrcLoc   
}

type Boolean = {
    id                  : ReferenceToType
    cons                : (bool*BoolConstraint) list
    baseType            : Boolean option
    Location            : SrcLoc   
}

type SequenceOf = {
    id                  : ReferenceToType
    childTypeRef        : ReferenceToType
    cons                : (bool*SequenceOfConstraint) list
    sizeUperRange       : uperRange<UInt32>
    baseType            : SequenceOf option
    Location            : SrcLoc   
}
 

type OctetString = {
    id                  : ReferenceToType
    cons                : (bool*OctetStringConstraint) list
    sizeUperRange       : uperRange<UInt32>
    baseType            : OctetString option
    Location            : SrcLoc   
}

type NullType = {
    id                  : ReferenceToType
    baseType            : NullType option
    Location            : SrcLoc   
}

type BitString = {
    id                  : ReferenceToType
    cons                : (bool*BitStringConstraint) list
    sizeUperRange       : uperRange<UInt32>
    baseType            : BitString option
    Location            : SrcLoc   
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
    id                  : ReferenceToType
    children            : ChildInfo list
    cons                : (bool*SequenceConstraint) list
    baseType            : Sequence option
    Location            : SrcLoc   
}

and Choice = {
    id                  : ReferenceToType
    children            : ChildInfo list
    cons                : (bool*ChoiceConstraint) list
    baseType            : Choice option
    Location            : SrcLoc   
}



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
    member this.asn1Name = 
        match this.id with
        | ReferenceToType((GenericFold2.MD _)::(GenericFold2.TA tasName)::[])   -> Some tasName
        | _                                                                     -> None



type AstRoot = AstRootTemplate<Asn1Type>

