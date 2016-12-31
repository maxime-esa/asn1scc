module BAst

open System
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open Constraints
open uPER2
open FsUtils



type Integer = {
    id                  : ReferenceToType
    cons                : IntegerTypeConstraint list
    withcons            : IntegerTypeConstraint list
    uperRange           : uperRange<BigInteger>
    baseType            : Integer option
    Location            : SrcLoc   
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

type Real = {
    id                  : ReferenceToType
    cons                : RealTypeConstraint list
    withcons            : RealTypeConstraint list
    uperRange           : uperRange<double>
    baseType            : Real option
    Location            : SrcLoc   
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

type StringType = {
    id                  : ReferenceToType
    cons                : IA5StringConstraint list
    withcons            : IA5StringConstraint list
    sizeUperRange       : uperRange<UInt32>
    charUperRange       : uperRange<char>
    baseType            : StringType option
    Location            : SrcLoc   
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
    items               : EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : EnumConstraint list
    withcons            : EnumConstraint list
    baseType            : Enumerated option
    Location            : SrcLoc   
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons
        

type Boolean = {
    id                  : ReferenceToType
    cons                : BoolConstraint list
    withcons            : BoolConstraint list
    baseType            : Boolean option
    Location            : SrcLoc   
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons
 

type OctetString = {
    id                  : ReferenceToType
    cons                : OctetStringConstraint list
    withcons            : OctetStringConstraint list
    sizeUperRange       : uperRange<UInt32>
    baseType            : OctetString option
    Location            : SrcLoc   
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons

type NullType = {
    id                  : ReferenceToType
    baseType            : NullType option
    Location            : SrcLoc   
}

type BitString = {
    id                  : ReferenceToType
    cons                : BitStringConstraint list
    withcons            : BitStringConstraint list
    sizeUperRange       : uperRange<UInt32>
    baseType            : BitString option
    Location            : SrcLoc   
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
    childType           : Asn1Type
    cons                : SequenceOfConstraint list
    withcons            : SequenceOfConstraint list
    sizeUperRange       : uperRange<UInt32>
    baseType            : SequenceOf option
    Location            : SrcLoc   
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
    children            : ChildInfo list
    cons                : SequenceConstraint list
    withcons            : SequenceConstraint list
    baseType            : Sequence option
    Location            : SrcLoc   
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons

and Choice = {
    id                  : ReferenceToType
    children            : ChildInfo list
    cons                : ChoiceConstraint list
    withcons            : ChoiceConstraint list
    baseType            : Choice option
    Location            : SrcLoc   
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
    member this.asn1Name = 
        match this.id with
        | ReferenceToType((GenericFold2.MD _)::(GenericFold2.TA tasName)::[])   -> Some tasName
        | _                                                                     -> None



type AstRoot = AstRootTemplate<Asn1Type>



(*
Statically resolved types with Records

type Cat = { Name : string } member x.Nickname = x.Name
type Dog = { Name : string } member x.Nickname = x.Name

let inline showName (animal : ^T ) =
    let name = (^T : (member Nickname : string) (animal))
    printfn "%s" name

let cat = { Name = "Miaou" } : Cat
let dog = { Name = "Waf" } : Dog

showName cat
showName dog
*)