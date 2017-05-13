module DAstBaseTypesEquivalence

open System
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open Constraints
open uPER2
open FsUtils
open DAst


let getInteger (t:CAst.Integer) (bo:Integer option) =
    let typedefBase =
        match bo with
        | None                                          -> None
        | Some bo   when t.IsUnsigned = bo.IsUnsigned   -> Some bo
        | Some _                                        -> None

    let uper =
        match bo with
        | None                 -> None
        | Some bo              ->
            match t.cons with
            | []            -> typedefBase
            | _             -> None
    
            

    {BaseTypesEquivalence.typeDefinition = typedefBase; uper = uper; acn = None}

let getReal (t:CAst.Real) (bo:Real option) =
    {BaseTypesEquivalence.typeDefinition = bo; uper = bo; acn = None}

let getIA5String (t:CAst.StringType) (bo:StringType option) =
    let typedefBase  =
        match bo with
        | None                                          -> None
        | Some bo   when t.maxSize = bo.maxSize  && t.minSize = bo.minSize    -> Some bo
        | Some _                                        -> None

    let uperBase  =
        match bo with
        | None                 -> None
        | Some bo   when t.maxSize = bo.maxSize  && t.minSize = bo.minSize  && t.charSet = bo.charSet
            -> Some bo
        | Some _                                        -> None
    {BaseTypesEquivalence.typeDefinition = typedefBase; uper = uperBase; acn = None}


let getOctetString (t:CAst.OctetString) (bo:OctetString option) =
    let typedefBase  =
        match bo with
        | None                                          -> None
        | Some bo   when t.maxSize = bo.maxSize  && t.minSize = bo.minSize    -> Some bo
        | Some _                                        -> None
    let uperBase  = typedefBase
    {BaseTypesEquivalence.typeDefinition = typedefBase; uper = uperBase; acn = None}



let getBitString (t:CAst.BitString) (bo:BitString option) =
    let typedefBase  =
        match bo with
        | None                                          -> None
        | Some bo   when t.maxSize = bo.maxSize  && t.minSize = bo.minSize    -> Some bo
        | Some _                                        -> None
    let uperBase  = typedefBase
    {BaseTypesEquivalence.typeDefinition = typedefBase; uper = uperBase; acn = None}


let getBoolean  (t: CAst.Boolean    ) (bo:Boolean    option) = 
    {BaseTypesEquivalence.typeDefinition = bo; uper = bo; acn = None}

let getNullType      (t:CAst.NullType   ) (bo:NullType   option) = 
    {BaseTypesEquivalence.typeDefinition = bo; uper = bo; acn = None}

let getEnumerated    (t:CAst.Enumerated ) (bo:Enumerated option) = 
    {BaseTypesEquivalence.typeDefinition = bo; uper = bo; acn = None}

let getSequenceOf    (t:CAst.SequenceOf ) (bo:SequenceOf option) = 
    let typedefBase  =
        match bo with
        | None                                          -> None
        | Some bo   when t.maxSize = bo.maxSize  && t.minSize = bo.minSize    -> Some bo
        | Some _                                        -> None
    let uperBase  = typedefBase
    {BaseTypesEquivalence.typeDefinition = typedefBase; uper = uperBase; acn = None}

let getSequence      (t:CAst.Sequence   ) (bo:Sequence   option) = 
    {BaseTypesEquivalence.typeDefinition = bo; uper = bo; acn = None}

let getChoice        (t:CAst.Choice     ) (bo:Choice     option) = 
    {BaseTypesEquivalence.typeDefinition = bo; uper = bo; acn = None}

