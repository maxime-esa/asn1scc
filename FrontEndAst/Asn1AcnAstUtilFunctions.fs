module Asn1AcnAstUtilFunctions

open Asn1AcnAst
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open System
open FsUtils
open CommonTypes

type ScopeNode with
    member this.AsString =
        match this with
        | MD strVal
        | TA strVal
        | VA strVal
        | PRM strVal
        | SEQ_CHILD strVal
        | CH_CHILD strVal -> strVal
        | SQF             -> "#"
    member this.StrValue = this.AsString

type ReferenceToType with 
    member this.AsString =
        match this with
        | ReferenceToType sn -> sn |> Seq.map(fun x -> x.AsString) |> Seq.StrJoin "."
        member this.ToScopeNodeList = 
            match this with
            | ReferenceToType path -> path 
        member this.ModName =
            match this with
            | ReferenceToType path -> 
                match path with
                | (MD modName)::_    -> modName
                | _                               -> raise(BugErrorException "Did not find module at the begining of the scope path")
        member this.AcnAbsPath =
            match this with
            | ReferenceToType path -> path |> List.map (fun i -> i.StrValue) 
        member this.getSeqChildId (childName:string) =
            match this with
            | ReferenceToType path -> ReferenceToType (path@[SEQ_CHILD childName])
        member this.getChildId (childName:string) =
            match this with
            | ReferenceToType path -> ReferenceToType (path@[CH_CHILD childName])
        member this.getParamId (paramName:string) =
            match this with
            | ReferenceToType ((MD mdName)::(TA tasName)::[]) -> ReferenceToType ((MD mdName)::(TA tasName)::[PRM paramName])
            | _                                                                         -> raise(BugErrorException "Cannot add parameter here. Only within TAS scope")

        member this.appendLongChildId (childRelativePath:string list) =
            match this with
            | ReferenceToType path -> 
                let newTail = 
                    childRelativePath |> 
                    List.map(fun s ->SEQ_CHILD s)
                ReferenceToType (path@newTail)
        member this.beginsWith (md:string) (ts:string)= 
            match this with
            | ReferenceToType((MD mdName)::(TA tasName)::[])   -> mdName = md && tasName = ts
            | _                                                                          -> false
        member this.lastItem =
            match this with
            | ReferenceToType path -> 
                match path |> List.rev |> List.head with
                | SEQ_CHILD name   -> name
                | CH_CHILD name    -> name
                | _                             -> raise (BugErrorException "error in lastitem")
        member this.parentTypeId =
            match this with
            | ReferenceToType path -> 
                let pathPar = path |> List.rev |> List.tail |> List.rev
                match pathPar with
                | [] 
                | _::[]     -> None
                | _         -> Some (ReferenceToType pathPar)
        member this.SeqeuenceOfLevel =
            match this with
            | ReferenceToType path -> path |> List.filter(fun n -> match n with SQF -> true | _ -> false) |> Seq.length
        static member createFromModAndTasName (modName : string) ((tasName : string))=
            ReferenceToType((MD modName)::(TA tasName)::[])


type Asn1Type with
    member this.uperMinSizeInBits =
        match this.Kind with
        | Integer        x -> x.uperMinSizeInBits
        | Real           x -> x.uperMinSizeInBits
        | IA5String      x -> x.uperMinSizeInBits
        | NumericString  x -> x.uperMinSizeInBits
        | OctetString    x -> x.uperMinSizeInBits
        | NullType       x -> x.uperMinSizeInBits
        | BitString      x -> x.uperMinSizeInBits
        | Boolean        x -> x.uperMinSizeInBits
        | Enumerated     x -> x.uperMinSizeInBits
        | SequenceOf     x -> x.uperMinSizeInBits
        | Sequence       x -> x.uperMinSizeInBits
        | Choice         x -> x.uperMinSizeInBits
        | ReferenceType  x -> x.baseType.uperMinSizeInBits

    member this.uperMaxSizeInBits =
        match this.Kind with
        | Integer        x -> x.uperMaxSizeInBits
        | Real           x -> x.uperMaxSizeInBits
        | IA5String      x -> x.uperMaxSizeInBits
        | NumericString  x -> x.uperMaxSizeInBits
        | OctetString    x -> x.uperMaxSizeInBits
        | NullType       x -> x.uperMaxSizeInBits
        | BitString      x -> x.uperMaxSizeInBits
        | Boolean        x -> x.uperMaxSizeInBits
        | Enumerated     x -> x.uperMaxSizeInBits
        | SequenceOf     x -> x.uperMaxSizeInBits
        | Sequence       x -> x.uperMaxSizeInBits
        | Choice         x -> x.uperMaxSizeInBits
        | ReferenceType  x -> x.baseType.uperMaxSizeInBits

    member this.acnMinSizeInBits =
        match this.Kind with
        | Integer        x -> x.acnMinSizeInBits
        | Real           x -> x.acnMinSizeInBits
        | IA5String      x -> x.acnMinSizeInBits
        | NumericString  x -> x.acnMinSizeInBits
        | OctetString    x -> x.acnMinSizeInBits
        | NullType       x -> x.acnMinSizeInBits
        | BitString      x -> x.acnMinSizeInBits
        | Boolean        x -> x.acnMinSizeInBits
        | Enumerated     x -> x.acnMinSizeInBits
        | SequenceOf     x -> x.acnMinSizeInBits
        | Sequence       x -> x.acnMinSizeInBits
        | Choice         x -> x.acnMinSizeInBits
        | ReferenceType  x -> x.baseType.acnMinSizeInBits

    member this.acnMaxSizeInBits =
        match this.Kind with
        | Integer        x -> x.acnMaxSizeInBits
        | Real           x -> x.acnMaxSizeInBits
        | IA5String      x -> x.acnMaxSizeInBits
        | NumericString  x -> x.acnMaxSizeInBits
        | OctetString    x -> x.acnMaxSizeInBits
        | NullType       x -> x.acnMaxSizeInBits
        | BitString      x -> x.acnMaxSizeInBits
        | Boolean        x -> x.acnMaxSizeInBits
        | Enumerated     x -> x.acnMaxSizeInBits
        | SequenceOf     x -> x.acnMaxSizeInBits
        | Sequence       x -> x.acnMaxSizeInBits
        | Choice         x -> x.acnMaxSizeInBits
        | ReferenceType  x -> x.baseType.acnMaxSizeInBits

type AcnInsertedType with
    member this.acnMinSizeInBits =
        match this with
        | AcnInteger        x -> x.acnMinSizeInBits
        | AcnNullType       x -> x.acnMinSizeInBits
        | AcnBoolean        x -> x.acnMinSizeInBits
    member this.acnMaxSizeInBits =
        match this with
        | AcnInteger        x -> x.acnMaxSizeInBits
        | AcnNullType       x -> x.acnMaxSizeInBits
        | AcnBoolean        x -> x.acnMaxSizeInBits
    member this.acnAligment =
        match this with
        | AcnInteger        x -> x.acnAligment
        | AcnNullType       x -> x.acnAligment
        | AcnBoolean        x -> x.acnAligment
    member this.Location =
        match this with
        | AcnInteger        x -> x.Location
        | AcnNullType       x -> x.Location
        | AcnBoolean        x -> x.Location
       
type BitString with
    member this.MaxOctets = int (ceil ((double this.maxSize)/8.0))



type SeqChildInfo with
    member this.Name =
        match this with
        | Asn1Child x   -> x.Name
        | AcnChild  x   -> x.Name

    member this.acnMinSizeInBits =
        match this with
        | Asn1Child x   -> x.Type.acnMinSizeInBits
        | AcnChild  x   -> x.Type.acnMinSizeInBits
    member this.acnMaxSizeInBits =
        match this with
        | Asn1Child x   -> x.Type.acnMaxSizeInBits
        | AcnChild  x   -> x.Type.acnMaxSizeInBits
    member this.acnAligment =
        match this with
        | Asn1Child x   -> x.Type.acnAligment
        | AcnChild  x   -> x.Type.acnAligment
    member this.Optionality =
        match this with
        | Asn1Child x   -> x.Optionality
        | AcnChild  x   -> None


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
