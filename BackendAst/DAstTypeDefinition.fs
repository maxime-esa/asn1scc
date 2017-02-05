module DAstTypeDefinition

open System
open System.Numerics
open FsUtils
open Constraints
open uPER2
open DAst

let createInnerTypes = false


let getTypeDefinitionName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (id : ReferenceToType) =
    let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
    ToC2(r.TypePrefix + longName.Replace("#","elem"))

let getCompleteDefinition l (typeOrSubsType:TypeOrSubsType) typeDefinitionBody typeDefinitionName (arraySize: int option) (childldrenCompleteDefintions:string list) =
    match l with
    | BAst.C ->  
        header_c.Define_Type typeDefinitionBody typeDefinitionName (arraySize |> Option.map(fun x -> BigInteger x)) childldrenCompleteDefintions
    | BAst.Ada   ->
        sprintf "%A %s %s;" typeOrSubsType typeDefinitionName typeDefinitionBody  


type State = {
    dummy : int
}

let ds = {dummy=0}

let createIntegerTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Integer)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C    when o.IsUnsigned -> header_c.Declare_Integer ()
                        | BAst.C                      -> header_c.Declare_Integer ()
                        | BAst.Ada                    -> 
                            match o.uperRange with
                            | Concrete(a,b)    ->   header_a.Declare_Integer_min_max a b
                            | NegInf (a)       ->   header_a.Declare_Integer_negInf a
                            | PosInf (a)       ->   header_a.Declare_Integer_posInf a
                            | Full             ->   header_a.Declare_Integer ()    


    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }

let createBooleanTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Boolean)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_Boolean ()
                        | BAst.Ada                    -> header_a.Declare_BOOLEAN ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }

let createRealTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Real)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        |BAst.C                      -> header_c.Declare_Real ()
                        |BAst.Ada                    -> header_a.Declare_REAL ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
}

let createStringTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.StringType)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let arraySize = Some(o.maxSize+1)
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_IA5String ()
                        | BAst.Ada                    -> "????"//header_a.IA5STRING_OF_tas_decl ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = arraySize
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName arraySize []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }

let createOctetTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.OctetString)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_OctetString (o.minSize=o.maxSize) (BigInteger o.maxSize)
                        | BAst.Ada                    -> "????"//header_a.IA5STRING_OF_tas_decl ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }

let createBitStringTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.BitString)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_BitString (o.minSize=o.maxSize) (BigInteger o.MaxOctets) (BigInteger o.maxSize)
                        | BAst.Ada                    -> "????"//header_a.IA5STRING_OF_tas_decl ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }

let createNullTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.NullType)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_NullType ()
                        | BAst.Ada                    -> header_a.Declare_NULL ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }


let createEnumeratedTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Enumerated)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_Enumerated items
                        | BAst.Ada                    -> header_a.Declare_Integer ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
    }

let createSequenceOfTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.SequenceOf)  (baseDefinition:TypeDefinitionCommon option) (childDefinition:TypeDefinitionCommon) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | BAst.C                      -> 
                            let typeDefinitionArrayPostfix = 
                                match childDefinition.arraySize with 
                                | None -> "" 
                                | Some x -> sprintf "[%d]" x
                            match createInnerTypes with
                            | true  ->
                                header_c.Declare_SequenceOf (o.minSize = o.maxSize) childDefinition.typeDefinitionBody (BigInteger o.maxSize) typeDefinitionArrayPostfix
                            | false ->
                                header_c.Declare_SequenceOf (o.minSize = o.maxSize) childDefinition.typeDefinitionBodyWithinSeq (BigInteger o.maxSize) typeDefinitionArrayPostfix
                        | BAst.Ada                    -> ""
    let childldrenCompleteDefintions =
        match createInnerTypes with
        | true  -> []
        | false -> childDefinition.completeDefinitionWithinSeq |> Option.toList
        
    let completeDefinition = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = completeDefinition
        typeDefinitionBodyWithinSeq              = 
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _                 -> typeDefinitionName

        completeDefinitionWithinSeq              = Some completeDefinition
    }
let createSequenceTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Sequence)  (baseDefinition:TypeDefinitionCommon option) (children:SeqChildInfo list) (us:State) =
    let handleChild (o:SeqChildInfo) =
        match o.acnInsertetField with
        | false ->
            let typeDefinitionArrayPostfix = match o.chType.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
            match l with
            | BAst.C                      -> 
                match createInnerTypes with
                | true  -> Some (header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBody o.c_name typeDefinitionArrayPostfix)
                | false -> Some (header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix)
            | BAst.Ada                    -> None
        | true                       -> None

    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        let childrenBodies = children |> List.choose handleChild
                        let optChildNames  = children |> List.choose(fun c -> match c.optionality with Some _ -> Some c.name | None -> None)
                        match l with
                        | BAst.C                      -> header_c.Declare_Sequence childrenBodies optChildNames
                        | BAst.Ada                    -> ""
    let childldrenCompleteDefintions =
        match createInnerTypes with
        | true  -> []
        | false -> (children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq))

    let completeDefinition = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = completeDefinition
        typeDefinitionBodyWithinSeq              = 
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _                 -> typeDefinitionName

        completeDefinitionWithinSeq              = Some completeDefinition
    }

let createChoiceTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Choice)  (baseDefinition:TypeDefinitionCommon option) (children:ChChildInfo list) (us:State) =
    let handleChild (o:ChChildInfo) =
        let typeDefinitionArrayPostfix = match o.chType.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
        match l with
        | BAst.C                      -> 
                match createInnerTypes with
                | true  -> header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBody o.c_name typeDefinitionArrayPostfix
                | false -> header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix
        | BAst.Ada                    -> header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBody o.c_name typeDefinitionArrayPostfix

    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        let chEnms = children |> List.map(fun c -> c.presentWhenName)
                        let childrenBodies = children |> List.map handleChild
                        match l with
                        | BAst.C                      -> header_c.Declare_Choice o.choiceIDForNone chEnms childrenBodies 
                        | BAst.Ada                    -> header_c.Declare_Choice o.choiceIDForNone chEnms childrenBodies 
    let childldrenCompleteDefintions =
        match createInnerTypes with
        | true  -> []
        | false -> (children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq))
    let completeDefinition = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = completeDefinition
        typeDefinitionBodyWithinSeq              = 
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _                 -> typeDefinitionName

        completeDefinitionWithinSeq              = Some completeDefinition
    }
