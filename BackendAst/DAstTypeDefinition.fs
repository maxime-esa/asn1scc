module DAstTypeDefinition

open System
open System.Numerics
open FsUtils
open Constraints
open uPER2
open DAst

let createInnerTypes (l:BAst.ProgrammingLanguage) = 
    match l with
    | BAst.Ada  -> false
    | BAst.C    -> true


let getTypeDefinitionName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (id : ReferenceToType) =
    let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
    ToC2(r.TypePrefix + longName.Replace("#","elem"))

let getCompleteDefinition l (typeOrSubsType:TypeOrSubsType) typeDefinitionBody typeDefinitionName (arraySize: int option) (childldrenCompleteDefintions:string list) =
    match l with
    | BAst.C ->  
        header_c.Define_Type typeDefinitionBody typeDefinitionName (arraySize |> Option.map(fun x -> BigInteger x)) childldrenCompleteDefintions
    | BAst.Ada   ->
        let typeOrSubsType = sprintf "%A" typeOrSubsType 
        header_a.Define_Type typeOrSubsType typeDefinitionName typeDefinitionBody  childldrenCompleteDefintions


type State = {
    dummy : int
}

let ds = {dummy=0}

let createIntegerTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Integer)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id

    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    match o.IsUnsigned with
                    | true  -> header_c.Declare_Integer ()
                    | false -> header_c.Declare_Integer ()
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let typeDefinitionBody = 
                    match o.uperRange with
                    | Concrete(a,b)    ->   header_a.Declare_Integer_min_max a b
                    | NegInf (a)       ->   header_a.Declare_Integer_negInf a
                    | PosInf (a)       ->   header_a.Declare_Integer_posInf a
                    | Full             ->   header_a.Declare_Integer ()    
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
                match o.uperRange with
                | Full  ->
                    completeDefintion, typeDefinitionBody, None
                | _     ->
                    completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        ////typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        choicePrivateGetters                     = []
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
        //typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        
        choicePrivateGetters                 = []
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
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        
        choicePrivateGetters                 = []
    }

let createStringTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.StringType)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let arraySize = Some(o.maxSize+1)
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _                 -> header_c.Declare_IA5String ()
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName arraySize [], typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let completeDefintion = header_a.IA5STRING_OF_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (BigInteger (o.maxSize + 1)) (o.charSet |> Array.map(fun c -> (BigInteger (int c))))
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName arraySize [], typeDefinitionBody, None

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = arraySize
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        
        choicePrivateGetters                 = []
    }

let createOctetTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.OctetString)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _                 -> header_c.Declare_OctetString (o.minSize=o.maxSize) (BigInteger o.maxSize)
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let completeDefintion = header_a.OCTET_STRING_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (o.maxSize=o.minSize)
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        
        choicePrivateGetters                 = []
    }

let createBitStringTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.BitString)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _                 -> header_c.Declare_BitString (o.minSize=o.maxSize) (BigInteger o.MaxOctets) (BigInteger o.maxSize)
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let completeDefintion = header_a.BIT_STRING_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (o.maxSize=o.minSize)
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        
        choicePrivateGetters                 = []
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
        //typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        
        choicePrivateGetters                 = []
    }


let createEnumeratedTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Enumerated)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let items = 
                match o.userDefinedValues with
                | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
                | false ->o.items |> List.map( fun i -> i.getBackendName l)
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _                 -> header_c.Declare_Enumerated items
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let arrsEnumNames = o.items |> List.map( fun i -> i.getBackendName l)
                let arrsEnumNamesAndValues = o.items |> List.map( fun i -> header_a.ENUMERATED_tas_decl_item (i.getBackendName l) i.Value)
                let nIndexMax = BigInteger ((Seq.length o.items)-1)
                let completeDefintion = header_a.ENUMERATED_tas_decl typeDefinitionName arrsEnumNames arrsEnumNamesAndValues nIndexMax
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        
        choicePrivateGetters                 = []
    }

let createSequenceOfTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.SequenceOf)  (baseDefinition:TypeDefinitionCommon option) (childDefinition:TypeDefinitionCommon) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    
    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> []
        | false -> childDefinition.completeDefinitionWithinSeq |> Option.toList


    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    let typeDefinitionArrayPostfix = 
                        match childDefinition.arraySize with 
                        | None -> "" 
                        | Some x -> sprintf "[%d]" x
                    header_c.Declare_SequenceOf (o.minSize = o.maxSize) childDefinition.typeDefinitionBodyWithinSeq (BigInteger o.maxSize) typeDefinitionArrayPostfix
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions, typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let completeDefintion = header_a.SEQUENCE_OF_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (o.minSize = o.maxSize) childDefinition.typeDefinitionBodyWithinSeq childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None


    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        //typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        
        choicePrivateGetters                     = childDefinition.choicePrivateGetters
    }

let createSequenceTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Sequence)  (baseDefinition:TypeDefinitionCommon option) (children:SeqChildInfo list) (us:State) =
    let handleChild (o:SeqChildInfo) =
        match o.acnInsertetField with
        | false ->
            match l with
            | BAst.C->
                let typeDefinitionArrayPostfix = match o.chType.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
                Some (header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix)
            | BAst.Ada  ->
                Some (header_a.SEQUENCE_tas_decl_child o.c_name o.chType.typeDefinition.typeDefinitionBodyWithinSeq)
        | true                       -> None

    let typeDefinitionName = getTypeDefinitionName r l o.id
    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> []
        | false -> (children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq))
    
    let choicePrivateGetters = children |> List.collect (fun c -> c.chType.typeDefinition.choicePrivateGetters)

    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    let childrenBodies = children |> List.choose handleChild
                    let optChildNames  = children |> List.choose(fun c -> match c.optionality with Some _ -> Some c.name | None -> None)
                    header_c.Declare_Sequence childrenBodies optChildNames
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let childrenBodies = children |> List.choose handleChild
                let optChildren  = children |> List.choose(fun c -> match c.optionality with Some _ -> Some(header_a.SEQUENCE_tas_decl_child_bit c.name) | None -> None)
                let completeDefintion = header_a.SEQUENCE_tas_decl typeDefinitionName childrenBodies optChildren childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None


    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        choicePrivateGetters                     = choicePrivateGetters
    }

let createChoiceTypeDefinition (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Choice)  (baseDefinition:TypeDefinitionCommon option) (children:ChChildInfo list) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let handleChild (o:ChChildInfo) =
        match l with
        | BAst.C                      -> 
            let typeDefinitionArrayPostfix = match o.chType.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
            header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix
        | BAst.Ada                    -> 
            header_a.CHOICE_tas_decl_child o.c_name  o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.presentWhenName

    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> []
        | false -> (children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq))

    let childrenChoicePrivateGetters = children |> List.collect (fun c -> c.chType.typeDefinition.choicePrivateGetters)
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq, choicePrivateGetters =
        match l with
        | BAst.C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    header_c.Declare_Choice o.choiceIDForNone chEnms childrenBodies 
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None, []
        | BAst.Ada                    -> 
            match baseDefinition with
            | None  ->
                let completeDefintion = 
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    let nIndexMax = BigInteger ((Seq.length children)-1)
                    header_a.CHOICE_tas_decl typeDefinitionName children.Head.presentWhenName childrenBodies chEnms nIndexMax childldrenCompleteDefintions
(*                let choiceGettersSpec =
                    let childrenBodies = children |> List.map(fun o -> header_a.CHOICE_tas_decl_priv_child o.c_name  o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.presentWhenName)
                    header_a.CHOICE_tas_decl_priv typeDefinitionName children.Head.presentWhenName childrenBodies
                let choiceGettersImplementation =
                    let children =  children |> List.map(fun o -> header_a.CHOICE_setters_body_child typeDefinitionName o.c_name  o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.presentWhenName)
                    header_a.CHOICE_setters_body  typeDefinitionName children*)
                completeDefintion, typeDefinitionName, (Some completeDefintion),  []//[{ChoicePrivateGetters.specPart = choiceGettersSpec; bodyPart = choiceGettersImplementation}]
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None, []



    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        choicePrivateGetters                     = childrenChoicePrivateGetters@choicePrivateGetters
    } 
