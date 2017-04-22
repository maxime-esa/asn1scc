module DAstTypeDefinition

open System
open System.Numerics
open FsUtils
open Constraints
open uPER2
open DAst



let createInnerTypes (l:ProgrammingLanguage) = 
    match l with
    | Ada  -> false
    | C    -> true


let getTypeDefinitionName (r:CAst.AstRoot) (l:ProgrammingLanguage) (id : ReferenceToType) =
    let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
    ToC2(r.TypePrefix + longName.Replace("#","elem"))

let getCompleteDefinition l (typeOrSubsType:TypeOrSubsType) typeDefinitionBody typeDefinitionName (arraySize: int option) (childldrenCompleteDefintions:string list) =
    match l with
    | C ->  
        header_c.Define_Type typeDefinitionBody typeDefinitionName (arraySize |> Option.map(fun x -> BigInteger x)) childldrenCompleteDefintions
    | Ada   ->
        let typeOrSubsType = sprintf "%A" typeOrSubsType 
        header_a.Define_Type typeOrSubsType typeDefinitionName typeDefinitionBody  childldrenCompleteDefintions

let hasSingleValueConstraint (c:SizableTypeConstraint<'v>) =
    foldSizableTypeConstraint2
        (fun e1 e2 b s      -> e1 || e2, s)
        (fun e1 e2 s        -> e1 || e2, s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> e1 || e2, s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> e1 || e2, s)
        (fun v rv s         -> true ,s)
        (fun intCon s       -> false,s)
        c
        0 |> fst



//let ds = {dummy=0}

let createIntegerTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id

    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    match o.IsUnsigned with
                    | true  -> header_c.Declare_PosInteger ()
                    | false -> header_c.Declare_Integer ()
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
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

    }

let createBooleanTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id

    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | C                      -> header_c.Declare_Boolean ()
                        | Ada                    -> header_a.Declare_BOOLEAN ()

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        //typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        

    }

let createRealTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        |C                      -> header_c.Declare_Real ()
                        |Ada                    -> header_a.Declare_REAL ()
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        

    }

let createStringTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let arraySize = Some(o.maxSize+1)
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _                 -> header_c.Declare_IA5String ()
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName arraySize [], typeDefinitionBody, None
        | Ada                    -> 
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
        

    }

let createOctetTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            match baseDefinition with
            | None  ->
                let typeDefinitionBody = header_c.Declare_OctetString (o.minSize=o.maxSize) (BigInteger o.maxSize)
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
                completeDefintion, typeDefinitionName, Some completeDefintion
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
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
        

    }

let createBitStringTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            match baseDefinition with 
            | None              -> 
                let typeDefinitionBody = header_c.Declare_BitString (o.minSize=o.maxSize) (BigInteger o.MaxOctets) (BigInteger o.maxSize)
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
                completeDefintion, typeDefinitionName, Some completeDefintion
            | Some baseType     -> 
                let typeDefinitionBody = baseType.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
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
        

    }

let createNullTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.NullType)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let typeDefinitionBody                       =
                    match baseDefinition with 
                    | Some baseType     -> baseType.name
                    | _    ->
                        match l with
                        | C                      -> header_c.Declare_NullType ()
                        | Ada                    -> header_a.Declare_NULL ()

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        //typeDefinitionBody                       = typeDefinitionBody
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        

    }


let createEnumeratedTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated)  (baseDefinition:TypeDefinitionCommon option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            let items = 
                match o.userDefinedValues with
                | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
                | false ->o.items |> List.map( fun i -> i.getBackendName l)
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _                 -> header_c.Declare_Enumerated items
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
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
        

    }

let createSequenceOfTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.SequenceOf)  (baseDefinition:TypeDefinitionCommon option) (childDefinition:TypeDefinitionCommon) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    
    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> childDefinition.completeDefinitionWithinSeq |> Option.toList
        | false -> childDefinition.completeDefinitionWithinSeq |> Option.toList


    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
          (*
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
            *)
            match baseDefinition with
            | None  ->
                let typeDefinitionArrayPostfix = 
                    match childDefinition.arraySize with 
                    | None -> "" 
                    | Some x -> sprintf "[%d]" x

                let typeDefinitionBody = header_c.Declare_SequenceOf (o.minSize = o.maxSize) childDefinition.typeDefinitionBodyWithinSeq (BigInteger o.maxSize) typeDefinitionArrayPostfix
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None

        | Ada                    -> 
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
    }

let createSequenceTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Sequence)  (baseDefinition:TypeDefinitionCommon option) (children:SeqChildInfo list) (us:State) =
    let handleChild (o:SeqChildInfo) =
        match o.acnInsertetField with
        | false ->
            match l with
            | C->
                let typeDefinitionArrayPostfix = match o.chType.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
                Some (header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix)
            | Ada  ->
                Some (header_a.SEQUENCE_tas_decl_child o.c_name o.chType.typeDefinition.typeDefinitionBodyWithinSeq)
        | true                       -> None

    let typeDefinitionName = getTypeDefinitionName r l o.id
    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> (children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq))
        | false -> (children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq))
    
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
        (*
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    let childrenBodies = children |> List.choose handleChild
                    let optChildNames  = children |> List.choose(fun c -> match c.optionality with Some _ -> Some c.name | None -> None)
                    header_c.Declare_Sequence childrenBodies optChildNames
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions, typeDefinitionBody, None
            *)
            match baseDefinition with
            | None  ->
                let childrenBodies = children |> List.choose handleChild
                let optChildNames  = children |> List.choose(fun c -> match c.optionality with Some _ -> Some c.name | None -> None)
                let typeDefinitionBody = header_c.Declare_Sequence childrenBodies optChildNames
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
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
    }

let createChoiceTypeDefinition (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Choice)  (baseDefinition:TypeDefinitionCommon option) (children:ChChildInfo list) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.id
    let handleChild (o:ChChildInfo) =
        match l with
        | C                      -> 
            let typeDefinitionArrayPostfix = match o.chType.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
            header_c.PrintSeq_ChoiceChild o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix
        | Ada                    -> 
            header_a.CHOICE_tas_decl_child o.c_name  o.chType.typeDefinition.typeDefinitionBodyWithinSeq o.presentWhenName

    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq)
        | false -> children |> List.choose (fun c -> c.chType.typeDefinition.completeDefinitionWithinSeq)

    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
        (*
            let typeDefinitionBody                       =
                match baseDefinition with 
                | Some baseType     -> baseType.name
                | _    ->
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    header_c.Declare_Choice o.choiceIDForNone chEnms childrenBodies 
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions, typeDefinitionBody, None
            *)
            match baseDefinition with
            | None  ->
                let completeDefintion = 
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    let typeDefinitionBody = header_c.Declare_Choice o.choiceIDForNone chEnms childrenBodies 
                    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion)
            | Some baseTypeName     ->
                let typeDefinitionBody = baseTypeName.name
                getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None

        | Ada                    -> 
            match baseDefinition with
            | None  ->
                let completeDefintion = 
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    let nIndexMax = BigInteger ((Seq.length children)-1)
                    header_a.CHOICE_tas_decl typeDefinitionName children.Head.presentWhenName childrenBodies chEnms nIndexMax childldrenCompleteDefintions
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
    } 
