module DAstTypeDefinition

open System
open System.Numerics
open FsUtils
open Asn1AcnAstUtilFunctions
open Asn1AcnAst
open CommonTypes
open DAst
open DAstUtilFunctions
open Asn1Fold



let createInnerTypes (l:ProgrammingLanguage) = 
    match l with
    | Ada  -> false
    | C    -> true


let getTypeDefinitionName (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (id : ReferenceToType) =
    let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
    ToC2(r.args.TypePrefix + longName.Replace("#","elem"))

let getCompleteDefinition l (typeOrSubsType:TypeOrSubsType) typeDefinitionBody typeDefinitionName (arraySize: int option) (childldrenCompleteDefintions:string list) =
    match l with
    | C ->  
        header_c.Define_Type typeDefinitionBody typeDefinitionName (arraySize |> Option.map(fun x -> BigInteger x)) childldrenCompleteDefintions
    | Ada   ->
        let typeOrSubsType = sprintf "%A" typeOrSubsType 
        header_a.Define_Type typeOrSubsType typeDefinitionName typeDefinitionBody  childldrenCompleteDefintions
(*
let hasSingleValueConstraint (c:SizableTypeConstraint<'v>) =
    foldSizableTypeConstraint2
        (fun e1 e2 b s      -> e1 || e2, s)
        (fun e1 e2 s        -> e1 || e2, s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> e1 || e2, s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> e1 || e2, s)
        (fun v  s           -> true ,s)
        (fun intCon s       -> false,s)
        c
        0 |> fst
*)


//let ds = {dummy=0}

let createInteger (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type)  (o:Asn1AcnAst.Integer)   (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id

    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            let typeDefinitionBody                       =
                match o.isUnsigned with
                | true  -> header_c.Declare_PosInteger ()
                | false -> header_c.Declare_Integer ()
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
            let typeDefinitionBody = 
                match o.uperRange with
                | Concrete(a,b)  when o.isUnsigned   ->   header_a.Declare_PosInteger_min_max a b
                | Concrete(a,b)    ->   header_a.Declare_Integer_min_max a b
                | NegInf (a)       ->   header_a.Declare_Integer_negInf a
                | PosInf (a) when o.isUnsigned      ->   header_a.Declare_PosInteger_posInf a
                | PosInf (a)       ->   header_a.Declare_Integer_posInf a
                | Full             ->   header_a.Declare_Integer ()    
            let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
            match o.uperRange with
            | Full  ->
                completeDefintion, typeDefinitionBody, None
            | _     ->
                completeDefintion, typeDefinitionName, (Some completeDefintion) 

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq

    }


let createPrmAcnInteger (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage)  =
    let Declare_Integer     =  match l with  C  -> header_c.Declare_Integer  | Ada   -> header_a.Declare_Integer 
    Declare_Integer ()

let createAcnInteger (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (a:Asn1AcnAst.AcnInteger) =
    let Declare_Integer     =  match l with  C  -> header_c.Declare_Integer  | Ada   -> header_a.Declare_Integer 
    let Declare_PosInteger  =  match l with  C  -> header_c.Declare_PosInteger  | Ada   -> header_a.Declare_PosInteger  
    match a.isUnsigned with
    | true     -> Declare_PosInteger ()
    | false    -> Declare_Integer ()
        
    
let createAcnBoolean (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) =
    match l with
    | C                      -> header_c.Declare_Boolean ()
    | Ada                    -> header_a.Declare_BOOLEAN ()    

let createAcnNull (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) =
    match l with
    | C                      -> header_c.Declare_NullType ()
    | Ada                    -> header_a.Declare_NULL ()

let createBoolean (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Boolean)   (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id

    let typeDefinitionBody                       =
                    //match baseDefinition with 
                    //| Some baseType     -> baseType.name
                    //| _    ->
                        match l with
                        | C                      -> header_c.Declare_Boolean ()
                        | Ada                    -> header_a.Declare_BOOLEAN ()

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        

    }

let createReal (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Real)   (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    let typeDefinitionBody                       =
                    //match baseDefinition with 
                    //| Some baseType     -> baseType.name
                    //| _    ->
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

let createString (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.StringType)  (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    let arraySize = Some(o.maxSize+1)
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            let typeDefinitionBody                       =
                //match baseDefinition with 
                //| Some baseType     -> baseType.name
                //| _                 -> 
                    header_c.Declare_IA5String ()
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName arraySize [], typeDefinitionBody, None
        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let completeDefintion = header_a.IA5STRING_OF_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (BigInteger (o.maxSize + 1)) (o.uperCharSet |> Array.map(fun c -> (BigInteger (int c))))
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName arraySize [], typeDefinitionBody, None

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = arraySize
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        

    }

let createOctet (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.OctetString)  (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            //match baseDefinition with
            //| None  ->
                let typeDefinitionBody = header_c.Declare_OctetString (o.minSize=o.maxSize) (BigInteger o.maxSize)
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
                completeDefintion, typeDefinitionName, Some completeDefintion
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let completeDefintion = header_a.OCTET_STRING_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (o.maxSize=o.minSize)
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        

    }

let createBitString (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.BitString)   (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            //match baseDefinition with 
            //| None              -> 
                let typeDefinitionBody = header_c.Declare_BitString (o.minSize=o.maxSize) (BigInteger o.MaxOctets) (BigInteger o.maxSize)
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
                completeDefintion, typeDefinitionName, Some completeDefintion
            //| Some baseType     -> 
            //    let typeDefinitionBody = baseType.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let completeDefintion = header_a.BIT_STRING_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (o.maxSize=o.minSize)
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        

    }

let createNull (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.NullType)  (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    let typeDefinitionBody                       =
                    //match baseDefinition with 
                    //| Some baseType     -> baseType.name
                    //| _    ->
                        match l with
                        | C                      -> header_c.Declare_NullType ()
                        | Ada                    -> header_a.Declare_NULL ()

    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None []
        typeDefinitionBodyWithinSeq              = typeDefinitionBody
        completeDefinitionWithinSeq              = None
        

    }


let createEnumerated (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Enumerated)  (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    let completeDefintion, typeDefinitionBodyWithinSeq, completeDefinitionWithinSeq =
        match l with
        | C                      -> 
            let items = 
                match o.userDefinedValues with
                | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.definitionValue)
                | false -> o.items |> List.map( fun i -> i.getBackendName l)
            let typeDefinitionBody                       =
                //match baseDefinition with 
                //| Some baseType     -> baseType.name
                //| _                 -> 
                header_c.Declare_Enumerated items
            getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let orderedItems = o.items |> List.sortBy(fun i -> i.definitionValue)
                let arrsEnumNames = orderedItems |> List.map( fun i -> i.getBackendName l)
                let arrsEnumNamesAndValues = orderedItems |> List.map( fun i -> header_a.ENUMERATED_tas_decl_item (i.getBackendName l) i.definitionValue)
                let nIndexMax = BigInteger ((Seq.length o.items)-1)
                let completeDefintion = header_a.ENUMERATED_tas_decl typeDefinitionName arrsEnumNames arrsEnumNamesAndValues nIndexMax
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
        

    }

let createSequenceOf (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.SequenceOf)  (childDefinition:TypeDefinitionCommon) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
    
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
            //match baseDefinition with
            //| None  ->
                let typeDefinitionArrayPostfix = 
                    match childDefinition.arraySize with 
                    | None -> "" 
                    | Some x -> sprintf "[%d]" x

                let typeDefinitionBody = header_c.Declare_SequenceOf (o.minSize = o.maxSize) childDefinition.typeDefinitionBodyWithinSeq (BigInteger o.maxSize) typeDefinitionArrayPostfix
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None

        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let completeDefintion = header_a.SEQUENCE_OF_tas_decl typeDefinitionName (BigInteger o.minSize) (BigInteger o.maxSize) (o.minSize = o.maxSize) childDefinition.typeDefinitionBodyWithinSeq childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None


    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
    }

let createSequence (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Sequence)  (children:SeqChildInfo list) (us:State) =
    let children = children |> List.choose (fun c -> match c with Asn1Child z -> Some z | _ -> None)
    let handleChild (o:Asn1Child) =
        match l with
        | C->
            let typeDefinitionArrayPostfix = match o.Type.typeDefinition.arraySize with None -> "" | Some x -> (sprintf "[%d]" x)
            Some (header_c.PrintSeq_ChoiceChild o.Type.typeDefinition.typeDefinitionBodyWithinSeq o.c_name typeDefinitionArrayPostfix)
        | Ada  ->
            Some (header_a.SEQUENCE_tas_decl_child o.c_name o.Type.typeDefinition.typeDefinitionBodyWithinSeq)

    let typeDefinitionName = getTypeDefinitionName r l t.id
    let childldrenCompleteDefintions =
        match createInnerTypes l with
        | true  -> (children |> List.choose (fun c -> c.Type.typeDefinition.completeDefinitionWithinSeq))
        | false -> (children |> List.choose (fun c -> c.Type.typeDefinition.completeDefinitionWithinSeq))
    
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
            //match baseDefinition with
            //| None  ->
                let childrenBodies = children |> List.choose handleChild
                let optChildNames  = children |> List.choose(fun c -> match c.Optionality with Some _ -> Some c.Name.Value | None -> None)
                let typeDefinitionBody = header_c.Declare_Sequence childrenBodies optChildNames
                let completeDefintion = getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None
        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let childrenBodies = children |> List.choose handleChild
                let optChildren  = children |> List.choose(fun c -> match c.Optionality with Some _ -> Some(header_a.SEQUENCE_tas_decl_child_bit c.Name.Value) | None -> None)
                let completeDefintion = header_a.SEQUENCE_tas_decl typeDefinitionName childrenBodies optChildren childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion) 
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None


    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
    }

let createChoice (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Choice)  (children:ChChildInfo list) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l t.id
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
            //match baseDefinition with
            //| None  ->
                let completeDefintion = 
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    let typeDefinitionBody = header_c.Declare_Choice (choiceIDForNone t.id) chEnms childrenBodies 
                    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion)
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None

        | Ada                    -> 
            //match baseDefinition with
            //| None  ->
                let completeDefintion = 
                    let chEnms = children |> List.map(fun c -> c.presentWhenName)
                    let childrenBodies = children |> List.map handleChild
                    let nIndexMax = BigInteger ((Seq.length children)-1)
                    header_a.CHOICE_tas_decl typeDefinitionName children.Head.presentWhenName childrenBodies chEnms nIndexMax childldrenCompleteDefintions
                completeDefintion, typeDefinitionName, (Some completeDefintion)
            //| Some baseTypeName     ->
            //    let typeDefinitionBody = baseTypeName.name
            //    getCompleteDefinition l SUBTYPE typeDefinitionBody typeDefinitionName None [], typeDefinitionBody, None



    {
        TypeDefinitionCommon.name                = typeDefinitionName
        typeOrSubsType                           = SUBTYPE
        arraySize                                = None
        completeDefinition                       = completeDefintion
        typeDefinitionBodyWithinSeq              = typeDefinitionBodyWithinSeq
        completeDefinitionWithinSeq              = completeDefinitionWithinSeq
    } 



let createReferenceType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.ReferenceType)  (baseType:Asn1Type ) (us:State) =
    match o.resolvedType.Kind with
    | Asn1AcnAst.Integer ii   when ii.isUnsigned ->
        createInteger r l o.resolvedType  ii   us
    | _             ->
        let typeDefinitionName = 
            match t.tasInfo with
            | Some tasInfo    -> ToC2(r.args.TypePrefix + tasInfo.tasName)
            | None            -> ToC2(r.args.TypePrefix + o.tasName.Value)
        let refTypeAssignment = ToC2(r.args.TypePrefix + o.tasName.Value)
        let completeDefinition                       = getCompleteDefinition l SUBTYPE refTypeAssignment typeDefinitionName None []
        {
            TypeDefinitionCommon.name                = typeDefinitionName
            typeOrSubsType                           = SUBTYPE
            arraySize                                = None
            completeDefinition                       = completeDefinition
            typeDefinitionBodyWithinSeq              = typeDefinitionName
            completeDefinitionWithinSeq              = None
        } 
