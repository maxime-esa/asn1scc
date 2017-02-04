module DAstConstruction
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst

type State = {
    curSeqOfLevel : int
    currentTypes  : Asn1Type list

}

let getTypeDefinitionName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName))

let getEqualFuncName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_Equal"))

let createInteger (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Integer)  (newBase:Integer option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = (DAstEqual.isEqualBodyPrimitive l)
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let ret = 
            {
                Integer.id          = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                uperRange           = o.uperRange
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "val1" "val2" with
                        | Some (bd,_) -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualPrimitive isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome
                                    -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C    when o.IsUnsigned -> header_c.Declare_Integer ()
                        | BAst.C                      -> header_c.Declare_Integer ()
                        | BAst.Ada                    -> header_a.Declare_Integer ()
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp      = isEqualBody
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us

let createReal (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Real)  (newBase:Real option) (us:State) : (Real*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = (DAstEqual.isEqualBodyPrimitive l)
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let ret = 
            {
                Real.id             = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                uperRange           = o.uperRange
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "val1" "val2" with
                        | Some (bd,_) -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualPrimitive isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome
                                    -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        |BAst.C                      -> header_c.Declare_Real ()
                        |BAst.Ada                    -> header_a.Declare_REAL ()
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp      = isEqualBody
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createString (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.StringType)  (newBase:StringType option) (us:State) : (StringType*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = DAstEqual.isEqualBodyString l
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let typeDefinitionArrayPostfix = sprintf "[%d]" (o.maxSize+1)
    let ret : StringType= 
            {
                StringType.id       = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                minSize             = o.minSize; 
                maxSize             = o.maxSize;
                charSet             = o.charSet
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "val1" "val2" with
                        | Some (bd,_) -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualPrimitive isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome  -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C                      -> 
                                header_c.Declare_IA5String ()
                        | BAst.Ada                    -> "????"//header_a.IA5STRING_OF_tas_decl ()
                typeDefinitionArrayPostfix = typeDefinitionArrayPostfix
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp      = isEqualBody
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createOctet (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.OctetString)  (newBase:OctetString option) (us:State) : (OctetString*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = DAstEqual.isEqualBodyOctetString l (BigInteger o.minSize) (BigInteger o.maxSize)
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let typeDefinitionArrayPostfix = sprintf "[%d]" o.maxSize
    let ret : OctetString= 
            {
                OctetString.id       = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                minSize             = o.minSize; 
                maxSize             = o.maxSize;
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome  -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C                      -> 
                                header_c.Declare_OctetString (o.minSize=o.maxSize) (BigInteger o.maxSize)
                        | BAst.Ada                    -> "????"//header_a.IA5STRING_OF_tas_decl ()
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "->" "pVal1" "pVal2" with
                        | Some (bd, _) -> 
                            typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualOctBit isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp    = isEqualBody "."
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createBitString (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.BitString)  (newBase:BitString option) (us:State) : (BitString*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = DAstEqual.isEqualBodyBitString l (BigInteger o.minSize) (BigInteger o.maxSize)
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let typeDefinitionArrayPostfix = sprintf "[%d]" o.maxSize
    let ret : BitString= 
            {
                BitString.id       = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                minSize             = o.minSize; 
                maxSize             = o.maxSize;
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome  -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C                      -> 
                                header_c.Declare_BitString (o.minSize=o.maxSize) (BigInteger o.MaxOctets) (BigInteger o.maxSize)
                        | BAst.Ada                    -> "????"//header_a.IA5STRING_OF_tas_decl ()
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "->" "pVal1" "pVal2" with
                        | Some (bd, _) -> 
                            typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualOctBit isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp    = isEqualBody "."
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createNullType (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.NullType)  (newBase:NullType option) (us:State) : (NullType*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = fun  v1 v2 -> None
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let ret : NullType= 
            {
                NullType.id          = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                isEqualFunc         = None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome
                                    -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_NullType ()
                        | BAst.Ada                    -> header_a.Declare_NULL ()
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp      = isEqualBody
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us
let createBoolean (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Boolean)  (newBase:Boolean option) (us:State) : (Boolean*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = (DAstEqual.isEqualBodyPrimitive l)
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let ret : Boolean= 
            {
                Boolean.id          = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "val1" "val2" with
                        | Some (bd,_) -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualPrimitive isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome
                                    -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_Boolean ()
                        | BAst.Ada                    -> header_a.Declare_BOOLEAN ()
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp      = isEqualBody
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us

let createEnumerated (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Enumerated)  (newBase:Enumerated option) (us:State) : (Enumerated*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody = (DAstEqual.isEqualBodyPrimitive l)
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)

    let ret : Enumerated= 
            {
                Enumerated.id          = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                items               = o.items
                userDefinedValues   = o.userDefinedValues
                cons                = o.cons
                withcons            = o.withcons
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                enumEncodingClass    = o.enumEncodingClass
                typeDefinitionName  = typeDefinitionName
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "val1" "val2" with
                        | Some (bd,_) -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualPrimitive isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | BAst.Ada   -> None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome
                                    -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | BAst.C                      -> header_c.Declare_Enumerated items
                        | BAst.Ada                    -> header_a.Declare_Integer ()
                isEqualFuncName     = isEqualFuncName
                isEqualBodyExp      = isEqualBody
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createSequenceOf (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (childType:Asn1Type) (o:CAst.SequenceOf)  (newBase:SequenceOf option) (us:State) : (SequenceOf*State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let isEqualBody   = DAstEqual.isEqualBodySequenceOf childType o l
    let ret : SequenceOf = 
            {
                SequenceOf.id       = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                cons                = o.cons
                withcons            = o.withcons
                minSize             = o.minSize
                maxSize             = o.maxSize
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinitionName  = typeDefinitionName
                typeDefinitionBody  = 
                    let typeDefinitionArrayPostfix = match childType.typeDefinitionArrayPostfix with None -> "" | Some x -> x

                    match l with
                    | BAst.C                      -> header_c.Declare_SequenceOf (o.minSize = o.maxSize) childType.typeDefinitionBody (BigInteger o.maxSize) typeDefinitionArrayPostfix
                    | BAst.Ada                    -> ""
                childType           = childType
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "->" "pVal1" "pVal2"  with
                        | Some (bd, lvars) -> 
                            let lvars = lvars |> List.map(fun lv -> lv.GetDeclaration l) |> Seq.distinct
                            typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualComposite isEqualFuncName.Value typeDefName bd lvars)
                        | None     -> None
                    | BAst.Ada   -> None
                isEqualFuncName     = isEqualFuncName
                isEqualBodyStats    = (fun v1 v2 -> isEqualBody "." v1 v2 )
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createSequenceChild (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage)  (o:CAst.SeqChildInfo)  (newChild:Asn1Type) (us:State) : (SeqChildInfo*State) =
    let c_name = ToC o.name
    
    {
        SeqChildInfo.name   = o.name
        chType              = newChild
        optionality         = o.optionality
        acnInsertetField    = o.acnInsertetField
        comments            = o.comments
        c_name              = c_name
        typeDefinitionBody  = 
            match o.acnInsertetField with
            | false ->
                let typeDefinitionArrayPostfix = match newChild.typeDefinitionArrayPostfix with None -> "" | Some x -> x
                match l with
                | BAst.C                      -> Some (header_c.PrintSeq_ChoiceChild newChild.typeDefinitionBody c_name typeDefinitionArrayPostfix)
                | BAst.Ada                    -> None
            | true                       -> None
        isEqualBodyStats = DAstEqual.isEqualBodySequenceChild l o newChild
    }, us

let createSequence (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (children:SeqChildInfo list) (o:CAst.Sequence)  (newBase:Sequence option) (us:State) : (Sequence*State) =
    let typeDefinitionName  = getTypeDefinitionName r l o.tasInfo
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let isEqualBody   = DAstEqual.isEqualBodySequence l children
            

    let ret : Sequence= 
            {
                Sequence.id         = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                children            = children
                cons                = o.cons
                withcons            = o.withcons
                baseType            = newBase
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment

                typeDefinitionName  = typeDefinitionName
                typeDefinitionBody  = 
                    let childrenBodies = children |> List.choose(fun c -> c.typeDefinitionBody)
                    let optChildNames  = children |> List.choose(fun c -> match c.optionality with Some _ -> Some c.name | None -> None)
                    match l with
                    | BAst.C                      -> header_c.Declare_Sequence childrenBodies optChildNames
                    | BAst.Ada                    -> ""
                isEqualFuncName     = isEqualFuncName
                isEqualFunc         =
                    match l with
                    | BAst.C     -> 
                        match isEqualBody "->" "pVal1" "pVal2"  with
                        | None  -> None
                        | Some (bodyEqual, lvars) ->
                            let lvars = lvars |> List.map(fun lv -> lv.GetDeclaration l) |> Seq.distinct
                            typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualComposite isEqualFuncName.Value typeDefName bodyEqual lvars)
                    | BAst.Ada   -> None

                isEqualBodyStats     = (fun v1 v2 -> isEqualBody "." v1 v2 )
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createChoiceChild (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage)  (o:CAst.ChChildInfo)  (newChild:Asn1Type) (us:State) : (ChChildInfo*State) =
    {
        ChChildInfo.name   = o.name
        chType              = newChild
        comments            = o.comments
        presenseIsHandleByExtField = o.presenseIsHandleByExtField
    }, us

let createChoice (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (children:ChChildInfo list) (o:CAst.Choice)  (newBase:Choice option) (us:State) : (Choice*State) =
    raise(Exception "Not Implemented yet")


let mapCTypeToDType (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (t:CAst.Asn1Type)  (initialSate:State) =
   
    CAstFold.foldAsn1Type
        t
        initialSate

        (fun o newBase us -> createInteger r l o newBase us)
        Integer

        (fun o newBase us -> createReal r l o newBase us)
        Real

        (fun o newBase us -> createString r l o newBase us)
        IA5String

        (fun o newBase us -> createOctet r l o newBase us)
        OctetString

        (fun o newBase us -> createNullType r l o newBase us)
        NullType

        (fun o newBase us -> createBitString r l o newBase us)
        BitString

        (fun o newBase us -> createBoolean r l o newBase us)
        Boolean

        (fun o newBase us -> createEnumerated r l o newBase us)
        Enumerated

        (fun childType o newBase us -> createSequenceOf r l childType o newBase us)
        SequenceOf

        //sequence
        (fun o newChild us -> createSequenceChild r l o newChild us)
        (fun children o newBase us -> createSequence r l children o newBase us)
        Sequence

        //Choice
        (fun o newChild us -> createChoiceChild r l o newChild us)
        (fun children o newBase us -> createChoice r l children o newBase us)
        Choice

let foldMap = CloneTree.foldMap

let DoWork (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) =
    let initialState = {State.currentTypes = []; curSeqOfLevel=0}
    let newTypeAssignments, finalState = 
        r.TypeAssignments |>
        foldMap (fun cs t ->
            let newType, newState = mapCTypeToDType r l t cs
            newType, {newState with currentTypes = newState.currentTypes@[newType]}
        ) initialState  
    let newTypes = finalState.currentTypes
    let newTypesMap = newTypes |> List.map(fun t -> t.id, t) |> Map.ofList
    let programUnits = DAstProgramUnit.createProgramUnits r.Files newTypesMap newTypeAssignments r.ValueAssignments l
    {
        AstRoot.Files = r.Files
        Encodings = r.Encodings
        GenerateEqualFunctions = r.GenerateEqualFunctions
        TypePrefix = r.TypePrefix
        AstXmlAbsFileName = r.AstXmlAbsFileName
        IcdUperHtmlFileName = r.IcdUperHtmlFileName
        IcdAcnHtmlFileName = r.IcdAcnHtmlFileName
        CheckWithOss = r.CheckWithOss
        mappingFunctionsModule = r.mappingFunctionsModule
        valsMap  = r.valsMap
        typesMap = newTypesMap
        TypeAssignments = newTypeAssignments
        ValueAssignments = r.ValueAssignments
        integerSizeInBytes = r.integerSizeInBytes
        acnParameters = r.acnParameters
        acnConstants = r.acnConstants
        acnLinks = r.acnLinks
        programUnits= programUnits
    }



