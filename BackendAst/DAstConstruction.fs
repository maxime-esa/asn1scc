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

let getTypeDefinitionName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName))

let getEqualFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_Equal"))

let createInteger (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer)  (newBase:Integer option) (us:State) =
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualBody v1 v2= 
        match l with
        | C         -> Some (sprintf "%s == %s" v1 v2)
        | Ada       -> Some (sprintf "%s = %s" v1 v2)
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
                    | C     -> 
                        match isEqualBody "val1" "val2" with
                        | Some bd -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualPrimitive isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | Ada   -> None
                typeDefinitionBody  = 
                    match newBase with 
                    | Some baseType when baseType.typeDefinitionName.IsSome
                                    -> baseType.typeDefinitionName.Value
                    | _    ->
                        match l with
                        | C    when o.IsUnsigned -> header_c.Declare_Integer ()
                        | C                      -> header_c.Declare_Integer ()
                        | Ada                    -> header_a.Declare_Integer ()
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

let createReal (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real)  (newBase:Real option) (us:State) : (Real*State) =
    raise(Exception "Not Implemented yet")

let createString (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType)  (newBase:StringType option) (us:State) : (StringType*State) =
    raise(Exception "Not Implemented yet")

let createOctet (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString)  (newBase:OctetString option) (us:State) : (OctetString*State) =
    raise(Exception "Not Implemented yet")

let createBitString (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString)  (newBase:BitString option) (us:State) : (BitString*State) =
    raise(Exception "Not Implemented yet")

let createNullType (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.NullType)  (newBase:NullType option) (us:State) : (NullType*State) =
    raise(Exception "Not Implemented yet")

let createBoolean (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean)  (newBase:Boolean option) (us:State) : (Boolean*State) =
    raise(Exception "Not Implemented yet")

let createEnumerated (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated)  (newBase:Enumerated option) (us:State) : (Enumerated*State) =
    raise(Exception "Not Implemented yet")


let createSequenceOf (r:CAst.AstRoot) (l:ProgrammingLanguage) (childType:Asn1Type) (o:CAst.SequenceOf)  (newBase:SequenceOf option) (us:State) : (SequenceOf*State) =
    //let curLever = us.curSeqOfLevel + 1
    //let us = {us with curSeqOfLevel = curLever}
    let curLever = o.id.SeqeuenceOfLevel + 1
    let typeDefinitionName = getTypeDefinitionName r l o.tasInfo
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let i = sprintf "i%d" curLever
    let isEqualBody   (v1:string) (v2:string) (childAccess: string) = 
        let soInnerStatement = 
            let childAccesPath v = v + childAccess + "arr[" + i + "]"
            match childType.isEqualBody with
            | Expression, func  ->  
                match func (childAccesPath v1) (childAccesPath v2) with
                | Some exp  -> Some (sprintf "ret = (%s);" exp)
                | None      -> None
            | Statement,  func   -> func (childAccesPath v1) (childAccesPath v2)
        if (o.minSize = o.maxSize && soInnerStatement.IsNone) then
            None
        else
            Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) soInnerStatement)

    let ret : SequenceOf = 
            {
                SequenceOf.id          = o.id
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
                    | C                      -> header_c.Declare_SequenceOf (o.minSize = o.maxSize) childType.typeDefinitionBody (BigInteger o.maxSize) typeDefinitionArrayPostfix
                    | Ada                    -> ""
                childType           = childType
                isEqualFunc         =
                    match l with
                    | C     -> 
                        match isEqualBody "pVal1" "pVal2" "->" with
                        | Some bd -> typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualSequence isEqualFuncName.Value typeDefName bd)
                        | None     -> None
                    | Ada   -> None
                isEqualFuncName     = isEqualFuncName
                isEqualBodyStats    = (fun v1 v2 -> isEqualBody v1 v2 ".")
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createSequenceChild (r:CAst.AstRoot) (l:ProgrammingLanguage)  (o:CAst.SeqChildInfo)  (newChild:Asn1Type) (us:State) : (SeqChildInfo*State) =
    let c_name = ToC o.name
    let isEqualBody   (v1:string) (v2:string) (childAccess: string) = 
        match l with
        | C         -> 
            let sInnerStatement = 
                match newChild.isEqualBody with
                | Expression, func  ->  
                    match func (v1 + childAccess + c_name) (v2 + childAccess + c_name) with
                    | Some exp  -> Some (sprintf "ret = (%s);" exp)
                    | None      -> None
                | Statement,  func   -> func (v1 + childAccess + c_name) (v2 + childAccess + c_name)
            equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name sInnerStatement

        | Ada       -> sprintf "%s = %s" v1 v2
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
                | C                      -> Some (header_c.PrintSeq_ChoiceChild newChild.typeDefinitionBody c_name typeDefinitionArrayPostfix)
                | Ada                    -> None
            | true                       -> None
        isEqualBodyStats = isEqualBody
    }, us

let createSequence (r:CAst.AstRoot) (l:ProgrammingLanguage) (children:SeqChildInfo list) (o:CAst.Sequence)  (newBase:Sequence option) (us:State) : (Sequence*State) =
    let typeDefinitionName  = getTypeDefinitionName r l o.tasInfo
    let isEqualFuncName     = getEqualFuncName r l o.tasInfo
    let isEqualBody   (v1:string) (v2:string) (childAccess: string) = 
        let printChild (c:SeqChildInfo) (sNestedContent:string option) = 
            let content = c.isEqualBodyStats v1 v2 childAccess
            match sNestedContent with
            | None  -> content
            | Some c-> equal_c.JoinItems content sNestedContent 
        let rec printChildren children = 
            match children with
            |[]     -> None
            |x::xs  -> Some (printChild x  (printChildren xs))
        
        
        printChildren (children |> List.filter(fun c -> not c.acnInsertetField))
            

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
                    | C                      -> header_c.Declare_Sequence childrenBodies optChildNames
                    | Ada                    -> ""
                isEqualFuncName     = isEqualFuncName
                isEqualFunc         =
                    match l with
                    | C     -> 
                        match isEqualBody "pVal1" "pVal2" "->" with
                        | None  -> None
                        | Some bodyEqual ->
                            typeDefinitionName |> Option.map(fun typeDefName -> equal_c.PrintEqualSequence isEqualFuncName.Value typeDefName bodyEqual)
                    | Ada   -> None

                isEqualBodyStats     = (fun v1 v2 -> isEqualBody v1 v2 ".")
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createChoiceChild (r:CAst.AstRoot) (l:ProgrammingLanguage)  (o:CAst.ChChildInfo)  (newChild:Asn1Type) (us:State) : (ChChildInfo*State) =
    {
        ChChildInfo.name   = o.name
        chType              = newChild
        comments            = o.comments
        presenseIsHandleByExtField = o.presenseIsHandleByExtField
    }, us

let createChoice (r:CAst.AstRoot) (l:ProgrammingLanguage) (children:ChChildInfo list) (o:CAst.Choice)  (newBase:Choice option) (us:State) : (Choice*State) =
    raise(Exception "Not Implemented yet")


let mapCTypeToDType (r:CAst.AstRoot) (l:ProgrammingLanguage) (t:CAst.Asn1Type)  (initialSate:State) =
   
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

let DoWork (r:CAst.AstRoot) (l:ProgrammingLanguage) =
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



