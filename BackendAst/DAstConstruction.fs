module DAstConstruction
open System
open System.Numerics
open System.IO
open DAstTypeDefinition
open FsUtils
open Constraints
open DAst
open uPER2

type State = {
    curSeqOfLevel : int
    currentTypes  : Asn1Type list

}

let getTypeDefinitionName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName))

let getEqualFuncName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_Equal"))

let createInteger (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Integer)  (newBase:Integer option) (us:State) =
    let typeDefinition      = createIntegerTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
    let ret : Integer = 
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createIntegerEqualFunction r l o typeDefinition
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us

let createReal (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Real)  (newBase:Real option) (us:State) : (Real*State) =
    let typeDefinition      = createRealTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createRealEqualFunction r l o typeDefinition
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createString (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.StringType)  (newBase:StringType option) (us:State) : (StringType*State) =
    let typeDefinition      = createStringTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createStringEqualFunction r l o typeDefinition
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createOctet (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.OctetString)  (newBase:OctetString option) (us:State) : (OctetString*State) =
    let typeDefinition      = createOctetTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createOctetStringEqualFunction r l o typeDefinition
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createBitString (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.BitString)  (newBase:BitString option) (us:State) : (BitString*State) =
    let typeDefinition      = createBitStringTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createBitStringEqualFunction r l o typeDefinition

                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, us

let createNullType (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.NullType)  (newBase:NullType option) (us:State) : (NullType*State) =
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
                typeDefinition      = createNullTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
                equalFunction       = DAstEqual.createNullTypeEqualFunction r l o 
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us
let createBoolean (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Boolean)  (newBase:Boolean option) (us:State) : (Boolean*State) =
    let typeDefinition      = createBooleanTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createBooleanEqualFunction r l o typeDefinition
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us

let createEnumerated (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Enumerated)  (newBase:Enumerated option) (us:State) : (Enumerated*State) =
    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)
    let typeDefinition      = createEnumeratedTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) ds

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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createEnumeratedEqualFunction r l o typeDefinition
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createSequenceOf (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (childType:Asn1Type) (o:CAst.SequenceOf)  (newBase:SequenceOf option) (us:State) : (SequenceOf*State) =
    let typeDefinition      = createSequenceOfTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) childType.typeDefinition ds
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
                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createSequenceOfEqualFunction r l o typeDefinition childType
                childType           = childType
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
        isEqualBodyStats = DAstEqual.isEqualBodySequenceChild l o newChild
    }, us

let createSequence (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (children:SeqChildInfo list) (o:CAst.Sequence)  (newBase:Sequence option) (us:State) : (Sequence*State) =
    let typeDefinition      = createSequenceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children ds

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

                typeDefinition      = createSequenceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children ds
                equalFunction       = DAstEqual.createSequenceEqualFunction r l o typeDefinition children

                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


let createChoiceChild (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage)  (o:CAst.ChChildInfo)  (newChild:Asn1Type) (us:State) : (ChChildInfo*State) =
    let c_name = ToC o.name
    {
        ChChildInfo.name   = o.name
        chType              = newChild
        comments            = o.comments
        presenseIsHandleByExtField = o.presenseIsHandleByExtField
        c_name              = c_name
        presentWhenName     = o.presentWhenName

        isEqualBodyStats = DAstEqual.isEqualBodyChoiceChild l o newChild
    }, us

let createChoice (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (children:ChChildInfo list) (o:CAst.Choice)  (newBase:Choice option) (us:State) : (Choice*State) =
    let typeDefinition      = createChoiceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children ds
    let ret : Choice= 
            {
                Choice.id           = o.id
                tasInfo             = o.tasInfo
                uperMaxSizeInBits   = o.uperMaxSizeInBits
                uperMinSizeInBits   = o.uperMinSizeInBits
                children            = children
                cons                = o.cons
                withcons            = o.withcons
                baseType            = newBase
                Location            = o.Location  
                choiceIDForNone     = o.choiceIDForNone
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                acnEncodingClass    = o.acnEncodingClass
                alignment           = o.alignment

                typeDefinition      = typeDefinition
                equalFunction       = DAstEqual.createChoiceEqualFunction r l o typeDefinition children
                isValidFuncName     = None
                isValidBody         = None
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, us


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



