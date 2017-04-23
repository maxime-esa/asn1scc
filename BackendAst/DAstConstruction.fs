module DAstConstruction
open System
open System.Numerics
open System.IO
open DAstTypeDefinition
open FsUtils
open Constraints
open DAst
open uPER2


let getTypeDefinitionName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName))

let getEqualFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_Equal"))

let createInteger (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer)  (newBase:Integer option) (us:State) =
    let typeDefinition      = createIntegerTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createIntegerFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = newBase |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = newBase |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createIntegerFunction r l Ast.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIntegerFunction r l Ast.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
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
                equalFunction       = DAstEqual.createIntegerEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                acnFunction         = DAstACN.createIntegerFunction r l o typeDefinition
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s3

let createReal (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real)  (newBase:Real option) (us:State) : (Real*State) =
    let typeDefinition      = createRealTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let isValidFunction, s1     = DAstValidate.createRealFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = newBase |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = newBase |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createRealFunction r l Ast.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createRealFunction r l Ast.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2

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
                equalFunction       = DAstEqual.createRealEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, s3

let createString (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType)  (newBase:StringType option) (us:State) : (StringType*State) =
    let typeDefinition      = createStringTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createStringFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = newBase |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = newBase |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createIA5StringFunction r l Ast.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIA5StringFunction r l Ast.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
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
                equalFunction       = DAstEqual.createStringEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, s3

let createOctet (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString)  (newBase:OctetString option) (us:State) : (OctetString*State) =
    let typeDefinition          = createOctetTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let equalFunction       = DAstEqual.createOctetStringEqualFunction r l o typeDefinition baseTypeEqFunc
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createOctetStringFunction r l o typeDefinition baseTypeValFunc equalFunction us
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
                equalFunction       = equalFunction
                isValidFunction     = isValidFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, s1

let createBitString (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString)  (newBase:BitString option) (us:State) : (BitString*State) =
    let typeDefinition      = createBitStringTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let equalFunction = DAstEqual.createBitStringEqualFunction r l o typeDefinition baseTypeEqFunc
    let isValidFunction, s1     = DAstValidate.createBitStringFunction r l o typeDefinition baseTypeValFunc equalFunction us
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
                equalFunction       = DAstEqual.createBitStringEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, s1

let createNullType (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.NullType)  (newBase:NullType option) (us:State) : (NullType*State) =
    let typeDefinition      = createNullTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeEncUperFunc     = newBase |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = newBase |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s1     = DAstUPer.createNullTypeFunction r l Ast.Codec.Encode o typeDefinition baseTypeEncUperFunc None us
    let uperDecFunction, s2     = DAstUPer.createNullTypeFunction r l Ast.Codec.Decode o typeDefinition baseTypeDecUperFunc None s1
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
                typeDefinition      = typeDefinition 
                equalFunction       = DAstEqual.createNullTypeEqualFunction r l o 
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s2

let createBoolean (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean)  (newBase:Boolean option) (us:State) : (Boolean*State) =
    let typeDefinition      = createBooleanTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createBoolFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = newBase |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = newBase |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createBooleanFunction r l Ast.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBooleanFunction r l Ast.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
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
                equalFunction       = DAstEqual.createBooleanEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s3

let createEnumerated (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated)  (newBase:Enumerated option) (us:State) : (Enumerated*State) =
    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)
    let typeDefinition      = createEnumeratedTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createEnumeratedFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = newBase |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = newBase |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createEnumeratedFunction r l Ast.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createEnumeratedFunction r l Ast.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2

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
                equalFunction       = DAstEqual.createEnumeratedEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s3


let createSequenceOf (r:CAst.AstRoot) (l:ProgrammingLanguage) (childType:Asn1Type) (o:CAst.SequenceOf)  (newBase:SequenceOf option) (us:State) : (SequenceOf*State) =
    let typeDefinition      = createSequenceOfTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) childType.typeDefinition us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createSequenceOfFunction r l o typeDefinition childType baseTypeValFunc us
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
                equalFunction       = DAstEqual.createSequenceOfEqualFunction r l o typeDefinition childType baseTypeEqFunc
                isValidFunction     = isValidFunction
                childType           = childType
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s1


let createSequenceChild (r:CAst.AstRoot) (l:ProgrammingLanguage)  (o:CAst.SeqChildInfo)  (newChild:Asn1Type) (us:State) : (SeqChildInfo*State) =
    {
        SeqChildInfo.name   = o.name
        chType              = newChild
        optionality         = o.optionality
        acnInsertetField    = o.acnInsertetField
        comments            = o.comments
        c_name              = o.c_name
        isEqualBodyStats    = DAstEqual.isEqualBodySequenceChild l o newChild
        isValidBodyStats    = DAstValidate.isValidSequenceChild l o newChild
    }, us

let createSequence (r:CAst.AstRoot) (l:ProgrammingLanguage) (children:SeqChildInfo list) (o:CAst.Sequence)  (newBase:Sequence option) (us:State) : (Sequence*State) =
    let typeDefinition          = createSequenceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createSequenceFunction r l o typeDefinition children baseTypeValFunc us

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
                typeDefinition      = createSequenceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children us
                equalFunction       = DAstEqual.createSequenceEqualFunction r l o typeDefinition children baseTypeEqFunc
                isValidFunction     = isValidFunction

                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s1


let createChoiceChild (r:CAst.AstRoot) (l:ProgrammingLanguage)  (o:CAst.ChChildInfo)  (newChild:Asn1Type) (us:State) : (ChChildInfo*State) =
    let typeDefinitionName = 
        let longName = newChild.id.AcnAbsPath.Tail |> List.rev |> List.tail |> List.rev |> Seq.StrJoin "_"
        ToC2(r.TypePrefix + longName.Replace("#","elem"))

    {
        ChChildInfo.name   = o.name
        chType              = newChild
        comments            = o.comments
        presenseIsHandleByExtField = o.presenseIsHandleByExtField
        c_name              = o.c_name
        presentWhenName     = o.presentWhenName
        isEqualBodyStats = DAstEqual.isEqualBodyChoiceChild typeDefinitionName l o newChild
        isValidBodyStats = DAstValidate.isValidChoiceChild l o newChild
    }, us

let createChoice (r:CAst.AstRoot) (l:ProgrammingLanguage) (children:ChChildInfo list) (o:CAst.Choice)  (newBase:Choice option) (us:State) : (Choice*State) =
    let typeDefinition = createChoiceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children us
    let baseTypeEqFunc  = newBase |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match newBase with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createChoiceFunction r l o typeDefinition children baseTypeValFunc us
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
                equalFunction       = DAstEqual.createChoiceEqualFunction r l o typeDefinition children baseTypeEqFunc
                isValidFunction     = isValidFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s1


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

let treeCollect (r:CAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1Type)  (initialSate:State) =
    DastFold.foldAsn1Type
        t
        initialSate

        (fun o newBase us -> [Integer o], us)
        id
        (fun o newBase us -> [Real o], us)
        id
        (fun o newBase us -> [IA5String o], us)
        id
        (fun o newBase us -> [OctetString o], us)
        id
        (fun o newBase us -> [NullType o], us)
        id
        (fun o newBase us -> [BitString o], us)
        id
        (fun o newBase us -> [Boolean o], us)
        id
        (fun o newBase us -> [Enumerated o], us)
        id
        (fun childType o newBase us -> (SequenceOf o)::childType, us)
        id
        //sequence
        (fun o newChild us -> newChild, us)
        (fun children o newBase us -> (Sequence o)::(children |> List.collect id) ,us)
        id
        //Choice
        (fun o newChild us -> newChild, us)
        (fun children o newBase us -> (Choice o)::(children |> List.collect id) ,us)
        id


let foldMap = CloneTree.foldMap

let DoWork (r:CAst.AstRoot) (l:ProgrammingLanguage) =
    let initialState = {State.currentTypes = []; curSeqOfLevel=0; currErrCode = 1}
    let newTypeAssignments, finalState = 
        r.TypeAssignments |>
        foldMap (fun cs t ->
            let newType, newState = mapCTypeToDType r l t cs
            newType, {newState with currentTypes = newState.currentTypes@[newType]}
        ) initialState  
    let _,allTypes = 
        newTypeAssignments |>
        foldMap (fun cs t ->
            let newTypes, _ = treeCollect r l t initialState
            0, newTypes@cs
        ) []  
    //let newTypes = finalState.currentTypes
    let newTypesMap = allTypes |> List.map(fun t -> t.id, t) |> Map.ofList
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



