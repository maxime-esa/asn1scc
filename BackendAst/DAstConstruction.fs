module DAstConstruction
open System
open System.Numerics
open System.IO
open DAstTypeDefinition
open FsUtils
open CommonTypes
open DAst
open DAstUtilFunctions


let foldMap = Asn1Fold.foldMap

let createAsn1ValueFromValueKind (t:Asn1AcnAst.Asn1Type) i (v:Asn1ValueKind)  =
    {Asn1Value.kind = v;  loc  = t.Location; id  = (ReferenceToValue (t.id.ToScopeNodeList,[IMG i]))}

let private mapAcnParameter (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (prm:Asn1AcnAst.AcnParameter) (us:State) =
    let funcUpdateStatement, ns1 = DAstACN.getUpdateFunctionUsedInEncoding r deps l m prm.id us
    {
        AcnParameter.asn1Type = prm.asn1Type; 
        name = prm.name; 
        loc = prm.loc
        id = prm.id
        c_name = DAstACN.getAcnDeterminantName prm.id
        typeDefinitionBodyWithinSeq = DAstACN.getDeterminantTypeDefinitionBodyWithinSeq r l (Asn1AcnAst.AcnParameterDeterminant prm)

        funcUpdateStatement = funcUpdateStatement 
    }, ns1

let private createAcnChild (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (ch:Asn1AcnAst.AcnChild) (us:State) =
    let funcBodyEncode, ns1 = 
        match ch.Type with
        | Asn1AcnAst.AcnInteger  a -> DAstACN.createAcnIntegerFunction r l Codec.Encode ch.id a us
        | Asn1AcnAst.AcnBoolean  a -> DAstACN.createAcnBooleanFunction r l Codec.Encode ch.id a us
        | Asn1AcnAst.AcnNullType a -> DAstACN.createAcnNullTypeFunction r l Codec.Encode ch.id a us
        | Asn1AcnAst.AcnReferenceToEnumerated a -> DAstACN.createAcnEnumeratedFunction r l Codec.Encode ch.id a us
        | Asn1AcnAst.AcnReferenceToIA5String a -> DAstACN.createAcnStringFunction r deps l Codec.Encode ch.id a us
        
    let funcBodyDecode, ns2 = 
        match ch.Type with
        | Asn1AcnAst.AcnInteger  a -> DAstACN.createAcnIntegerFunction r l Codec.Decode ch.id a ns1
        | Asn1AcnAst.AcnBoolean  a -> DAstACN.createAcnBooleanFunction r l Codec.Decode ch.id a ns1
        | Asn1AcnAst.AcnNullType a -> DAstACN.createAcnNullTypeFunction r l Codec.Decode ch.id a us
        | Asn1AcnAst.AcnReferenceToEnumerated a -> DAstACN.createAcnEnumeratedFunction r l Codec.Decode ch.id a us
        | Asn1AcnAst.AcnReferenceToIA5String a -> DAstACN.createAcnStringFunction r deps l Codec.Decode ch.id a us
        
    let funcUpdateStatement, ns3 = DAstACN.getUpdateFunctionUsedInEncoding r deps l m ch.id ns2

    let ret = 
        {
        
            AcnChild.Name  = ch.Name
            id             = ch.id
            c_name         = DAstACN.getAcnDeterminantName ch.id
            Type           = ch.Type
            typeDefinitionBodyWithinSeq = DAstACN.getDeterminantTypeDefinitionBodyWithinSeq r l (Asn1AcnAst.AcnChildDeterminant ch)
            funcBody = fun codec -> match codec with Codec.Encode -> funcBodyEncode | Codec.Decode -> funcBodyDecode
            funcUpdateStatement = funcUpdateStatement
        }
    AcnChild ret, ns3

let private createInteger (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Integer) (us:State) =
    let typeDefinition = DAstTypeDefinition.createInteger  r l t o us
    let automaticTestCasesIntValues      = EncodeDecodeTestCase.IntegerAutomaticTestCaseValues r t o 
    let initialValue        = 
        match automaticTestCasesIntValues with
        | []    -> getValueByUperRange o.uperRange 0I
        | x::_  -> 
            match automaticTestCasesIntValues |> Seq.exists ((=) 0I) with
            |true    -> 0I
            |false   -> x
    let automaticTestCasesValues      = automaticTestCasesIntValues |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (IntegerValue x)) 
    let initFunction        = DAstInitialize.createIntegerInitFunc r l t o typeDefinition (IntegerValue initialValue)
    let equalFunction       = DAstEqual.createIntegerEqualFunction r l t o typeDefinition 
    let isValidFunction, s1     = DAstValidate.createIntegerFunction r l t o typeDefinition  us
    let uperEncFunction, s2     = DAstUPer.createIntegerFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIntegerFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createIntegerFunction r l Codec.Encode t o typeDefinition isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createIntegerFunction r l Codec.Decode t o typeDefinition isValidFunction uperDecFunction s4

    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let ret =
        {
            Integer.baseInfo    = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createIntegerFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues     = automaticTestCasesValues
        }
    ((Integer ret),[]), s7

let private createReal (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Real) (us:State) =
    let typeDefinition = DAstTypeDefinition.createReal  r l t o us
    let equalFunction       = DAstEqual.createRealEqualFunction r l t o typeDefinition 
    let initialValue        = getValueByUperRange o.uperRange 0.0
    let initFunction        = DAstInitialize.createRealInitFunc r l t o typeDefinition (RealValue initialValue)
    let isValidFunction, s1     = DAstValidate.createRealFunction r l t o typeDefinition  us
    let uperEncFunction, s2     = DAstUPer.createRealFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createRealFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createRealrFunction r l Codec.Encode t o typeDefinition isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createRealrFunction r l Codec.Decode t o typeDefinition isValidFunction uperDecFunction s4

    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.RealAutomaticTestCaseValues r t o |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (RealValue x)) 

    let ret =
        {
            Real.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createRealFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((Real ret),[]), s7



let private createStringType (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.StringType) (us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createString  r l t o us0
    let equalFunction       = DAstEqual.createStringEqualFunction r l t o typeDefinition 
    let initialValue        =
        let ch = 
            match o.uperCharSet |> Seq.exists((=) ' ') with
            | true  -> ' '
            | false -> o.uperCharSet |> Seq.find(fun c -> not (Char.IsControl c))
        System.String(ch, o.minSize)
    let initFunction        = DAstInitialize.createIA5StringInitFunc r l t o typeDefinition (StringValue initialValue)
    let isValidFunction, s1     = DAstValidate.createStringFunction r l t o typeDefinition  us
    let uperEncFunction, s2     = DAstUPer.createIA5StringFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIA5StringFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createStringFunction r deps l Codec.Encode t o typeDefinition isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createStringFunction r deps l Codec.Decode t o typeDefinition isValidFunction uperDecFunction s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.StringAutomaticTestCaseValues r t o |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (StringValue x)) 

    let ret =
        {
            StringType.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createStringFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    (ret,newPrms), s7


let private createOctetString (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.OctetString) (us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createOctet  r l t o us0
    let initialValue        =
        [1 .. o.minSize] |> List.map(fun i -> 0uy)
    let initFunction        = DAstInitialize.createOctetStringInitFunc r l t o typeDefinition (OctetStringValue initialValue)
    let equalFunction       = DAstEqual.createOctetStringEqualFunction r l t o typeDefinition 
    let printValue          = DAstVariables.createOctetStringFunction r l t o typeDefinition 

    let isValidFunction, s1     = DAstValidate.createOctetStringFunction r l t o typeDefinition  equalFunction printValue us
    let uperEncFunction, s2     = DAstUPer.createOctetStringFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createOctetStringFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createOctetStringFunction r deps l Codec.Encode t o typeDefinition isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createOctetStringFunction r deps l Codec.Decode t o typeDefinition isValidFunction uperDecFunction s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.OctetStringAutomaticTestCaseValues r t o |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (OctetStringValue x)) 
    
    let ret =
        {
            OctetString.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = printValue
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((OctetString ret),newPrms), s7



let private createNullType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.NullType) (us:State) =
    let typeDefinition = DAstTypeDefinition.createNull  r l t o us
    let equalFunction       = DAstEqual.createNullTypeEqualFunction r l  o
    let initialValue        = ()
    let initFunction        = DAstInitialize.createNullTypeInitFunc r l t o typeDefinition (NullValue initialValue)
    let uperEncFunction, s2     = DAstUPer.createNullTypeFunction r l Codec.Encode t o typeDefinition None None us
    let uperDecFunction, s3     = DAstUPer.createNullTypeFunction r l Codec.Decode t o typeDefinition None None s2
    let acnEncFunction, s4      = DAstACN.createNullTypeFunction r l Codec.Encode t o typeDefinition None  s3
    let acnDecFunction, s5      = DAstACN.createNullTypeFunction r l Codec.Decode t o typeDefinition None  s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction None (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction None (Some acnEncFunction) (Some acnEncFunction) s6
    let ret =
        {
            NullType.baseInfo   = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createNullTypeFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
        }
    ((NullType ret),[]), s7



let private createBitString (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.BitString) (us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createBitString  r l t o us0
    let initialValue        =
        System.String('0', o.minSize)
        
    let initFunction        = DAstInitialize.createBitStringInitFunc r l t o typeDefinition (BitStringValue initialValue)
    let equalFunction       = DAstEqual.createBitStringEqualFunction r l t o typeDefinition 
    let printValue          = DAstVariables.createBitStringFunction r l t o typeDefinition 
    let isValidFunction, s1     = DAstValidate.createBitStringFunction r l t o typeDefinition equalFunction printValue us
    let uperEncFunction, s2     = DAstUPer.createBitStringFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBitStringFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createBitStringFunction r deps l Codec.Encode t o typeDefinition isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createBitStringFunction r deps l Codec.Decode t o typeDefinition isValidFunction uperDecFunction s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.BitStringAutomaticTestCaseValues r t o |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (BitStringValue x)) 
    let ret =
        {
            BitString.baseInfo  = o
            typeDefinition      = typeDefinition
            printValue          = printValue
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((BitString ret),newPrms), s7


let private createBoolean (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Boolean) (us:State) =
    let typeDefinition = DAstTypeDefinition.createBoolean  r l t o us
    let equalFunction       = DAstEqual.createBooleanEqualFunction r l t o typeDefinition 
    let initialValue        = false
    let initFunction        = DAstInitialize.createBooleanInitFunc r l t o typeDefinition (BooleanValue initialValue)
    let isValidFunction, s1     = DAstValidate.createBoolFunction r l t o typeDefinition us
    let uperEncFunction, s2     = DAstUPer.createBooleanFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBooleanFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createBooleanFunction r l Codec.Encode t o typeDefinition None isValidFunction  s3
    let acnDecFunction, s5      = DAstACN.createBooleanFunction r l Codec.Decode t o typeDefinition None isValidFunction  s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.BooleanAutomaticTestCaseValues r t o |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (BooleanValue x)) 
    let ret =
        {
            Boolean.baseInfo    = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createBooleanFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((Boolean ret),[]), s7


let private createEnumerated (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Enumerated) (us:State) =
    let typeDefinition = DAstTypeDefinition.createEnumerated  r l t o us
    let equalFunction       = DAstEqual.createEnumeratedEqualFunction r l t o typeDefinition 
    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.definitionValue)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)
    let initialValue  =o.items.Head.Name.Value
    let initFunction        = DAstInitialize.createEnumeratedInitFunc r l t o typeDefinition (EnumValue initialValue)
    let isValidFunction, s1     = DAstValidate.createEnumeratedFunction r l t o typeDefinition us
    let uperEncFunction, s2     = DAstUPer.createEnumeratedFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createEnumeratedFunction r l Codec.Decode t o typeDefinition None isValidFunction s2

    let acnEncFunction, s4      = DAstACN.createEnumeratedFunction r l Codec.Encode t o typeDefinition isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createEnumeratedFunction r l Codec.Decode t o typeDefinition isValidFunction uperDecFunction s4

    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.EnumeratedAutomaticTestCaseValues r t o |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (EnumValue x)) 

    let ret =
        {
            Enumerated.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createEnumeratedFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((Enumerated ret),[]), s7


let private createSequenceOf (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.SequenceOf) (childType:Asn1Type, us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createSequenceOf r l t o childType.typeDefinition us0
    let equalFunction       = DAstEqual.createSequenceOfEqualFunction r l t o typeDefinition childType
    let initialValue =
        [1 .. o.minSize] |> List.map(fun i -> childType.initialValue) |> List.map(fun x -> {Asn1Value.kind=x;id=ReferenceToValue([],[]);loc=emptyLocation}) 
    let initFunction        = DAstInitialize.createSequenceOfInitFunc r l t o typeDefinition childType (SeqOfValue initialValue)
    let isValidFunction, s1     = DAstValidate.createSequenceOfFunction r l t o typeDefinition childType None us
    let uperEncFunction, s2     = DAstUPer.createSequenceOfFunction r l Codec.Encode t o typeDefinition None isValidFunction childType s1
    let uperDecFunction, s3     = DAstUPer.createSequenceOfFunction r l Codec.Decode t o typeDefinition None isValidFunction childType s2
    let acnEncFunction, s4      = DAstACN.createSequenceOfFunction r deps l Codec.Encode t o typeDefinition  isValidFunction childType s3
    let acnDecFunction, s5      = DAstACN.createSequenceOfFunction r deps l Codec.Decode t o typeDefinition  isValidFunction childType s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.SequenceOfAutomaticTestCaseValues r t o childType |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (SeqOfValue x)) 
    let ret =
        {
            SequenceOf.baseInfo = o
            childType           = childType
            printValue          = DAstVariables.createSequenceOfFunction r l t o typeDefinition  childType
            typeDefinition      = typeDefinition
            initialValue        = initialValue 
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((SequenceOf ret),newPrms), s7



let private createAsn1Child (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (ch:Asn1AcnAst.Asn1Child) (newChildType : Asn1Type, us:State) =
    let ret = 
        {
        
            Asn1Child.Name     = ch.Name
            c_name             = ch.c_name
            ada_name           = ch.ada_name
            Type               = newChildType
            Optionality        = ch.Optionality
            Comments           = ch.Comments
            isEqualBodyStats   = DAstEqual.isEqualBodySequenceChild l ch newChildType
            isValidBodyStats    = DAstValidate.isValidSequenceChild l ch newChildType
        }
    Asn1Child ret, us




let private createSequence (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Sequence) (children:SeqChildInfo list, us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createSequence r l t o children us0
    let equalFunction       = DAstEqual.createSequenceEqualFunction r l t o typeDefinition children
    let initialValue =
        children |> 
        List.choose(fun ch -> 
            match ch with
            | Asn1Child o -> Some ({NamedValue.name = o.Name.Value; Value={Asn1Value.kind=o.Type.initialValue;id=ReferenceToValue([],[]);loc=emptyLocation}})
            | AcnChild  _ -> None)
    let initFunction        = DAstInitialize.createSequenceInitFunc r l t o typeDefinition children (SeqValue initialValue)
    let isValidFunction, s1     = DAstValidate.createSequenceFunction r l t o typeDefinition children  us
    let uperEncFunction, s2     = DAstUPer.createSequenceFunction r l Codec.Encode t o typeDefinition None isValidFunction children s1
    let uperDecFunction, s3     = DAstUPer.createSequenceFunction r l Codec.Decode t o typeDefinition None isValidFunction children s2
    let acnEncFunction, s4      = DAstACN.createSequenceFunction r deps l Codec.Encode t o typeDefinition  isValidFunction children newPrms s3
    let acnDecFunction, s5      = DAstACN.createSequenceFunction r deps l Codec.Decode t o typeDefinition  isValidFunction children newPrms s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.SequenceAutomaticTestCaseValues r t o children |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (SeqValue x)) 
    let ret =
        {
            Sequence.baseInfo   = o
            children            = children
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createSequenceFunction r l t o typeDefinition  children
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((Sequence ret),newPrms), s7

let private createChoice (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Choice) (children:ChChildInfo list, us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createChoice r l t o children us0
    let equalFunction       = DAstEqual.createChoiceEqualFunction r l t o typeDefinition children
    let initialValue =
        children |> Seq.map(fun o -> {NamedValue.name = o.Name.Value; Value={Asn1Value.kind=o.chType.initialValue;id=ReferenceToValue([],[]);loc=emptyLocation}}) |> Seq.head
    let initFunction        = DAstInitialize.createChoiceInitFunc r l t o typeDefinition children (ChValue initialValue)
    let isValidFunction, s1     = DAstValidate.createChoiceFunction r l t o typeDefinition children None us
    let uperEncFunction, s2     = DAstUPer.createChoiceFunction r l Codec.Encode t o typeDefinition None isValidFunction children s1
    let uperDecFunction, s3     = DAstUPer.createChoiceFunction r l Codec.Decode t o typeDefinition None isValidFunction children s2
    let acnEncFunction, s4      = DAstACN.createChoiceFunction r deps l Codec.Encode t o typeDefinition  isValidFunction children newPrms  s3
    let acnDecFunction, s5      = DAstACN.createChoiceFunction r deps l Codec.Decode t o typeDefinition  isValidFunction children newPrms  s4
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some acnEncFunction) (Some acnDecFunction) s6
    let automaticTestCasesValues      = EncodeDecodeTestCase.ChoiceAutomaticTestCaseValues r t o children |> List.mapi (fun i x -> createAsn1ValueFromValueKind t i (ChValue x)) 
    let ret =
        {
            Choice.baseInfo     = o
            children            = children
            printValue          = DAstVariables.createChoiceFunction r l t o typeDefinition  children
            typeDefinition      = typeDefinition
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = automaticTestCasesValues
        }
    ((Choice ret),[]), s7

let private createChoiceChild (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (ch:Asn1AcnAst.ChChildInfo) (newChildType : Asn1Type, us:State) =
    let typeDefinitionName = 
        let longName = newChildType.id.AcnAbsPath.Tail |> List.rev |> List.tail |> List.rev |> Seq.StrJoin "_"
        ToC2(r.args.TypePrefix + longName.Replace("#","elem"))
    let ret = 
        {
        
            ChChildInfo.Name     = ch.Name
            c_name             = ch.c_name
            ada_name           = ch.ada_name
            _present_when_name_private  = ch.present_when_name
            acnPresentWhenConditions = ch.acnPresentWhenConditions
            chType              = newChildType
            Comments            = ch.Comments
            isEqualBodyStats    = DAstEqual.isEqualBodyChoiceChild typeDefinitionName l ch newChildType
            isValidBodyStats    = DAstValidate.isValidChoiceChild l ch newChildType
        }
    ret, us

let private createReferenceType (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.ReferenceType) (newBaseType:Asn1Type, us:State) =
    let newPrms, us0 = t.acnParameters |> foldMap(fun ns p -> mapAcnParameter r deps l m t p ns) us
    let typeDefinition = DAstTypeDefinition.createReferenceType r l t o newBaseType us
    let equalFunction       = DAstEqual.createReferenceTypeEqualFunction r l t o newBaseType
    let initialValue        = {Asn1Value.kind=newBaseType.initialValue;id=ReferenceToValue([],[]);loc=emptyLocation}
    let initFunction        = DAstInitialize.createReferenceType r l t o newBaseType
    let isValidFunction, s1     = DAstValidate.createReferenceTypeFunction r l t o typeDefinition newBaseType us
    let uperEncFunction, s2     = DAstUPer.createReferenceFunction r l Codec.Encode t o typeDefinition isValidFunction newBaseType s1
    let uperDecFunction, s3     = DAstUPer.createReferenceFunction r l Codec.Decode t o typeDefinition isValidFunction newBaseType s2
    let acnEncFunction, s4      = DAstACN.createReferenceFunction r l Codec.Encode t o typeDefinition  isValidFunction newBaseType s3
    let acnDecFunction, s5      = DAstACN.createReferenceFunction r l Codec.Decode t o typeDefinition  isValidFunction newBaseType s4
    
    let uperEncDecTestFunc,s6         = EncodeDecodeTestCase.createUperEncDecFunction r l t typeDefinition equalFunction isValidFunction (Some uperEncFunction) (Some uperDecFunction) s5
    let acnEncDecTestFunc ,s7         = EncodeDecodeTestCase.createAcnEncDecFunction r l t typeDefinition equalFunction isValidFunction acnEncFunction acnDecFunction s6

    let ret = 
        {
            ReferenceType.baseInfo = o
            baseType            = newBaseType
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createReferenceTypeFunction r l t o typeDefinition newBaseType
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = equalFunction
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction.Value
            acnDecFunction      = acnDecFunction.Value
            uperEncDecTestFunc  = uperEncDecTestFunc
            acnEncDecTestFunc   = acnEncDecTestFunc
            automaticTestCasesValues = newBaseType.automaticTestCasesValues
        }
    ((ReferenceType ret),newPrms), s7


let private mapType (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type, us:State) =
    Asn1Fold.foldType2
        (fun t ti us -> createInteger r l m t ti us)
        (fun t ti us -> createReal r l m t ti us)
        (fun t ti us -> 
            let (strtype, prms), ns = createStringType r deps l m t ti us
            ((IA5String strtype),prms), ns)
        (fun t ti us -> 
            let (strtype, prms), ns = createStringType r deps l m t ti us
            ((IA5String strtype),prms), ns)
        (fun t ti us -> createOctetString r deps l m t ti us)
        (fun t ti us -> createNullType r l m t ti us)
        (fun t ti us -> createBitString r deps l m t ti us)
        
        (fun t ti us -> createBoolean r l m t ti us)
        (fun t ti us -> createEnumerated r l m t ti us)

        (fun t ti newChild -> createSequenceOf r deps l m t ti newChild)

        (fun t ti newChildren -> createSequence r deps l m t ti newChildren)
        (fun ch newChild -> createAsn1Child r l m ch newChild)
        (fun ch us -> createAcnChild r deps l m ch us)
        

        (fun t ti newChildren -> createChoice r deps l m t ti newChildren)
        (fun ch newChild -> createChoiceChild r l m ch newChild)

        (fun t ti newBaseType -> createReferenceType r deps l m t ti newBaseType)

        (fun t ((newKind, newPrms),us)        -> 
            {
                Asn1Type.Kind = newKind
                id            = t.id
                acnAligment   = t.acnAligment
                acnParameters = newPrms 
                Location      = t.Location
                tasInfo       = t.tasInfo
            }, us)
        t
        us 
        

let private mapTas (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (tas:Asn1AcnAst.TypeAssignment) (us:State)=
    let newType, ns = mapType r deps l m (tas.Type, us)
    {
        TypeAssignment.Name = tas.Name
        c_name = tas.c_name
        ada_name = tas.ada_name
        Type = newType
        Comments = tas.Comments
    },ns


let private mapVas (r:Asn1AcnAst.AstRoot) (allNewTypeAssignments : TypeAssignment list) (deps:Asn1AcnAst.AcnInsertedFieldDependencies)  (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (vas:Asn1AcnAst.ValueAssignment) (us:State)=
    let newType, ns = 
        match vas.Type.Kind with
        | Asn1AcnAst.ReferenceType ref ->
            match allNewTypeAssignments |> Seq.tryFind(fun ts -> ts.Name.Value = ref.tasName.Value && ref.modName.Value = m.Name.Value) with
            | None          -> 
                let oldType = Asn1AcnAstUtilFunctions.GetActualTypeByName r ref.modName ref.tasName
                mapType r deps l m (oldType, us)
            | Some newTas   -> newTas.Type, us
        | _     ->  mapType r deps l m (vas.Type, us)
    {
        ValueAssignment.Name = vas.Name
        c_name = vas.c_name
        ada_name = vas.ada_name
        Type = newType
        Value = mapValue vas.Value
    },ns

let private mapModule (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (us:State) =
    let newTases, ns1 = m.TypeAssignments |> foldMap (fun ns nt -> mapTas r deps l m nt ns) us
    {
        Asn1Module.Name = m.Name
        TypeAssignments = newTases
        ValueAssignments = []
        Imports = m.Imports
        Exports = m.Exports
        Comments = m.Comments
    }, ns1

let private reMapModule (r:Asn1AcnAst.AstRoot) (files0:Asn1File list) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1Module) (us:State) =
    let allNewTasses = files0 |> List.collect(fun f -> f.Modules) |> List.collect(fun m -> m.TypeAssignments)
    let oldModule = r.Files |> List.collect(fun f -> f.Modules) |> List.find(fun oldM -> oldM.Name.Value = m.Name.Value)
    let newVases, ns1 = oldModule.ValueAssignments |> foldMap (fun ns nt -> mapVas r allNewTasses deps l oldModule nt ns) us
    { m with ValueAssignments = newVases}, ns1

let private mapFile (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (f:Asn1AcnAst.Asn1File) (us:State) =
    let newModules, ns = f.Modules |> foldMap (fun cs m -> mapModule r deps l m cs) us
    {
        Asn1File.FileName = f.FileName
        Tokens = f.Tokens
        Modules = newModules
    }, ns

let private reMapFile (r:Asn1AcnAst.AstRoot) (files0:Asn1File list) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (f:Asn1File) (us:State) =
    let newModules, ns = f.Modules |> foldMap (fun cs m -> reMapModule r files0 deps l m cs) us
    {f with Modules = newModules}, ns

let DoWork (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (lang:CommonTypes.ProgrammingLanguage) (encodings: CommonTypes.Asn1Encoding list) : AstRoot=
    let l =
        match lang with
        | CommonTypes.ProgrammingLanguage.C     -> DAst.ProgrammingLanguage.C
        | CommonTypes.ProgrammingLanguage.Ada   
        | CommonTypes.ProgrammingLanguage.Spark -> DAst.ProgrammingLanguage.Ada
        | _                             -> raise(System.Exception "Unsupported programming language")

    
    let initialState = {curSeqOfLevel=0; currErrorCode = 1; curErrCodeNames = Set.empty}
    //first map all type assignments and then value assignments
    let files0, ns = r.Files |> foldMap (fun cs f -> mapFile r deps l f cs) initialState
    let files, ns = files0 |> foldMap (fun cs f -> reMapFile r files0 deps l f cs) ns
    {
        AstRoot.Files = files
        acnConstants = r.acnConstants
        args = r.args
        programUnits = DAstProgramUnit.createProgramUnits files l
        lang = l
    }

