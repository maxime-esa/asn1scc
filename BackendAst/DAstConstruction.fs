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

let private createInteger (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Integer) (us:State) =
    let typeDefinition = DAstTypeDefinition.createInteger  r l t o us
    let initialValue        = getValueByUperRange o.uperRange 0I
    let initFunction        = DAstInitialize.createIntegerInitFunc r l t o typeDefinition (IntegerValue initialValue)
    let isValidFunction, s1     = DAstValidate.createIntegerFunction r l t o typeDefinition None us
    let uperEncFunction, s2     = DAstUPer.createIntegerFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIntegerFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createIntegerFunction r l Codec.Encode t o typeDefinition None isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createIntegerFunction r l Codec.Decode t o typeDefinition None isValidFunction uperDecFunction s4

    let ret =
        {
            Integer.baseInfo    = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createIntegerFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createIntegerEqualFunction r l t o typeDefinition 
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
        }
    Integer ret, s5

let private createReal (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Real) (us:State) =
    let typeDefinition = DAstTypeDefinition.createReal  r l t o us
    let initialValue        = getValueByUperRange o.uperRange 0.0
    let initFunction        = DAstInitialize.createRealInitFunc r l t o typeDefinition (RealValue initialValue)
    let isValidFunction, s1     = DAstValidate.createRealFunction r l t o typeDefinition None us
    let uperEncFunction, s2     = DAstUPer.createRealFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createRealFunction r l Codec.Decode t o typeDefinition None isValidFunction s2

    let ret =
        {
            Real.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createRealFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createRealEqualFunction r l t o typeDefinition 
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    Real ret, s3



let private createStringType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.StringType) (us:State) =
    let typeDefinition = DAstTypeDefinition.createString  r l t o us
    let initialValue        =
        let ch = 
            match o.uperCharSet |> Seq.exists((=) ' ') with
            | true  -> ' '
            | false -> o.uperCharSet |> Seq.find(fun c -> not (Char.IsControl c))
        System.String(ch, o.minSize)
    let initFunction        = DAstInitialize.createIA5StringInitFunc r l t o typeDefinition (StringValue initialValue)
    let isValidFunction, s1     = DAstValidate.createStringFunction r l t o typeDefinition None us
    let uperEncFunction, s2     = DAstUPer.createIA5StringFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIA5StringFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let ret =
        {
            StringType.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createStringFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createStringEqualFunction r l t o typeDefinition 
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    ret, s3


let private createOctetString (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.OctetString) (us:State) =
    let typeDefinition = DAstTypeDefinition.createOctet  r l t o us
    let initialValue        =
        [1 .. o.minSize] |> List.map(fun i -> 0uy)
    let initFunction        = DAstInitialize.createOctetStringInitFunc r l t o typeDefinition (OctetStringValue initialValue)
    let equalFunction       = DAstEqual.createOctetStringEqualFunction r l t o typeDefinition 
    let printValue          = DAstVariables.createOctetStringFunction r l t o typeDefinition 

    let isValidFunction, s1     = DAstValidate.createOctetStringFunction r l t o typeDefinition None equalFunction printValue us
    let uperEncFunction, s2     = DAstUPer.createOctetStringFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createOctetStringFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
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
        }
    OctetString ret, s3



let private createNullType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.NullType) (us:State) =
    let typeDefinition = DAstTypeDefinition.createNull  r l t o us
    let initialValue        = ()
    let initFunction        = DAstInitialize.createNullTypeInitFunc r l t o typeDefinition (NullValue initialValue)
    let uperEncFunction, s2     = DAstUPer.createNullTypeFunction r l Codec.Encode t o typeDefinition None None us
    let uperDecFunction, s3     = DAstUPer.createNullTypeFunction r l Codec.Decode t o typeDefinition None None s2
    let ret =
        {
            NullType.baseInfo   = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createNullTypeFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createNullTypeEqualFunction r l  o
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    NullType ret, s3



let private createBitString (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.BitString) (us:State) =
    let typeDefinition = DAstTypeDefinition.createBitString  r l t o us
    let initialValue        =
        System.String('0', o.minSize)
        
    let initFunction        = DAstInitialize.createBitStringInitFunc r l t o typeDefinition (BitStringValue initialValue)
    let equalFunction       = DAstEqual.createBitStringEqualFunction r l t o typeDefinition 
    let printValue          = DAstVariables.createBitStringFunction r l t o typeDefinition 
    let isValidFunction, s1     = DAstValidate.createBitStringFunction r l t o typeDefinition None equalFunction printValue us
    let uperEncFunction, s2     = DAstUPer.createBitStringFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBitStringFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
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
        }
    BitString ret, s3


let private createBoolean (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Boolean) (us:State) =
    let typeDefinition = DAstTypeDefinition.createBoolean  r l t o us
    let initialValue        = false
    let initFunction        = DAstInitialize.createBooleanInitFunc r l t o typeDefinition (BooleanValue initialValue)
    let isValidFunction, s1     = DAstValidate.createBoolFunction r l t o typeDefinition None us
    let uperEncFunction, s2     = DAstUPer.createBooleanFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBooleanFunction r l Codec.Decode t o typeDefinition None isValidFunction s2
    let acnEncFunction, s4      = DAstACN.createBooleanFunction r l Codec.Encode t o typeDefinition None isValidFunction  s3
    let acnDecFunction, s5      = DAstACN.createBooleanFunction r l Codec.Decode t o typeDefinition None isValidFunction  s4
    let ret =
        {
            Boolean.baseInfo    = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createBooleanFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createBooleanEqualFunction r l t o typeDefinition 
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
        }
    Boolean ret, s3


let private createEnumerated (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Enumerated) (us:State) =
    let typeDefinition = DAstTypeDefinition.createEnumerated  r l t o us

    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.definitionValue)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)
    let initialValue  =o.items.Head.Name.Value
    let initFunction        = DAstInitialize.createEnumeratedInitFunc r l t o typeDefinition (EnumValue initialValue)
    let isValidFunction, s1     = DAstValidate.createEnumeratedFunction r l t o typeDefinition None us
    let uperEncFunction, s2     = DAstUPer.createEnumeratedFunction r l Codec.Encode t o typeDefinition None isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createEnumeratedFunction r l Codec.Decode t o typeDefinition None isValidFunction s2

    let ret =
        {
            Enumerated.baseInfo = o
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createEnumeratedFunction r l t o typeDefinition 
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createEnumeratedEqualFunction r l t o typeDefinition 
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    Enumerated ret, s3


let private createSequenceOf (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.SequenceOf) (childType:Asn1Type, us:State) =
    let typeDefinition = DAstTypeDefinition.createSequenceOf r l t o childType.typeDefinition us
    let initialValue =
        [1 .. o.minSize] |> List.map(fun i -> childType.initialValue) |> List.map(fun x -> {Asn1Value.kind=x;id=ReferenceToValue([],[]);loc=emptyLocation}) 
    let initFunction        = DAstInitialize.createSequenceOfInitFunc r l t o typeDefinition childType (SeqOfValue initialValue)
    let isValidFunction, s1     = DAstValidate.createSequenceOfFunction r l t o typeDefinition childType None us
    let uperEncFunction, s2     = DAstUPer.createSequenceOfFunction r l Codec.Encode t o typeDefinition None isValidFunction childType s1
    let uperDecFunction, s3     = DAstUPer.createSequenceOfFunction r l Codec.Decode t o typeDefinition None isValidFunction childType s2
    let ret =
        {
            SequenceOf.baseInfo = o
            childType           = childType
            printValue          = DAstVariables.createSequenceOfFunction r l t o typeDefinition  childType
            typeDefinition      = typeDefinition
            initialValue        = initialValue 
            initFunction        = initFunction
            equalFunction       = DAstEqual.createSequenceOfEqualFunction r l t o typeDefinition childType
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    SequenceOf ret, s3



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


let private createAcnChild (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (ch:Asn1AcnAst.AcnChild) (us:State) =
    let ret = 
        {
        
            AcnChild.Name  = ch.Name
            id             = ch.id
            Type           = ch.Type
        }
    AcnChild ret, us


let private createSequence (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Sequence) (children:SeqChildInfo list, us:State) =
    let typeDefinition = DAstTypeDefinition.createSequence r l t o children us
    let initialValue =
        children |> 
        List.choose(fun ch -> 
            match ch with
            | Asn1Child o -> Some ({NamedValue.name = o.Name.Value; Value={Asn1Value.kind=o.Type.initialValue;id=ReferenceToValue([],[]);loc=emptyLocation}})
            | AcnChild  _ -> None)
    let initFunction        = DAstInitialize.createSequenceInitFunc r l t o typeDefinition children (SeqValue initialValue)
    let isValidFunction, s1     = DAstValidate.createSequenceFunction r l t o typeDefinition children None us
    let uperEncFunction, s2     = DAstUPer.createSequenceFunction r l Codec.Encode t o typeDefinition None isValidFunction children s1
    let uperDecFunction, s3     = DAstUPer.createSequenceFunction r l Codec.Decode t o typeDefinition None isValidFunction children s2
    let acnEncFunction, s4      = DAstACN.createSequenceFunction r deps l Codec.Encode t o typeDefinition None isValidFunction children s3
    let acnDecFunction, s5      = DAstACN.createSequenceFunction r deps l Codec.Decode t o typeDefinition None isValidFunction children s4
    let ret =
        {
            Sequence.baseInfo   = o
            children            = children
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createSequenceFunction r l t o typeDefinition  children
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createSequenceEqualFunction r l t o typeDefinition children
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
            acnEncFunction      = acnEncFunction
            acnDecFunction      = acnDecFunction
        }
    Sequence ret, s5

let private createChoice (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Choice) (children:ChChildInfo list, us:State) =
    let typeDefinition = DAstTypeDefinition.createChoice r l t o children us
    let initialValue =
        children |> Seq.map(fun o -> {NamedValue.name = o.Name.Value; Value={Asn1Value.kind=o.chType.initialValue;id=ReferenceToValue([],[]);loc=emptyLocation}}) |> Seq.head
    let initFunction        = DAstInitialize.createChoiceInitFunc r l t o typeDefinition children (ChValue initialValue)
    let isValidFunction, s1     = DAstValidate.createChoiceFunction r l t o typeDefinition children None us
    let uperEncFunction, s2     = DAstUPer.createChoiceFunction r l Codec.Encode t o typeDefinition None isValidFunction children s1
    let uperDecFunction, s3     = DAstUPer.createChoiceFunction r l Codec.Decode t o typeDefinition None isValidFunction children s2
    let ret =
        {
            Choice.baseInfo     = o
            children            = children
            printValue          = DAstVariables.createChoiceFunction r l t o typeDefinition  children
            typeDefinition      = typeDefinition
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createChoiceEqualFunction r l t o typeDefinition children
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    Choice ret, s3

let private createChoiceChild (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (ch:Asn1AcnAst.ChChildInfo) (newChildType : Asn1Type, us:State) =
    let typeDefinitionName = 
        let longName = newChildType.id.AcnAbsPath.Tail |> List.rev |> List.tail |> List.rev |> Seq.StrJoin "_"
        ToC2(r.args.TypePrefix + longName.Replace("#","elem"))
    let ret = 
        {
        
            ChChildInfo.Name     = ch.Name
            c_name             = ch.c_name
            ada_name           = ch.ada_name
            present_when_name  = ch.present_when_name
            acnPresentWhenConditions = ch.acnPresentWhenConditions
            chType              = newChildType
            Comments            = ch.Comments
            isEqualBodyStats    = DAstEqual.isEqualBodyChoiceChild typeDefinitionName l ch newChildType
            isValidBodyStats    = DAstValidate.isValidChoiceChild l ch newChildType
        }
    ret, us

let private createReferenceType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.ReferenceType) (newBaseType:Asn1Type, us:State) =
    let typeDefinition = DAstTypeDefinition.createReferenceType r l t o newBaseType us
    let initialValue        = {Asn1Value.kind=newBaseType.initialValue;id=ReferenceToValue([],[]);loc=emptyLocation}
    let initFunction        = DAstInitialize.createReferenceType r l t o newBaseType
    let isValidFunction, s1     = DAstValidate.createReferenceTypeFunction r l t o typeDefinition newBaseType us
    let uperEncFunction, s2     = DAstUPer.createReferenceFunction r l Codec.Encode t o typeDefinition isValidFunction newBaseType s1
    let uperDecFunction, s3     = DAstUPer.createReferenceFunction r l Codec.Decode t o typeDefinition isValidFunction newBaseType s2

    let ret = 
        {
            ReferenceType.baseInfo = o
            baseType            = newBaseType
            typeDefinition      = typeDefinition
            printValue          = DAstVariables.createReferenceTypeFunction r l t o typeDefinition newBaseType
            initialValue        = initialValue
            initFunction        = initFunction
            equalFunction       = DAstEqual.createReferenceTypeEqualFunction r l t o newBaseType
            isValidFunction     = isValidFunction
            uperEncFunction     = uperEncFunction
            uperDecFunction     = uperDecFunction 
        }
    ReferenceType ret, s3

let private mapType (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (t:Asn1AcnAst.Asn1Type, us:State) =
    Asn1Fold.foldType2
        (fun t ti us -> createInteger r l m t ti us)
        (fun t ti us -> createReal r l m t ti us)
        (fun t ti us -> 
            let strtype, ns = createStringType r l m t ti us
            IA5String strtype, ns)
        (fun t ti us -> 
            let strtype, ns = createStringType r l m t ti us
            IA5String strtype, ns)
        (fun t ti us -> createOctetString r l m t ti us)
        (fun t ti us -> createNullType r l m t ti us)
        (fun t ti us -> createBitString r l m t ti us)
        
        (fun t ti us -> createBoolean r l m t ti us)
        (fun t ti us -> createEnumerated r l m t ti us)

        (fun t ti newChild -> createSequenceOf r l m t ti newChild)

        (fun t ti newChildren -> createSequence r deps l m t ti newChildren)
        (fun ch newChild -> createAsn1Child r l m ch newChild)
        (fun ch us -> createAcnChild r l m ch us)
        

        (fun t ti newChildren -> createChoice r l m t ti newChildren)
        (fun ch newChild -> createChoiceChild r l m ch newChild)

        (fun t ti newBaseType -> createReferenceType r l m t ti newBaseType)

        (fun t (newKind,us)        -> 
            {
                Asn1Type.Kind = newKind
                id            = t.id
                acnAligment   = t.acnAligment
                acnParameters = t.acnParameters
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


let private mapVas (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies)  (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (vas:Asn1AcnAst.ValueAssignment) (us:State)=
    let newType, ns = mapType r deps l m (vas.Type, us)
    {
        ValueAssignment.Name = vas.Name
        c_name = vas.c_name
        ada_name = vas.ada_name
        Type = newType
        Value = mapValue vas.Value
    },ns

let private mapModule (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (us:State) =
    let newTases, ns1 = m.TypeAssignments |> foldMap (fun ns nt -> mapTas r deps l m nt ns) us
    let newVases, ns2 = m.ValueAssignments |> foldMap (fun ns nt -> mapVas r deps l m nt ns) ns1
    {
        Asn1Module.Name = m.Name
        TypeAssignments = newTases
        ValueAssignments = newVases
        Imports = m.Imports
        Exports = m.Exports
        Comments = m.Comments
    }, ns2

let private mapFile (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (f:Asn1AcnAst.Asn1File) (us:State) =
    let newModules, ns = f.Modules |> foldMap (fun cs m -> mapModule r deps l m cs) us
    {
        Asn1File.FileName = f.FileName
        Tokens = f.Tokens
        Modules = newModules
    }, ns

let DoWork (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (lang:CommonTypes.ProgrammingLanguage) : AstRoot=

    let l =
        match lang with
        | CommonTypes.ProgrammingLanguage.C     -> DAst.ProgrammingLanguage.C
        | CommonTypes.ProgrammingLanguage.Ada   
        | CommonTypes.ProgrammingLanguage.Spark -> DAst.ProgrammingLanguage.Ada
        | _                             -> raise(System.Exception "Unsupported programming language")

    
    let initialState = {State.currentTypes = []; curSeqOfLevel=0; currErrCode = 1}

    let files, ns = r.Files |> foldMap (fun cs f -> mapFile r deps l f cs) initialState
    {
        AstRoot.Files = files
        acnConstants = r.acnConstants
        args = r.args
        programUnits = DAstProgramUnit.createProgramUnits files l
        lang = l
    }

(*

let getValueByUperRange (r:uperRange<'T>) (z:'T) = 
    match r with
    | Concrete (a,b)    -> if a <= z && z <= b then z else a
    | NegInf  b         -> if z <= b then z else b              //(-inf, b]
    | PosInf a          -> if a <= z then z else a               //[a, +inf)
    | Full              -> z


let createInteger (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer)  (newBase:Integer option) (us:State) =
    let baseTypeEq          = DAstBaseTypesEquivalence.getInteger o newBase
    let typeDefinition      = createIntegerTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        let v = getValueByUperRange o.uperRange 0I
        {IntegerValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = v; }
    let initFunction            = DAstInitialize.createIntegerInitFunc r l o typeDefinition (IntegerValue initialValue)
    let baseTypeEqFunc          = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc         = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createIntegerFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createIntegerFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIntegerFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
    let baseTypeEncAcnFunc      = baseTypeEq.acn |> Option.map(fun x -> x.acnEncFunction)
    let baseTypeDecAcnFunc      = baseTypeEq.acn |> Option.map(fun x -> x.acnDecFunction)
    let acnEncFunction, s4      = DAstACN.createIntegerFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncAcnFunc isValidFunction uperEncFunction s3
    let acnDecFunction, s5      = DAstACN.createIntegerFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecAcnFunc isValidFunction uperDecFunction s4


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
                initialValue        = initialValue
                initFunction        = initFunction
                equalFunction       = DAstEqual.createIntegerEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                acnEncFunction      = acnEncFunction
                acnDecFunction      = acnDecFunction
                baseTypeEquivalence = baseTypeEq

            }
    ret, s5

let createReal (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real)  (newBase:Real option) (us:State) : (Real*State) =
    let baseTypeEq          = DAstBaseTypesEquivalence.getReal o newBase
    let typeDefinition      = createRealTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        let v = getValueByUperRange o.uperRange 0.0
        {RealValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = v; }    
    let initFunction        = DAstInitialize.createRealInitFunc r l o typeDefinition (RealValue initialValue)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let isValidFunction, s1     = DAstValidate.createRealFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createRealFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createRealFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2

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
                initialValue        = initialValue
                initFunction        = initFunction
                baseTypeEquivalence = baseTypeEq
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
    let baseTypeEq = DAstBaseTypesEquivalence.getIA5String o newBase
    let typeDefinition      = createStringTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        let ch = 
            match o.charSet |> Seq.exists((=) ' ') with
            | true  -> ' '
            | false -> o.charSet |> Seq.find(fun c -> not (Char.IsControl c))
        let v = System.String(ch, o.minSize)
        {StringValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = v; }
    let initFunction        = DAstInitialize.createIA5StringInitFunc r l o typeDefinition (StringValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createStringFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createIA5StringFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createIA5StringFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
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
                baseTypeEquivalence = baseTypeEq
                acnEncodingClass    = o.acnEncodingClass
                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
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
    let baseTypeEq = DAstBaseTypesEquivalence.getOctetString o newBase
    let typeDefinition          = createOctetTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        let v = [1 .. o.minSize] |> List.map(fun i -> 0uy)
        {OctetStringValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = v; }
    let initFunction        = DAstInitialize.createOctetStringInitFunc r l o typeDefinition (OctetStringValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let equalFunction       = DAstEqual.createOctetStringEqualFunction r l o typeDefinition baseTypeEqFunc
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createOctetStringFunction r l o typeDefinition baseTypeValFunc equalFunction us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createOctetStringFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createOctetStringFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
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
                baseTypeEquivalence = baseTypeEq
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
                equalFunction       = equalFunction
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, s3

let createBitString (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString)  (newBase:BitString option) (us:State) : (BitString*State) =
    let baseTypeEq = DAstBaseTypesEquivalence.getBitString o newBase
    let typeDefinition      = createBitStringTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        let v = System.String('0', o.minSize)
        {BitStringValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = v; }
    let initFunction        = DAstInitialize.createBitStringInitFunc r l o typeDefinition (BitStringValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let equalFunction = DAstEqual.createBitStringEqualFunction r l o typeDefinition baseTypeEqFunc
    let isValidFunction, s1     = DAstValidate.createBitStringFunction r l o typeDefinition baseTypeValFunc equalFunction us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createBitStringFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBitStringFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
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
                baseTypeEquivalence = baseTypeEq
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
                equalFunction       = DAstEqual.createBitStringEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x
            }
    ret, s3

let createNullType (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.NullType)  (newBase:NullType option) (us:State) : (NullType*State) =
    let baseTypeEq          = DAstBaseTypesEquivalence.getNullType o newBase
    let typeDefinition      = createNullTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        {NullValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = (); }
    let initFunction        = DAstInitialize.createNullTypeInitFunc r l o typeDefinition (NullValue initialValue)
    let baseTypeEqFunc          = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s1     = DAstUPer.createNullTypeFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc None us
    let uperDecFunction, s2     = DAstUPer.createNullTypeFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc None s1
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
                baseTypeEquivalence = baseTypeEq
                acnEncodingClass    = o.acnEncodingClass
                typeDefinition      = typeDefinition 
                initialValue        = initialValue
                initFunction        = initFunction
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
    let baseTypeEq          = DAstBaseTypesEquivalence.getBoolean o newBase
    let typeDefinition      = createBooleanTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue        =
        {BooleanValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = false; }
    let initFunction        = DAstInitialize.createBooleanInitFunc r l o typeDefinition (BooleanValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createBoolFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createBooleanFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createBooleanFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2
    let baseTypeEncAcnFunc      = baseTypeEq.acn |> Option.map(fun x -> x.acnEncFunction)
    let baseTypeDecAcnFunc      = baseTypeEq.acn |> Option.map(fun x -> x.acnDecFunction)
    let acnEncFunction, s4      = DAstACN.createBooleanFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncAcnFunc isValidFunction s3
    let acnDecFunction, s5      = DAstACN.createBooleanFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecAcnFunc isValidFunction s4
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
                baseTypeEquivalence = baseTypeEq
                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
                equalFunction       = DAstEqual.createBooleanEqualFunction r l o typeDefinition baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                acnEncFunction      = acnEncFunction
                acnDecFunction      = acnDecFunction
            }
    ret, s5

let createEnumerated (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated)  (newBase:Enumerated option) (us:State) : (Enumerated*State) =
    let baseTypeEq          = DAstBaseTypesEquivalence.getEnumerated o newBase
    let items = 
        match o.userDefinedValues with
        | true  -> o.items |> List.map( fun i -> header_c.PrintNamedItem (i.getBackendName l) i.Value)
        | false ->o.items |> List.map( fun i -> i.getBackendName l)
    let typeDefinition      = createEnumeratedTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) us
    let initialValue =
        {EnumValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = o.items.Head.name; }
    let initFunction        = DAstInitialize.createEnumeratedInitFunc r l o typeDefinition (EnumValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createEnumeratedFunction r l o typeDefinition baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createEnumeratedFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction s1
    let uperDecFunction, s3     = DAstUPer.createEnumeratedFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction s2

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
                baseTypeEquivalence = baseTypeEq
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                enumEncodingClass    = o.enumEncodingClass
                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
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
    let baseTypeEq = DAstBaseTypesEquivalence.getSequenceOf o newBase
    let typeDefinition      = createSequenceOfTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) childType.typeDefinition us
    let initialValue =
        let v = [1 .. o.minSize] |> List.map(fun i -> childType.initialValue)
        {SeqOfValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = v; }
    let initFunction        = DAstInitialize.createSequenceOfInitFunc r l o typeDefinition childType (SeqOfValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createSequenceOfFunction r l o typeDefinition childType baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createSequenceOfFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction childType s1
    let uperDecFunction, s3     = DAstUPer.createSequenceOfFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction childType s2
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
                baseTypeEquivalence = baseTypeEq
                Location            = o.Location  
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                acnEncodingClass    = o.acnEncodingClass
                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
                equalFunction       = DAstEqual.createSequenceOfEqualFunction r l o typeDefinition childType baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                childType           = childType
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s3


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
    let baseTypeEq = DAstBaseTypesEquivalence.getSequence o newBase
    let typeDefinition          = createSequenceTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) children us
    let initialValue =
        let childValues = children |> List.map(fun o -> {NamedValue.name = o.name; Value=o.chType.initialValue})
        {SeqValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = childValues }
    let initFunction        = DAstInitialize.createSequenceInitFunc r l o typeDefinition children (SeqValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createSequenceFunction r l o typeDefinition children baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createSequenceFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction children s1
    let uperDecFunction, s3     = DAstUPer.createSequenceFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction children s2
    let baseTypeEncAcnFunc      = baseTypeEq.acn |> Option.map(fun x -> x.acnEncFunction)
    let baseTypeDecAcnFunc      = baseTypeEq.acn |> Option.map(fun x -> x.acnDecFunction)
    let acnEncFunction, s4      = DAstACN.createSequenceFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncAcnFunc isValidFunction children  s3
    let acnDecFunction, s5      = DAstACN.createSequenceFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecAcnFunc isValidFunction children  s4

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
                baseTypeEquivalence = baseTypeEq
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                alignment           = o.alignment
                initialValue        = initialValue
                initFunction        = initFunction
                typeDefinition      = createSequenceTypeDefinition r l o  (newBase |> Option.map(fun x -> x.typeDefinition)) children us
                equalFunction       = DAstEqual.createSequenceEqualFunction r l o typeDefinition children baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                acnEncFunction      = acnEncFunction
                acnDecFunction      = acnDecFunction

            }
    ret, s5


let createChoiceChild (r:CAst.AstRoot) (l:ProgrammingLanguage)  (o:CAst.ChChildInfo)  (newChild:Asn1Type) (us:State) : (ChChildInfo*State) =
    let typeDefinitionName = 
        let longName = newChild.id.AcnAbsPath.Tail |> List.rev |> List.tail |> List.rev |> Seq.StrJoin "_"
        ToC2(r.args.TypePrefix + longName.Replace("#","elem"))

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
    let baseTypeEq = DAstBaseTypesEquivalence.getChoice o newBase
    let typeDefinition = createChoiceTypeDefinition r l o  (baseTypeEq.typeDefinition |> Option.map(fun x -> x.typeDefinition)) children us
    let initialValue =
        let firstChildVal =  children |> Seq.map(fun o -> {NamedValue.name = o.name; Value=o.chType.initialValue}) |> Seq.head
        {ChValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = o.tasInfo.IsNone; refToType = o.id; Value = firstChildVal}
    let initFunction        = DAstInitialize.createChoiceInitFunc r l o typeDefinition children (ChValue initialValue)
    let baseTypeEqFunc  = baseTypeEq.typeDefinition |> Option.map(fun x -> x.equalFunction)
    let baseTypeValFunc = match baseTypeEq.typeDefinition with None -> None | Some x -> x.isValidFunction
    let isValidFunction, s1     = DAstValidate.createChoiceFunction r l o typeDefinition children baseTypeValFunc us
    let baseTypeEncUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperEncFunction)
    let baseTypeDecUperFunc     = baseTypeEq.uper |> Option.map(fun x -> x.uperDecFunction)
    let uperEncFunction, s2     = DAstUPer.createChoiceFunction r l CommonTypes.Codec.Encode o typeDefinition baseTypeEncUperFunc isValidFunction children s1
    let uperDecFunction, s3     = DAstUPer.createChoiceFunction r l CommonTypes.Codec.Decode o typeDefinition baseTypeDecUperFunc isValidFunction children s2
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
                baseTypeEquivalence = baseTypeEq
                choiceIDForNone     = o.choiceIDForNone
                acnMaxSizeInBits    = o.acnMaxSizeInBits
                acnMinSizeInBits    = o.acnMinSizeInBits
                acnEncodingClass    = o.acnEncodingClass
                alignment           = o.alignment

                typeDefinition      = typeDefinition
                initialValue        = initialValue
                initFunction        = initFunction
                equalFunction       = DAstEqual.createChoiceEqualFunction r l o typeDefinition children baseTypeEqFunc
                isValidFunction     = isValidFunction
                uperEncFunction     = uperEncFunction
                uperDecFunction     = uperDecFunction
                encodeFuncName      = None
                encodeFuncBody      = fun x -> x
                decodeFuncName      = None
                decodeFuncBody      = fun x -> x

            }
    ret, s3


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


let foldMap = GenericFold2.foldMap

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
        args = r.args
        valsMap  = r.valsMap
        typesMap = newTypesMap
        TypeAssignments = newTypeAssignments
        ValueAssignments = r.ValueAssignments
        acnParameters = r.acnParameters
        acnConstants = r.acnConstants
        acnLinks = r.acnLinks
        programUnits= programUnits
    }



*)