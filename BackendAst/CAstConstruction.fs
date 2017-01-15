module CAstConstruction

open CAst
open FsUtils
open Constraints


type State = {
    currentTypes : Asn1Type list
}

let mapBTypeToCType (r:BAst.AstRoot) (t:BAst.Asn1Type) (acn:AcnTypes.AcnAst) (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) (initialSate:State) =
   
    let createAnyParams (ts:BAst.TypeAssignmentInfo) =
        acn.Parameters |> 
        List.filter(fun p -> p.ModName = ts.modName && p.TasName = ts.tasName) |>
        List.map(fun p -> 
            match p.Asn1Type with
            | AcnTypes.Integer      -> IntParameter {IntParameter.name = p.Name; prmType = AcnInteger}
            | AcnTypes.Boolean      -> BoolParameter {BooleanParameter.name = p.Name; prmType = AcnBoolean}
            | AcnTypes.NullType     -> raise(SemanticError(p.Location, "Invalid parameter type. Expecting INTEGER or BOOLEAN"))
            | AcnTypes.RefTypeCon (md,ts)   ->
                let asn1TypeName = {Asn1TypeName.moduName = md.Value; tasName = ts.Value}
                match r.typesMap.TryFind asn1TypeName.id with 
                | Some t -> 
                    match t with
                    | BAst.Integer       o -> IntParameter {IntParameter.name = p.Name; prmType = Asn1Integer asn1TypeName}
                    | BAst.IA5String     o -> StringParameter {StringParameter.name = p.Name; prmType = Asn1String asn1TypeName}
                    | BAst.Boolean       o -> BoolParameter {BooleanParameter.name = p.Name; prmType = Asn1Boolean asn1TypeName}
                    | BAst.Enumerated    o -> EnumeratedParameter {EnumeratedParameter.name = p.Name; prmType = Asn1Enumerated asn1TypeName}
                    | _          -> raise(SemanticError(p.Location, "Invalid parameter type. Expecting INTEGER or reference to INTEGER"))
                | None   -> raise(SemanticError(p.Location, sprintf "Unknown reference '%s'.'%s'" md.Value ts.Value)))
                

    let createIntParams (ts:BAst.TypeAssignmentInfo) =
        acn.Parameters |> 
        List.filter(fun p -> p.ModName = ts.modName && p.TasName = ts.tasName) |>
        List.map(fun p -> 
            match p.Asn1Type with
            | AcnTypes.Integer      -> {IntParameter.name = p.Name; prmType = AcnInteger}
            | AcnTypes.Boolean      
            | AcnTypes.NullType     -> raise(SemanticError(p.Location, "Invalid parameter type. Expecting INTEGER or reference to INTEGER"))
            | AcnTypes.RefTypeCon (md,ts)   ->
                let asn1TypeName = {Asn1TypeName.moduName = md.Value; tasName = ts.Value}
                match r.typesMap.TryFind asn1TypeName.id with 
                | Some t -> 
                    match t with
                    | BAst.Integer  o -> {IntParameter.name = p.Name; prmType = Asn1Integer asn1TypeName}
                    | _          -> raise(SemanticError(p.Location, "Invalid parameter type. Expecting INTEGER or reference to INTEGER"))
                | None   -> raise(SemanticError(p.Location, sprintf "Unknown reference '%s'.'%s'" md.Value ts.Value)))
                
    
    BAstFold.foldAsn1Type
        t
        initialSate

        (fun o newBase us -> 
            let encClass, acnMinSizeInBits, acnMaxSizeInBits = CAstAcnEncodingClasses.GetIntEncodingClass acn acnTypes o.Location o
            {Integer.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; uperRange=o.uperRange; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass}, us)
        Integer

        (fun o newBase us -> 
            let encClass, acnMinSizeInBits, acnMaxSizeInBits = CAstAcnEncodingClasses.GetRealEncodingClass acn acnTypes o.Location o
            {Real.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; uperRange=o.uperRange; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass}, us)
        Real

        (fun o newBase us -> 
            let tasInfo = o.tasInfo |> Option.map (fun ts -> 
                let acnParams = createIntParams ts 
                {AcnTypeAssignmentInfo.modName=ts.modName; tasName = ts.tasName; ancParameters = acnParams})
            let encClass, acnMinSizeInBits, acnMaxSizeInBits = CAstAcnEncodingClasses.GetStringEncodingClass acn acnTypes o.Location o tasInfo
            {StringType.id = o.id; tasInfo = tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; charSet = o.charSet; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass;acnArguments=[]}, us)
        IA5String

        (fun o newBase us -> 
            let tasInfo = o.tasInfo |> Option.map (fun ts -> 
                let acnParams = createIntParams ts 
                {AcnTypeAssignmentInfo.modName=ts.modName; tasName = ts.tasName; ancParameters = acnParams})
            {OctetString.id = o.id; tasInfo = tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = AutoSize; acnArguments=[]}, us)
        OctetString

        (fun o newBase us -> {NullType.id = o.id;  tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = {NullAcnEncodingClass.encodePattern=[];patternSizeInBits=0}}, us)
        NullType

        (fun o newBase us -> 
            let tasInfo = o.tasInfo |> Option.map (fun ts -> 
                let acnParams = createIntParams ts 
                {AcnTypeAssignmentInfo.modName=ts.modName; tasName = ts.tasName; ancParameters = acnParams})
            {BitString.id = o.id; tasInfo = tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = AutoSize;acnArguments=[]}, us)
        BitString

        (fun o newBase us -> {Boolean.id = o.id;  tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = {BolleanAcnEncodingClass.encodingValueIsTrue=true; patternSizeInBits=1; truePattern=[]; falsePattern=[]}}, us)
        Boolean

        (fun o newBase us -> {Enumerated.id = o.id;  tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; userDefinedValues = o.userDefinedValues; items = o.items; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; enumEncodingClass = (EncodeIndexes Acn.Integer_uPER)}, us)
        Enumerated

        (fun childType o newBase us -> 
            let tasInfo = o.tasInfo |> Option.map (fun ts -> 
                let acnParams = createAnyParams ts 
                {AcnTypeAssignmentInfo.modName=ts.modName; tasName = ts.tasName; ancParameters = acnParams})
            {SequenceOf.id = o.id; tasInfo = tasInfo; childType = childType; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = AutoSize;acnArguments=[]}, us)
        SequenceOf

        //sequence
        (fun o newChild us -> {SeqChildInfo.name = o.Name; chType = newChild; optionality = None; acnInsertetField = false; comments = o.Comments}, us)
        (fun children o newBase us -> 
            let tasInfo = o.tasInfo |> Option.map (fun ts -> 
                let acnParams = createAnyParams ts 
                {AcnTypeAssignmentInfo.modName=ts.modName; tasName = ts.tasName; ancParameters = acnParams})
            {Sequence.id = o.id; tasInfo = tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; children = children; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnArguments=[]}, us)
        Sequence

        //Choice
        (fun o newChild us -> {ChChildInfo.name = o.Name; chType = newChild; comments = o.Comments; presentConditions = []}, us)
        (fun children o newBase us -> 
            let tasInfo = o.tasInfo |> Option.map (fun ts -> 
                let acnParams = createAnyParams ts 
                {AcnTypeAssignmentInfo.modName=ts.modName; tasName = ts.tasName; ancParameters = acnParams})
            {Choice.id = o.id; tasInfo = tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; children = children; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnArguments=[];acnEncodingClass = EmbededChoiceIndexLikeUper}, us)
        Choice
    


let foldMap = CloneTree.foldMap

let mapBAstToCast (r:BAst.AstRoot) (acn:AcnTypes.AcnAst) : AstRoot=
    let initialState = {State.currentTypes = []}
    let acnTypes = acn.Types |> List.map(fun t -> t.TypeID, t) |> Map.ofList
    let newTypes,_ = 
        r.TypeAssignments |>
        foldMap (fun cs t ->
            let newType, newState = mapBTypeToCType r t acn acnTypes cs
            newType, {newState with currentTypes = newState.currentTypes@[newType]}
        ) initialState  
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
        typesMap = newTypes |> List.map(fun t -> t.id, t) |> Map.ofList
        TypeAssignments = newTypes
        ValueAssignments = r.ValueAssignments
        integerSizeInBytes = r.integerSizeInBytes
        acnParameters = r.acnParameters
        acnConstants = r.acnConstants
    }

