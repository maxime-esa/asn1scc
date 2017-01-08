module CAstConstruction

open CAst




let mapBTypeToCType (t:BAst.Asn1Type) (acn:AcnTypes.AcnAst) initialSate=
    BAstFold.foldAsn1Type
        t
        initialSate
        (fun o newBase us -> {Integer.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; uperRange=o.uperRange; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = Acn.Integer_uPER}, us)
        Integer
        (fun o newBase us -> {Real.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; uperRange=o.uperRange; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = Acn.Real_uPER}, us)
        Real
        (fun o newBase us -> {StringType.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; charSet = o.charSet; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = Acn_Enc_String_CharIndex_Internal_Field_Determinant;ancParameters=[];acnArguments=[]}, us)
        IA5String
        (fun o newBase us -> {OctetString.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = AutoSize;ancParameters=[];acnArguments=[]}, us)
        OctetString
        (fun o newBase us -> {NullType.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = {NullAcnEncodingClass.encodePattern=[];patternSizeInBits=0}}, us)
        NullType
        (fun o newBase us -> {BitString.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = AutoSize;ancParameters=[];acnArguments=[]}, us)
        BitString
        (fun o newBase us -> {Boolean.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = {BolleanAcnEncodingClass.encodingValueIsTrue=true; patternSizeInBits=1; truePattern=[]; falsePattern=[]}}, us)
        Boolean
        (fun o newBase us -> {Enumerated.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; userDefinedValues = o.userDefinedValues; items = o.items; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; enumEncodingClass = (EncodeIndexes Acn.Integer_uPER)}, us)
        Enumerated
        (fun childType o newBase us -> {SequenceOf.id = o.id; childType = childType; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = AutoSize;ancParameters=[];acnArguments=[]}, us)
        SequenceOf

        //sequence
        (fun o newChild us -> {SeqChildInfo.name = o.Name; chType = newChild; optionality = None; acnInsertetField = false; comments = o.Comments}, us)
        (fun children o newBase us -> {Sequence.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; children = children; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; ancParameters=[];acnArguments=[]}, us)
        Sequence

        //Choice
        (fun o newChild us -> {ChChildInfo.name = o.Name; chType = newChild; comments = o.Comments; presentConditions = []}, us)
        (fun children o newBase us -> {Choice.id = o.id; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; children = children; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; ancParameters=[];acnArguments=[];acnEncodingClass = EmbededChoiceIndexLikeUper}, us)
        Choice
    

type State = {
    currentTypes : Asn1Type list
}

let foldMap = CloneTree.foldMap

let mapBAstToCast (r:BAst.AstRoot) (acn:AcnTypes.AcnAst) : AstRoot=
    let initialState = {State.currentTypes = []}
    let newTypes,_ = 
        r.TypeAssignments |>
        foldMap (fun cs t ->
            let newType, newState = mapBTypeToCType t acn cs
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
    }

