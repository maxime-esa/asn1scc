module CAstConstruction

open CAst
open FsUtils
open Constraints
open CAstAcnEncodingClasses


let mapBTypeToCType (r:BAst.AstRoot) (t:BAst.Asn1Type) (acn:AcnTypes.AcnAst) (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) (acnParameters: AcnParameter list) (initialSate:State) =
   
    let getAcnParams (tid:ReferenceToType) =
        tid.BelongingTypeAssignment |> Option.map(fun ts -> acnParameters |> List.filter(fun x -> x.ModName = ts.moduName && x.TasName = ts.tasName)) |> Option.toList |> List.collect id
                
    
    BAstFold.foldAsn1Type
        t
        initialSate

        (fun o newBase us -> 
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetIntEncodingClass acn acnTypes o.Location o
            {Integer.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; uperRange=o.uperRange; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass; alignment = alignment}, us)
        Integer

        (fun o newBase us -> 
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetRealEncodingClass acn acnTypes o.Location o
            {Real.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; uperRange=o.uperRange; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass; alignment= alignment}, us)
        Real

        (fun o newBase us -> 
            let acnParams = getAcnParams o.id
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits, nus = GetStringEncodingClass acn acnTypes o.Location o acnParams us
            {StringType.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; charSet = o.charSet; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass; alignment=alignment}, nus)
        IA5String

        (fun o newBase us -> 
            let acnParams = getAcnParams o.id
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits, nus = GetOctetStringEncodingClass acn acnTypes o.Location o acnParams us
            {OctetString.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = encClass; alignment=alignment}, nus)
        OctetString

        (fun o newBase us -> 
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetNullTypeEncodingClass acn acnTypes o.Location o
            {NullType.id = o.id;  tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = encClass; alignment = alignment}, us)
        NullType

        (fun o newBase us -> 
            let acnParams = getAcnParams o.id
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits, nus = GetBitStringEncodingClass acn acnTypes o.Location o acnParams us
            {BitString.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = encClass; alignment = alignment}, nus)
        BitString

        (fun o newBase us -> 
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetBooleanTypeEncodingClass acn acnTypes o.Location o
            {Boolean.id = o.id;  tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = encClass; alignment = alignment}, us)
        Boolean

        (fun o newBase us -> 
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetEnumeratedEncodingClass acn acnTypes o.Location o
            {Enumerated.id = o.id;  tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; userDefinedValues = o.userDefinedValues; items = o.items; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; enumEncodingClass = encClass; alignment = alignment}, us)
        Enumerated

        (fun childType o newBase us -> 
            let acnParams = getAcnParams o.id
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits, nus = GetSequenceOfEncodingClass acn acnTypes o.Location  o childType.acnMinSizeInBits childType.acnMaxSizeInBits acnParams us
            {SequenceOf.id = o.id; tasInfo = o.tasInfo; childType = childType; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; cons=o.cons; withcons = o.withcons; minSize = o.minSize; maxSize = o.maxSize; baseType = newBase; Location = o.Location; acnMaxSizeInBits = 0; acnMinSizeInBits = 0; acnEncodingClass = encClass; alignment = alignment}, nus)
        SequenceOf

        //sequence
        (fun o newChild us -> 
            let acnParams = getAcnParams newChild.id
            let newOptionality, nus = GetSeqChildOptionality acn  acnTypes o.Location newChild o.Optionality (acnParams: AcnParameter list) (us:State)
            {SeqChildInfo.name = o.Name; chType = newChild; optionality = newOptionality; acnInsertetField = o.acnInsertetField; comments = o.Comments}, nus)
        (fun children o newBase us -> 
            let acnProps = getAcnProps acnTypes o.id
            let alignment, alignmentSize = GetAlignment acnProps
            let bitMaskSize = seqAcnOptionalChildrenHandledLikeuPER children |> Seq.length
            let reqChildren = children |> List.filter(fun c -> match c.optionality with Some (Optional _) -> false | _ -> true)
            let acnMaxSizeInBits = alignmentSize + bitMaskSize + (children |> List.map(fun c -> c.chType.acnMaxSizeInBits) |> List.sum)
            let acnMinSizeInBits = alignmentSize + bitMaskSize + (reqChildren |> List.map(fun c -> c.chType.acnMinSizeInBits) |> List.sum)
            {Sequence.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; children = children; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = 0; alignment=alignment}, us)
        Sequence

        //Choice
        (fun o newChild us -> 
            let acnParams = getAcnParams newChild.id
            let presenseIsHandleByExtField, nus = getChildLinks acn  acnTypes o.Location newChild  acnParams us
            {ChChildInfo.name = o.Name; chType = newChild; comments = o.Comments; presenseIsHandleByExtField=presenseIsHandleByExtField; presentWhenName = (ToC o.Name) + "_PRESENT"}, nus)
        (fun children o newBase us -> 
            let acnParams = getAcnParams o.id
            let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits, nus = GetChoiceEncodingClass acn  acnTypes o.Location o children acnParams us
            let choiceIDForNone =  ToC (o.id.AcnAbsPath.Tail.StrJoin("_").Replace("#","elem")) + "_NONE"

            {Choice.id = o.id; tasInfo = o.tasInfo; uperMaxSizeInBits= o.uperMaxSizeInBits; uperMinSizeInBits=o.uperMinSizeInBits; children = children; cons=o.cons; withcons = o.withcons; baseType = newBase; Location = o.Location; choiceIDForNone = choiceIDForNone; acnMaxSizeInBits = acnMaxSizeInBits; acnMinSizeInBits = acnMinSizeInBits; acnEncodingClass = encClass; alignment = alignment}, us)
        Choice
    


let foldMap = CloneTree.foldMap

let mapBAstToCast (r:BAst.AstRoot) (acn:AcnTypes.AcnAst) : AstRoot=
    let initialState = {State.currentTypes = []}
    let acnConstants    = acn.Constants
    let acnParameters   = acn.Parameters |> List.map(fun p -> {ModName = p.ModName;TasName = p.TasName; Name = p.Name; Asn1Type = p.Asn1Type;Location=p.Location})
    let acnTypes = acn.Types |> List.map(fun t -> t.TypeID, t) |> Map.ofList
    let newTypeAssignments, finalState = 
        r.TypeAssignments |>
        foldMap (fun cs t ->
            let newType, newState = mapBTypeToCType r t acn acnTypes acnParameters cs
            newType, {newState with currentTypes = newState.currentTypes@[newType]}
        ) initialState  
    let newTypes = finalState.currentTypes
    let newTypesMap = newTypes |> List.map(fun t -> t.id, t) |> Map.ofList
    let acnLinks    = 
        acn.References |>
        List.map(fun l ->
            let decTypeId = ReferenceToType.createFromAcnAbsPath l.TypeID
            let acnParams = acnParameters |> List.filter(fun x -> x.ModName = l.TypeID.Head && x.TasName = l.TypeID.Tail.Head)
            let decType = 
                match newTypesMap.TryFind decTypeId with
                | Some t -> t
                | None   -> raise(SemanticError (l.Location, sprintf "Invalid Reference '%s'" (l.TypeID.ToString()) ))
                
            let determinantId  =
                let parentId = decTypeId.parentTypeId
                let determinantId childRelPath = 
                    let determinantId = parentId |> Option.map (fun x -> x.appendLongChildId childRelPath)
                    match determinantId with
                    | None                  -> raise(SemanticError (l.Location, sprintf "Invalid Reference '%s'" (l.LongRef.ToString()) ))
                    | Some determinantId    -> determinantId
                match l.LongRef with
                | []            -> raise(SemanticError (l.Location,"Invalid Reference (empty path)" ))
                | fldName::[]   ->
                    match acnParams |> Seq.tryFind(fun p -> p.Name = fldName) with
                    | Some p    -> 
                        match decTypeId.BelongingTypeAssignment with
                        | Some tasId    -> tasId.id.getParamId p.Name
                        | None          -> raise(SemanticError (l.Location,"Invalid type id" ))
                    | None      -> determinantId l.LongRef
                | _             -> determinantId l.LongRef

            match l.Kind with
            | AcnTypes.RefTypeArgument prmName   -> {AcnLink.decType = decType; determinant = determinantId ; linkType = RefTypeArgument  prmName}
            | AcnTypes.SizeDeterminant           -> {AcnLink.decType = decType; determinant = determinantId ; linkType = SizeDeterminant}
            | AcnTypes.PresenceBool              -> {AcnLink.decType = decType; determinant = determinantId ; linkType = PresenceBool}
            | AcnTypes.PresenceInt intCon        -> {AcnLink.decType = decType; determinant = determinantId ; linkType = PresenceInt  (AcnTypes.EvaluateConstant acnConstants intCon)}
            | AcnTypes.PresenceStr strCon        -> {AcnLink.decType = decType; determinant = determinantId ; linkType = PresenceStr  strCon}
            | AcnTypes.ChoiceDeteterminant       -> {AcnLink.decType = decType; determinant = determinantId ; linkType = ChoiceDeteterminant})

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
        acnParameters = acnParameters
        acnConstants = acnConstants
        acnLinks = acnLinks
    }

