﻿module GenerateAcnIcd
open System.Globalization
open System
open System.Numerics
open System.IO
open FsUtils
open CommonTypes
open DAst
open DastFold
open DAstUtilFunctions
open Antlr.Asn1
open Antlr.Acn
open Antlr.Runtime


let Kind2Name  = GenerateUperIcd.Kind2Name

let rec getASN1Name (r:AstRoot) (t:Asn1Type) =
    match t.Kind with
    | Integer       _  -> "INTEGER"
    | Real          _ -> "REAL"
    | IA5String     _ -> "IA5String"
    | OctetString   _ -> "OCTET STRING"
    | NullType      _ -> "NULL"
    | BitString     _ -> "BIT STRING"
    | Boolean       _ -> "BOOLEAN"
    | Enumerated    _  -> "ENUMERATED"
    | SequenceOf    _  -> "SEQUENCE OF"
    | Sequence     _  -> "SEQUENCE"
    | Choice       _  -> "CHOICE"
    | ObjectIdentifier   _       -> "OBJECT IDENTIFIER"
    | TimeType     _  -> "TIME"
    | ReferenceType _ -> getASN1Name r t.ActualType


let makeEmptyNull (s:string) =
    match s with
    | null  -> null
    | _     -> match s.Trim() with "" -> null | _ -> s

// Generate a formatted version of the ACN grammar given as input,
// using the stringtemplate layouts.
let PrintAcnAsHTML stgFileName (r:AstRoot)  =
    let acnTokens = [|
            "endianness"; "big"; "little"; "encoding"; "pos-int"; "twos-complement"; "BCD"; "ASCII";
            "IEEE754-1985-32"; "IEEE754-1985-64"; "size"; "null-terminated"; "align-to-next"; "byte";
            "word"; "dword"; "encode-values"; "true-value"; "false-value"; "pattern"; "present-when";
            "determinant"; "DEFINITIONS"; "BEGIN"; "END"; "CONSTANT"; "NOT"; "INTEGER"; "BOOLEAN"; "NULL"|]
    let colorize (t: IToken, tasses: string array) =
            let lt = icd_acn.LeftDiple stgFileName ()
            let gt = icd_acn.RightDiple stgFileName ()
            let containedIn = Array.exists (fun elem -> elem = t.Text) 
            let isAcnKeyword = containedIn acnTokens
            let isType = containedIn tasses
            let safeText = t.Text.Replace("<",lt).Replace(">",gt)
            let uid =
                match isType with
                |true -> icd_acn.TasName stgFileName safeText (ToC safeText)
                |false -> safeText
            let colored =
                match t.Type with
                |acnLexer.StringLiteral
                |acnLexer.BitStringLiteral -> icd_acn.StringLiteral stgFileName safeText
                |acnLexer.UID -> uid
                |acnLexer.COMMENT
                |acnLexer.COMMENT2 -> icd_acn.Comment stgFileName safeText
                |_ -> safeText
            if isAcnKeyword then icd_acn.AcnKeyword stgFileName safeText else colored

    let tasNames = r.Files |> Seq.collect(fun f -> f.Modules) |> Seq.collect(fun x -> x.TypeAssignments) |> Seq.map(fun x -> x.Name.Value) |> Seq.toArray
    
    r.acnParseResults |>
    Seq.map(fun pr -> pr.fileName, pr.tokens) |>
    Seq.map(fun (fName, tokens) -> 
            //let f = r.Files |> Seq.find(fun x -> Path.GetFileNameWithoutExtension(x.FileName) = Path.GetFileNameWithoutExtension(fName))
            //let tasNames = f.Modules |> Seq.collect(fun x -> x.TypeAssignments) |> Seq.map(fun x -> x.Name.Value) |> Seq.toArray
            let content = tokens |> Seq.map(fun token -> colorize(token,tasNames))
            icd_acn.EmmitFilePart2  stgFileName (Path.GetFileName fName) (content |> Seq.StrJoin "")
    )

let foldGenericCon = GenerateUperIcd.foldGenericCon
let foldRangeCon   = GenerateUperIcd.foldRangeCon

type SequenceRow = {
    sClass              : string
    nIndex              : BigInteger
    chName              : string
    sComment            : string
    sPresentWhen        : string
    sType               : string
    sAsn1Constraints    : string
    sMinBits            : string
    sMaxBits            : string
    noAlignToNextSize   : string
    soUnit              : string option
}
let enumStg : GenerateUperIcd.StgCommentLineMacros = 
    {
        NewLine                  = icd_acn.NewLine                 
        EmitEnumItem             = icd_acn.EmitEnumItem            
        EmitEnumItemWithComment  = icd_acn.EmitEnumItemWithComment 
        EmitEnumInternalContents = icd_acn.EmitEnumInternalContents
    } 

let handleNullType stgFileName (encodingPattern : AcnGenericTypes.PATTERN_PROP_VALUE option) defaultRetValue =
    match encodingPattern with
    | Some(AcnGenericTypes.PATTERN_PROP_BITSTR_VALUE bitStr)       -> icd_acn.NullTypeWithBitPattern  stgFileName  bitStr.Value
    | Some(AcnGenericTypes.PATTERN_PROP_OCTSTR_VALUE byteList     )-> icd_acn.NullTypeWithBytePattern stgFileName  (byteList |> List.map (fun z -> z.Value)) 
    | None                                                        -> defaultRetValue


let icd_acn_EmmitSeqChild_RefType (fileName:string) (r:AstRoot) (allExportedTypes:Set<string>) (modName:string)  (sRefName:string) (soRefNameC:string) = 
    //match allExportedTypes |> Seq.exists(fun z -> z.t.id = )
    match allExportedTypes.Contains(sRefName) with
    | true  -> icd_acn.EmmitSeqChild_RefType fileName sRefName (Some soRefNameC)
    | false -> 
        match r.Modules |> Seq.tryFind(fun m -> m.Name.Value = modName) with
        | Some m ->
            match m.TypeAssignments |> Seq.tryFind(fun ts -> ts.Name.Value = sRefName) with
            | Some ts ->
                let baseAsn1Type = getASN1Name r ts.Type
                icd_acn.EmmitSeqChild_RefType fileName (sRefName + " (" + baseAsn1Type + ")") None
            | None ->  icd_acn.EmmitSeqChild_RefType fileName (sRefName + "1") None
        | None ->  icd_acn.EmmitSeqChild_RefType fileName (sRefName + "2")  None

let emitSequenceComponent (r:AstRoot) (allExportedTypes:Set<string>) (modName:string) stgFileName (optionalLikeUperChildren:Asn1Child list) (i:int) (ch:SeqChildInfo) =
    let GetCommentLine = GenerateUperIcd.GetCommentLineFactory stgFileName enumStg
    let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())
    let nIndex = BigInteger i
    let sPresentWhen, bAlwaysAbsent = 
        match ch with
        | AcnChild  _ -> "always", false
        | Asn1Child ch  ->
            let aux1 = function
                | 1 -> "st"
                | 2 -> "nd"
                | 3 -> "rd"
                | _ -> "th"
            match ch.Optionality with
            | None                      -> "always", false
            | Some(Asn1AcnAst.AlwaysPresent)   -> "always", false
            | Some(Asn1AcnAst.AlwaysAbsent)    -> "never", true
            | Some(Asn1AcnAst.Optional opt)    ->
                match opt.acnPresentWhen with
                | None  ->  
                    let nBit =  optionalLikeUperChildren |> Seq.findIndex(fun x -> x.Name.Value = ch.Name.Value) |> (+) 1
                    sprintf "when the %d%s bit of the bit mask is set" nBit (aux1 nBit), false
                | Some (AcnGenericTypes.PresenceWhenBool presWhen)     ->
                    let dependency = r.deps.acnDependencies |> List.find(fun d -> d.asn1Type = ch.Type.id )
                    //match dependency.dependencyKind with
                    sprintf "when %s is true" presWhen.AsString , false
                | Some (AcnGenericTypes.PresenceWhenBoolExpression acnExp)  ->
                    let _, debugStr = AcnGenericCreateFromAntlr.printDebug acnExp
                    sprintf "when %s is true" debugStr, false

    let sType, sComment, sAsn1Constraints, nAlignToNextSize, soUnit  = 
        match ch with
        | Asn1Child ch  ->
            let sType = 
                let defaultRetValue = 
                    match ch.Type.Kind with
                    | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> 
                        icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes modName  ch.Type.FT_TypeDefintion.[CommonTypes.C].asn1Name (ToC ch.Type.FT_TypeDefintion.[CommonTypes.C].asn1Name)
                    | OctetString o -> "OCTET STRING"
                    | _ ->
                        match ch.Type.ActualType.Kind with
                        | Sequence _
                        | Choice _
                        | SequenceOf _ -> 
                            icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes modName  ch.Type.id.AsString.RDD (ToC ch.Type.id.AsString.RDD)
                        | _            ->
                            icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes modName  ch.Type.FT_TypeDefintion.[CommonTypes.C].asn1Name (ToC ch.Type.FT_TypeDefintion.[CommonTypes.C].asn1Name)
                match ch.Type.ActualType.Kind with
                | DAst.NullType       o  when o.baseInfo.acnProperties.encodingPattern.IsSome  -> 
                                                handleNullType stgFileName o.baseInfo.acnProperties.encodingPattern defaultRetValue
                | _                       -> defaultRetValue
            let soUnit =  GenerateUperIcd.getUnits ch.Type
            sType, GetCommentLine ch.Comments ch.Type, ch.Type.ConstraintsAsn1Str |> Seq.StrJoin "", AcnEncodingClasses.getAlignmentSize ch.Type.acnAligment, soUnit
        | AcnChild ch   ->
            let commentLine =
                ch.Comments |> Seq.StrJoin (enumStg.NewLine stgFileName ()) 
                        

            let sType,consAsStt = 
                match ch.Type with
                | Asn1AcnAst.AcnInteger                o -> 
                    let constAsStr = DAstAsn1.createAcnInteger (o.cons@o.withcons) |> Seq.StrJoin ""
                    match o.inheritInfo with
                    | None                              ->  icd_acn.Integer           stgFileName ()    , constAsStr
                    | Some inhInfo                      ->  icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes modName  inhInfo.tasName (ToC inhInfo.tasName) , constAsStr
                | Asn1AcnAst.AcnNullType               o -> 
                    let sType = handleNullType stgFileName o.acnProperties.encodingPattern (icd_acn.NullType           stgFileName ())
                    sType, ""
                | Asn1AcnAst.AcnBoolean                o -> icd_acn.Boolean           stgFileName (), ""
                | Asn1AcnAst.AcnReferenceToEnumerated  o -> icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes modName  o.tasName.Value (ToC o.tasName.Value), ""
                | Asn1AcnAst.AcnReferenceToIA5String   o -> icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes modName  o.tasName.Value (ToC o.tasName.Value), ""
            sType, commentLine, consAsStt, AcnEncodingClasses.getAlignmentSize ch.Type.acnAligment, None
    let name = ch.Name
    let noAlignToNextSize = if nAlignToNextSize = 0I then None else (Some nAlignToNextSize)
    let acnMaxSizeInBits = ch.acnMaxSizeInBits - nAlignToNextSize
    let acnMinSizeInBits = (if bAlwaysAbsent then 0I else ch.acnMinSizeInBits) - nAlignToNextSize
    let sMaxBits, sMaxBytes = acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(acnMaxSizeInBits)/8.0)).ToString()
    let sMinBits, sMinBytes = acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(acnMinSizeInBits)/8.0)).ToString()
    icd_acn.EmmitSeqOrChoiceRow stgFileName sClass nIndex ch.Name sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits noAlignToNextSize soUnit


let rec printType stgFileName (tas:GenerateUperIcd.IcdTypeAssignment) (t:Asn1Type) (m:Asn1Module) (allExportedTypes:Set<string>) (r:AstRoot)  isAnonymousType : string list=
    let GetCommentLine = GenerateUperIcd.GetCommentLineFactory stgFileName enumStg
        
    let hasAcnDef = r.acnParseResults |> Seq.collect (fun p -> p.tokens) |> Seq.exists(fun x -> x.Text = tas.name)

    let sTasName = tas.name
    let sKind = Kind2Name stgFileName t
    let sMaxBits, sMaxBytes = t.acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(t.acnMaxSizeInBits)/8.0)).ToString()
    let sMinBits, sMinBytes = t.acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(t.acnMinSizeInBits)/8.0)).ToString()
    let sMaxBitsExplained =  ""
    let sCommentLine = GetCommentLine tas.comments t
    let myParams colSpan= 
        t.acnParameters |>
        List.mapi(fun i x -> 
            let sType = match x.asn1Type with
                            | AcnGenericTypes.AcnParamType.AcnPrmInteger    _         -> "INTEGER"
                            | AcnGenericTypes.AcnParamType.AcnPrmBoolean    _         -> "BOOLEAN"
                            | AcnGenericTypes.AcnParamType.AcnPrmNullType   _         -> "NULL"
                            | AcnGenericTypes.AcnParamType.AcnPrmRefType(md,ts)     -> icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes md.Value  ts.Value (ToC ts.Value)

            icd_acn.PrintParam stgFileName (i+1).AsBigInt x.name sType colSpan)



    let handlePrimitive (sAsn1Constraints:string)   =
        let ret = icd_acn.EmitPrimitiveType stgFileName isAnonymousType sTasName (ToC sTasName) hasAcnDef sKind sMinBytes sMaxBytes sMaxBitsExplained sCommentLine ( if sAsn1Constraints.Trim() ="" then "N.A." else sAsn1Constraints) sMinBits sMaxBits (myParams 2I) (sCommentLine.Split [|'\n'|]) t.unitsOfMeasure
        [ret]
    match t.Kind with
    | Integer    o   ->
        let sAsn1Constraints = o.AllCons |> List.map (foldRangeCon (fun z -> z.ToString())) |> Seq.StrJoin "" 
        handlePrimitive sAsn1Constraints
    | Real    o   ->
        let sAsn1Constraints = o.AllCons |> List.map (foldRangeCon (fun z -> z.ToString())) |> Seq.StrJoin ""
        handlePrimitive sAsn1Constraints
    | Boolean   o   ->
        let sAsn1Constraints = o.AllCons |> List.map (foldGenericCon (fun z -> z.ToString().ToUpper() )) |> Seq.StrJoin ""
        handlePrimitive sAsn1Constraints
    | NullType  o   ->
        let sAsn1Constraints = ""
        handlePrimitive sAsn1Constraints
    | Enumerated  o   ->
        let sAsn1Constraints = ""
        handlePrimitive sAsn1Constraints
    | ObjectIdentifier  o   ->
        let sAsn1Constraints = ""
        handlePrimitive sAsn1Constraints
    |ReferenceType o when  o.baseInfo.encodingOptions.IsNone ->
        printType stgFileName tas o.resolvedType m allExportedTypes r isAnonymousType
    |Sequence seq   -> 
        let optionalLikeUperChildren = 
            seq.Asn1Children 
            |> Seq.filter (fun x -> 
                match x.Optionality with
                | None  -> false
                | Some (Asn1AcnAst.Optional opt)  ->
                    match opt.acnPresentWhen with
                    | Some (AcnGenericTypes.PresenceWhenBool _) -> false
                    | Some (AcnGenericTypes.PresenceWhenBoolExpression _) -> false
                    | None                      -> true
                | _                               -> false) 
            |> Seq.toList
        let SeqPreamble =
            match optionalLikeUperChildren with
            | []    -> None
            | _     ->
                let arrsOptWihtNoPresentWhenChildren = 
                    optionalLikeUperChildren |> Seq.mapi(fun i c -> icd_acn.EmmitSequencePreambleSingleComment stgFileName (BigInteger (i+1)) c.Name.Value)

                let nLen = optionalLikeUperChildren |> Seq.length
                let ret = icd_acn.EmmitSeqOrChoiceRow stgFileName (icd_acn.OddRow stgFileName ()) 1I "Preamble" (icd_acn.EmmitSequencePreambleComment stgFileName arrsOptWihtNoPresentWhenChildren)  "always"  "Bit mask" "N.A." (nLen.ToString()) (nLen.ToString()) None None
                Some ret
        let emitSequenceRow (i:int, curResult:string list) (ch:SeqChildInfo) =
            let di, newLines =   
                match ch with
                | AcnChild  _ -> 1, [emitSequenceComponent r allExportedTypes m.Name.Value stgFileName optionalLikeUperChildren i ch]
                | Asn1Child ach  ->
                                1, [emitSequenceComponent r allExportedTypes m.Name.Value stgFileName optionalLikeUperChildren i ch]
                (*
                    match ach.Type.Kind with
                    | OctetString o when o.baseInfo.acnEncodingClass = Asn1AcnAst.SizeableAcnEncodingClass.SZ_EC_uPER ->
                        let lengthLine =
                            let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())

                            icd_acn.EmmitSeqOrChoiceRow stgFileName sClass (BigInteger i) "length" "uper length determinant"  "???"  "OCTET STRING" "N/A" sMinBits sMaxBits None None

                        1, [emitSequenceComponent r stgFileName optionalLikeUperChildren i ch]
                    | _ -> 1, [emitSequenceComponent r stgFileName optionalLikeUperChildren i ch]
                *)
            (i+di, curResult@newLines)
        let arChildren idx = 
            seq.children |> 
            Seq.fold emitSequenceRow (idx, []) |>
            snd
//        let arChildren idx = 
//            seq.children |> 
//            Seq.mapi(fun i ch -> emitSequenceComponent r stgFileName optionalLikeUperChildren (idx + i) ch )  
//            |> Seq.toList
        let childTasses = 
            seq.children |> 
            Seq.map(fun ch -> 
                    match ch with
                    | Asn1Child ch  ->
                        match ch.Type.Kind with
                        | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> []
                        | _     ->
                            match ch.Type.ActualType.Kind with
                            | Sequence _
                            | Choice _
                            | SequenceOf _ -> 
                                let chTas = {tas with name=ch.Type.id.AsString.RDD; t=ch.Type; comments = Array.concat [ tas.comments; [|sprintf "Acn inline encoding in the context of %s type and %s component" tas.name ch.Name.Value|]]; isBlue = true }
                                printType stgFileName chTas ch.Type m allExportedTypes r isAnonymousType
                            | _            -> []
                    | AcnChild _       -> [])|> 
            Seq.collect id |> Seq.toList
        let arRows =
            match SeqPreamble with 
            | None          -> arChildren 1
            | Some(prm)     -> prm::(arChildren 2)
        let seqRet = icd_acn.EmitSequenceOrChoice stgFileName isAnonymousType sTasName (ToC sTasName) hasAcnDef "SEQUENCE" sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arRows (myParams 4I) (sCommentLine.Split [|'\n'|])
        [seqRet] @ childTasses
    |Choice chInfo   ->
        let EmitSeqOrChoiceChild (i:int) (ch:ChChildInfo)  getPresence =
            let sClass = if i % 2 = 0 then (icd_acn.EvenRow stgFileName ()) else (icd_acn.OddRow stgFileName ())
            let nIndex = BigInteger i
            let sComment = GetCommentLine ch.Comments ch.chType

            let sPresentWhen = getPresence i ch

            let sType = 
                let defaultRetValue = icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes m.Name.Value  ch.chType.FT_TypeDefintion.[CommonTypes.C].asn1Name (ToC ch.chType.FT_TypeDefintion.[CommonTypes.C].asn1Name)
                match ch.chType.Kind with
                | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> defaultRetValue
                | _  ->
                    match ch.chType.ActualType.Kind with
                    | Sequence _
                    | Choice _
                    | SequenceOf _ -> 
                        icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes m.Name.Value   ch.chType.id.AsString.RDD (ToC ch.chType.id.AsString.RDD)
                    | DAst.NullType       o  when o.baseInfo.acnProperties.encodingPattern.IsSome  -> 
                                                    handleNullType stgFileName o.baseInfo.acnProperties.encodingPattern defaultRetValue
                    | _                       -> defaultRetValue

            let sAsn1Constraints = ch.chType.ConstraintsAsn1Str |> Seq.StrJoin ""
            let sMaxBits, sMaxBytes = ch.chType.acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(ch.chType.acnMaxSizeInBits)/8.0)).ToString()
            let sMinBits, sMinBytes = ch.chType.acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(ch.chType.acnMinSizeInBits)/8.0)).ToString()
            let soUnit = GenerateUperIcd.getUnits ch.chType
            icd_acn.EmmitSeqOrChoiceRow stgFileName sClass nIndex ch.Name.Value sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits None soUnit
        let children = chInfo.children
        let children = children |> List.filter(fun ch -> match ch.Optionality with  Some (Asn1AcnAst.ChoiceAlwaysAbsent) -> false | _ -> true)
        let arrRows = 
            match chInfo.ancEncClass with
            | CEC_uper          -> 
                let ChIndex, curI =
                    //let optChild = chInfo.children |> Seq.mapi(fun i c -> icd_uper.EmmitChoiceIndexSingleComment stgFileName (BigInteger (i+1)) c.Name.Value)
                    match children.Length <= 1 with
                    | true    -> [], 1
                    | false     ->
                        let sComment = icd_acn.EmmitChoiceIndexComment stgFileName ()
                        let indexSize = (GetChoiceUperDeterminantLengthInBits(BigInteger(Seq.length children))).ToString()
                        let ret = icd_acn.EmmitSeqOrChoiceRow stgFileName (icd_acn.OddRow stgFileName ()) (BigInteger 1) "ChoiceIndex" sComment  "always"  "unsigned int" "N.A." indexSize indexSize None None
                        [ret], 2
                    //icd_acn.EmmitSeqOrChoiceRow stgFileName sClass nIndex ch.Name.Value sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits
                let getPresenceWhenNone_uper (i:int) (ch:ChChildInfo) =
                    match children.Length <= 1 with
                    | true  -> "always"
                    | false ->
                        let index = children |> Seq.findIndex (fun z -> z.Name.Value = ch.Name.Value) 
                        sprintf "ChoiceIndex = %d" index
                    //sprintf "ChoiceIndex = %d" i
                let EmitChild (i:int) (ch:ChChildInfo) = EmitSeqOrChoiceChild i ch  getPresenceWhenNone_uper
                let arChildren = children |> Seq.mapi(fun i ch -> EmitChild (curI + i) ch) |> Seq.toList
                ChIndex@arChildren
            | CEC_enum    (r,d)     -> 
                let getPresence (i:int) (ch:ChChildInfo) =
                    let refToStr id =
                        match id with
                        | ReferenceToType sn -> sn |> List.rev |> List.head |> (fun x -> x.AsString) 

                    sprintf "%s = %s" (refToStr d.id) ch.Name.Value
                let EmitChild (i:int) (ch:ChChildInfo) = EmitSeqOrChoiceChild i ch  getPresence
                children |> Seq.mapi(fun i ch -> EmitChild (1 + i) ch) |> Seq.toList
            | CEC_presWhen      -> 
                let getPresence (i:int) (ch:ChChildInfo) =
                    let getPresenceSingle (pc:AcnGenericTypes.AcnPresentWhenConditionChoiceChild) = 
                        match pc with
                        | AcnGenericTypes.PresenceInt   (rp, intLoc) -> sprintf "%s=%A" rp.AsString intLoc.Value
                        | AcnGenericTypes.PresenceStr   (rp, strLoc) -> sprintf "%s=%A" rp.AsString strLoc.Value
                    ch.acnPresentWhenConditions |> Seq.map getPresenceSingle |> Seq.StrJoin " AND " 
                let EmitChild (i:int) (ch:ChChildInfo) = EmitSeqOrChoiceChild i ch  getPresence
                children |> Seq.mapi(fun i ch -> EmitChild (1 + i) ch) |> Seq.toList
        let chRet = icd_acn.EmitSequenceOrChoice stgFileName isAnonymousType sTasName (ToC sTasName) hasAcnDef "CHOICE" sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arrRows (myParams 4I) (sCommentLine.Split [|'\n'|])
        let childTasses = 
            chInfo.children |> 
            Seq.map(fun ch -> 
                    match ch.chType.Kind with
                    | ReferenceType o when not o.baseInfo.hasExtraConstrainsOrChildrenOrAcnArgs -> []
                    | _  ->
                        match ch.chType.ActualType.Kind with
                        | Sequence _
                        | Choice _
                        | SequenceOf _ -> 
                            let chTas = {tas with name=ch.chType.id.AsString.RDD; t=ch.chType; comments = Array.concat [ tas.comments; [|sprintf "Acn inline encoding in the context of %s type and %s component" tas.name ch.Name.Value|]]; isBlue = true }
                            printType stgFileName chTas ch.chType m allExportedTypes r isAnonymousType
                        | _            -> [] )|> 
            Seq.collect id |> Seq.toList
        [chRet]@childTasses
    | IA5String  o  ->
        let nMin, nMax, encClass = o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
        let sType, characterSizeInBits = 
            match encClass with
            | Asn1AcnAst.Acn_Enc_String_uPER                                   characterSizeInBits             -> "NUMERIC CHARACTER" , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_uPER_Ascii                             characterSizeInBits             -> "ASCII CHARACTER"   , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_Ascii_Null_Teminated                  (characterSizeInBits, nullChars)  -> "ASCII CHARACTER"  , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_Ascii_External_Field_Determinant      (characterSizeInBits, rp)        -> "ASCII CHARACTER"   , characterSizeInBits.ToString()
            | Asn1AcnAst.Acn_Enc_String_CharIndex_External_Field_Determinant  (characterSizeInBits, rp)        -> "NUMERIC CHARACTER" , characterSizeInBits.ToString()
        let ChildRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_acn.EvenRow stgFileName () else icd_acn.OddRow stgFileName ()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber stgFileName i
            let sComment = ""
            icd_acn.EmmitChoiceChild stgFileName sClass nIndex sFieldName sComment  sType "" characterSizeInBits characterSizeInBits
        let NullRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_acn.EvenRow stgFileName () else icd_acn.OddRow stgFileName ()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber stgFileName i
            let sComment = "NULL Character"
            icd_acn.EmmitChoiceChild stgFileName sClass nIndex sFieldName sComment  sType "" characterSizeInBits characterSizeInBits
                
        let comment = "Special field used by ACN indicating the number of items."
        let sCon = t.ConstraintsAsn1Str |> Seq.StrJoin ""
        let sCon =  if sCon.Trim() ="" then "N.A." else sCon
        let lenDetSize = GetNumberOfBitsForNonNegativeInteger ( (o.baseInfo.maxSize.acn - o.baseInfo.minSize.acn))
        let arRows, sExtraComment =
            match encClass with
            | Asn1AcnAst.Acn_Enc_String_uPER                                  nSizeInBits              -> 
                let lengthLine = icd_acn.EmmitChoiceChild stgFileName (icd_acn.OddRow stgFileName ()) 1I "Length" comment    "unsigned int" sCon (lenDetSize.ToString()) (lenDetSize.ToString())
                lengthLine::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I ( nMax))::[], ""
            | Asn1AcnAst.Acn_Enc_String_uPER_Ascii                            nSizeInBits              -> 
                let lengthLine = icd_acn.EmmitChoiceChild stgFileName (icd_acn.OddRow stgFileName ()) 1I "Length" comment    "unsigned int" sCon (lenDetSize.ToString()) (lenDetSize.ToString())
                lengthLine::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I ( nMax))::[], ""
            | Asn1AcnAst.Acn_Enc_String_Ascii_Null_Teminated                  (nSizeInBits, nullChars)  -> 
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::(NullRow 0I ( (nMax+1I)))::[],""
            | Asn1AcnAst.Acn_Enc_String_Ascii_External_Field_Determinant      (nSizeInBits, rp)        -> 
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::[], sprintf "Length determined by external field %s" (rp.AsString)
            | Asn1AcnAst.Acn_Enc_String_CharIndex_External_Field_Determinant  (nSizeInBits, rp)        -> 
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I ( nMax))::[], sprintf "Length determined by external field %s" (rp.AsString)
        let sCommentLine = match sCommentLine with
                           | null | ""  -> sExtraComment
                           | _          -> sprintf "%s%s%s" sCommentLine (icd_acn.NewLine stgFileName ()) sExtraComment

        let strRet = icd_acn.EmitSizeable stgFileName isAnonymousType sTasName  (ToC sTasName) hasAcnDef (Kind2Name stgFileName t) sMinBytes sMaxBytes sMaxBitsExplained (makeEmptyNull sCommentLine) arRows (myParams 2I) (sCommentLine.Split [|'\n'|])
        [strRet]
    | ReferenceType _
    | OctetString _
    | BitString  _
    | SequenceOf _   ->
        let nMin, nMax, encClass =
            match t.Kind with
            | OctetString o   ->
               o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
            | BitString   o   ->
                o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
            | SequenceOf  o   ->
                o.baseInfo.minSize.acn, o.baseInfo.maxSize.acn, o.baseInfo.acnEncodingClass
            | ReferenceType o   ->
                match o.baseInfo.encodingOptions with
                | None      -> raise(BugErrorException "")
                | Some eo   ->
                    eo.minSize.acn, eo.maxSize.acn, eo.acnEncodingClass
            | _                            -> raise(BugErrorException "")
        let ChildRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_acn.EvenRow stgFileName () else icd_acn.OddRow stgFileName ()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber stgFileName i
            let sComment = ""
            let sType, sAsn1Constraints, sMinBits, sMaxBits = 
                match t.Kind with
                | SequenceOf(seqOf) ->
                    let child = seqOf.childType
                    let sAsn1Constraints = child.ConstraintsAsn1Str |> Seq.StrJoin ""
                    let ret = ( if sAsn1Constraints.Trim() ="" then "N.A." else sAsn1Constraints)
                    let sMaxBits, sMaxBytes = child.acnMaxSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(child.acnMaxSizeInBits)/8.0)).ToString()
                    let sMinBits, sMinBytes = child.acnMinSizeInBits.ToString(), BigInteger(System.Math.Ceiling(double(child.acnMinSizeInBits)/8.0)).ToString()
                    let sType =
                        icd_acn_EmmitSeqChild_RefType stgFileName r allExportedTypes m.Name.Value child.FT_TypeDefintion.[CommonTypes.C].asn1Name (ToC child.FT_TypeDefintion.[CommonTypes.C].asn1Name)
//                        match child.Kind with
//                        | ReferenceType ref -> icd_acn_EmmitSeqChild_RefType stgFileName ref.baseInfo.tasName.Value (ToC ref.baseInfo.tasName.Value)
//                        | _                       -> Kind2Name stgFileName child
                    sType, ret, sMinBits, sMaxBits
                | OctetString        _         -> "OCTET", "", "8", "8"
                | BitString          _         -> "BIT", "", "1","1"
                | ReferenceType o   ->
                    match o.baseInfo.encodingOptions with
                    | None      -> raise(BugErrorException "")
                    | Some eo   ->
                        match eo.octOrBitStr with
                        | ContainedInOctString  -> "OCTET", "", "8", "8"   
                        | ContainedInBitString  -> "BIT", "", "1","1"
                | _                            -> raise(BugErrorException "")
            icd_acn.EmmitChoiceChild stgFileName sClass nIndex sFieldName sComment  sType sAsn1Constraints sMinBits sMaxBits
        let sFixedLengthComment = sprintf "Length is Fixed equal to %A, so no length determinant is encoded." nMax
        let arRows, sExtraComment =
            match encClass, nMax >= 2I with
            | Asn1AcnAst.SZ_EC_FIXED_SIZE, _                     
            | Asn1AcnAst.SZ_EC_LENGTH_EMBEDDED _, _                     -> 
                let sizeUperRange =  CommonTypes.Concrete(nMin, nMax)
                let sFixedLengthComment (nMax: BigInteger) =
                    sprintf "Length is fixed to %A elements (no length determinant is needed)." nMax
                let LengthRow =
                    let nMin, nLengthSize = 
                        match sizeUperRange with
                        | CommonTypes.Concrete(a,b)  when a=b       -> 0I, 0I
                        | CommonTypes.Concrete(a,b)                 -> (GetNumberOfBitsForNonNegativeInteger(b - a)), (GetNumberOfBitsForNonNegativeInteger(b - a))
                        | CommonTypes.NegInf(_)                     -> raise(BugErrorException "")
                        | CommonTypes.PosInf(b)                     ->  8I, 16I
                        | CommonTypes.Full                          -> 8I, 16I
                    let comment = "Special field used by ACN to indicate the number of items present in the array."
                    let ret = t.ConstraintsAsn1Str |> Seq.StrJoin "" //+++ t.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin "" 
                    let sCon = ( if ret.Trim() ="" then "N.A." else ret)

                    icd_acn.EmmitChoiceChild stgFileName (icd_acn.OddRow stgFileName ()) (BigInteger 1) "Length" comment    "unsigned int" sCon (nMin.ToString()) (nLengthSize.ToString())

                match sizeUperRange with
                | CommonTypes.Concrete(a,b)  when a=b && b<2I     -> [ChildRow 0I 1I], "The array contains a single element."
                | CommonTypes.Concrete(a,b)  when a=b && b=2I     -> (ChildRow 0I 1I)::(ChildRow 0I 2I)::[], (sFixedLengthComment b)
                | CommonTypes.Concrete(a,b)  when a=b && b>2I     -> (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I b)::[], (sFixedLengthComment b)
                | CommonTypes.Concrete(a,b)  when a<>b && b<2I    -> LengthRow::(ChildRow 1I 1I)::[],""
                | CommonTypes.Concrete(a,b)                       -> LengthRow::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I b)::[], ""
                | CommonTypes.PosInf(_)
                | CommonTypes.Full                                -> LengthRow::(ChildRow 1I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 1I 65535I)::[], ""
                | CommonTypes.NegInf(_)                           -> raise(BugErrorException "")

            | Asn1AcnAst.SZ_EC_ExternalField relPath,false    -> 
                (ChildRow 0I 1I)::[], sprintf "Length is determined by the external field: %s" relPath.AsString
            | Asn1AcnAst.SZ_EC_ExternalField relPath,true     -> 
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I (nMax))::[], sprintf "Length determined by external field %s" relPath.AsString
            | Asn1AcnAst.SZ_EC_TerminationPattern bitPattern, false ->
                (ChildRow 0I 1I)::[], sprintf "Length is determined by the stop marker '%s'" bitPattern.Value
            | Asn1AcnAst.SZ_EC_TerminationPattern bitPattern, true ->
                (ChildRow 0I 1I)::(icd_acn.EmitRowWith3Dots stgFileName ())::(ChildRow 0I (nMax))::[], sprintf "Length is determined by the stop marker '%s'" bitPattern.Value

                

        let sCommentLine = match sCommentLine with
                           | null | ""  -> sExtraComment
                           | _          -> sprintf "%s%s%s" sCommentLine (icd_acn.NewLine stgFileName ()) sExtraComment
        
        let sizeRet = icd_acn.EmitSizeable stgFileName false (*isAnonymousType*) sTasName  (ToC sTasName) hasAcnDef (Kind2Name stgFileName t) sMinBytes sMaxBytes sMaxBitsExplained (makeEmptyNull sCommentLine) arRows (myParams 2I) (sCommentLine.Split [|'\n'|])
        [sizeRet]

let PrintTas stgFileName (tas:GenerateUperIcd.IcdTypeAssignment) (m:Asn1Module) (allExportedTypes:Set<string>) (r:AstRoot)   =
    //let isAnonymousType = blueTasses |> Seq.exists (fun x -> x = tas.Name.Value)
    printfn "### %s" tas.name
    let tasses = printType stgFileName tas tas.t  m allExportedTypes r  tas.isBlue
    tasses |> List.map (icd_acn.EmmitTass stgFileName ) |> Seq.StrJoin "\n"


let PrintModule stgFileName (m:Asn1Module) (f:Asn1File) (allExportedTypes:Set<string>) (r:AstRoot)   =
    //let blueTasses = GenerateUperIcd.getModuleBlueTasses m |> Seq.map snd
    //let sortedTas = m.TypeAssignments //spark_spec.SortTypeAssignments m r acn |> List.rev
    let icdTasses = GenerateUperIcd.getModuleIcdTasses m

    let tases = icdTasses |> Seq.map (fun x -> PrintTas stgFileName x m allExportedTypes r ) 
    let comments = m.Comments |> Array.map (fun x -> x.Trim().Replace("--", "").Replace("/*", "").Replace("*/",""))
    let moduleName = m.Name.Value
    let title = if comments.Length > 0 then moduleName + " - " + comments.[0] else moduleName
    let commentsTail = if comments.Length > 1 then comments.[1..] else [||]
    let acnFileName = 
        match r.acnParseResults |> Seq.tryFind(fun (rp) -> rp.tokens |> Seq.exists (fun (token:IToken) -> token.Text = moduleName)) with
        | Some (rp) -> (Some (Path.GetFileName(rp.fileName)))
        | None                  -> None
    
    icd_acn.EmitModule stgFileName title (Path.GetFileName(f.FileName)) acnFileName commentsTail tases


let PrintTasses stgFileName (f:Asn1File) (allExportedTypes:Set<string>) (r:AstRoot)   =
    f.Modules |> Seq.map (fun  m -> PrintModule stgFileName m f allExportedTypes r ) |> String.concat "\n"

let emitCss (r:AstRoot) stgFileName   outFileName =
    let cssContent = icd_acn.RootCss stgFileName ()
    File.WriteAllText(outFileName, cssContent.Replace("\r", ""))

let printToC stgFileName  (r:AstRoot)   =

    let arrsModules = 
        r.Modules |> 
        List.choose(fun m -> 
            let icdTasses = GenerateUperIcd.getModuleIcdTasses m |> List.filter(fun z -> not z.isBlue)
            match icdTasses with
            | [] -> None
            | t1::_ -> 
                let tasses = icdTasses |> List.map (fun tas -> icd_acn.ToC_Module_tas stgFileName tas.name ("ICD_" + ToC(tas.name)))
                let ret = icd_acn.ToC_Module stgFileName m.Name.Value ("ICD_" + ToC(t1.name)) tasses
                Some ret)
    icd_acn.ToC stgFileName arrsModules

let DoWork (r:AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (stgFileName:string) (asn1HtmlStgFileMacros:string option)   outFileName =
    let allTass = r.Modules |> List.collect(fun m -> m.TypeAssignments)
    let allExportedTypes = 
        GenerateUperIcd.getModuleIcdTasses0 allTass |> 
        List.map(fun z -> z.name) |> Set.ofList

    let files1 = r.Files |> Seq.map (fun f -> PrintTasses stgFileName  f allExportedTypes r ) 
    let bAcnParamsMustBeExplained = true 
    let asn1HtmlMacros =
        match asn1HtmlStgFileMacros with
        | None  -> stgFileName
        | Some x -> x
    let files2 = r.Files |> Seq.map (GenerateUperIcd.PrintFile2 asn1HtmlMacros)
    let files3 = PrintAcnAsHTML stgFileName r 
    let cssFileName = Path.ChangeExtension(outFileName, ".css")
    let sToC = printToC stgFileName r
    let htmlContent = icd_acn.RootHtml stgFileName sToC files1 files2 bAcnParamsMustBeExplained files3 (Path.GetFileName(cssFileName))
    
    File.WriteAllText(outFileName, htmlContent.Replace("\r",""))
    let cssFileName = Path.ChangeExtension(outFileName, ".css");
    emitCss r stgFileName cssFileName


