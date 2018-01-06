module DAstInitialize
open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open CommonTypes
open Asn1AcnAstUtilFunctions
open DAst
open DAstUtilFunctions


(*
create c and Ada procedures that initialize an ASN.1 type.
Currently this code is not used since it is no longer required (it was originally written to handle the 'data might not be initialized' errors of spark
However, now with the 'pragma Annotate (GNATprove, False_Positive)' we can handle this case.
*)

let getFuncName (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.args.TypePrefix + x.tasName + "_Initialize"))

let createInitFunctionCommon (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage)   (o:Asn1AcnAst.Asn1Type) (typeDefinition:TypeDefintionOrReference) funcBody (iv:Asn1ValueKind) =
    let funcName            = getFuncName r l o.id.tasInfo
    let p = o.getParamType l CommonTypes.Codec.Decode
    let initTypeAssignment = match l with C -> init_c.initTypeAssignment | Ada -> init_a.initTypeAssignment
    let initTypeAssignment_def = match l with C -> init_c.initTypeAssignment_def | Ada -> init_a.initTypeAssignment_def
    let varName = p.arg.p
    let sStar = p.arg.getStar l

    let  func, funcDef  = 
            match funcName  with
            | None              -> None, None
            | Some funcName     -> 
                let content:string = funcBody p iv
                match (content.Trim()) with
                | ""        -> None, None
                | _         -> Some(initTypeAssignment varName sStar funcName  (typeDefinition.longTypedefName l) content ), Some(initTypeAssignment_def varName sStar funcName  (typeDefinition.longTypedefName l))


    {
        initFuncName            = funcName
        initFunc                = func
        initFuncDef             = funcDef
        initFuncBody            = funcBody
    }

let createIntegerInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Integer) (typeDefinition:TypeDefintionOrReference) iv =
    let initInteger = match l with C -> init_c.initInteger | Ada -> init_a.initInteger
    let funcBody (p:CallerScope) v = 
        let vl = 
            match v with
            | IntegerValue iv   -> iv
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initInteger (p.arg.getValue l) vl
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createRealInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.Real) (typeDefinition:TypeDefintionOrReference) iv = 
    let initReal = match l with C -> init_c.initReal | Ada -> init_a.initReal
    let funcBody (p:CallerScope) v = 
        let vl = 
            match v with
            | RealValue iv   -> iv
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initReal (p.arg.getValue l) vl
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createIA5StringInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.StringType   ) (typeDefinition:TypeDefintionOrReference) iv = 
    let initIA5String = match l with C -> init_c.initIA5String | Ada -> init_a.initIA5String
    let funcBody (p:CallerScope) v = 
        let vl = 
            match v with
            | StringValue iv   -> 
                iv
            | _                 -> raise(BugErrorException "UnexpectedValue")
        let arrNuls = [0 .. (o.maxSize- vl.Length)]|>Seq.map(fun x -> variables_a.PrintStringValueNull())
        initIA5String (p.arg.getValue l) (vl.Replace("\"","\"\"")) arrNuls
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createOctetStringInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.OctetString ) (typeDefinition:TypeDefintionOrReference) iv = 
    let initFixSizeBitOrOctString_bytei = match l with C -> init_c.initFixSizeBitOrOctString_bytei  | Ada -> init_a.initFixSizeBitOrOctString_bytei
    let initFixSizeBitOrOctString       = match l with C -> init_c.initFixSizeBitOrOctString        | Ada -> init_a.initFixSizeBitOrOctString
    let initFixVarSizeBitOrOctString    = match l with C -> init_c.initFixVarSizeBitOrOctString     | Ada -> init_a.initFixVarSizeBitOrOctString

    let funcBody (p:CallerScope) v = 
        let bytes = 
            match v with
            | OctetStringValue iv -> iv
            | BitStringValue iv   -> bitStringValueToByteArray (StringLoc.ByValue iv) |> Seq.toList
            | _                 -> raise(BugErrorException "UnexpectedValue")
        let arrsBytes = bytes |> List.mapi(fun i b -> initFixSizeBitOrOctString_bytei p.arg.p (p.arg.getAcces l) ((i+l.ArrayStartIndex).ToString()) (sprintf "%x" b))
        match o.minSize = o.maxSize with
        | true  -> initFixSizeBitOrOctString p.arg.p (p.arg.getAcces l) arrsBytes
        | false -> initFixVarSizeBitOrOctString p.arg.p (p.arg.getAcces l) (BigInteger arrsBytes.Length) arrsBytes
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createNullTypeInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.NullType    ) (typeDefinition:TypeDefintionOrReference) iv = 
    let initNull = match l with C -> init_c.initNull | Ada -> init_a.initNull
    let funcBody (p:CallerScope) v = initNull (p.arg.getValue l) 
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createBitStringInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.BitString   ) (typeDefinition:TypeDefintionOrReference) iv = 
    let initFixSizeBitOrOctString_bytei = match l with C -> init_c.initFixSizeBitOrOctString_bytei  | Ada -> init_a.initFixSizeBitOrOctString_bytei
    let initFixSizeBitOrOctString       = match l with C -> init_c.initFixSizeBitOrOctString        | Ada -> init_a.initFixSizeBitOrOctString
    let initFixVarSizeBitOrOctString    = match l with C -> init_c.initFixVarSizeBitOrOctString     | Ada -> init_a.initFixVarSizeBitOrOctString

    let funcBody (p:CallerScope) v = 
        let bytes = 
            match v with
            | BitStringValue iv     -> bitStringValueToByteArray (StringLoc.ByValue iv) |> Seq.toList
            | OctetStringValue iv   -> iv
            | _                     -> raise(BugErrorException "UnexpectedValue")
        let arrsBytes = bytes |> List.mapi(fun i b -> initFixSizeBitOrOctString_bytei p.arg.p (p.arg.getAcces l) ((i+l.ArrayStartIndex).ToString()) (sprintf "%x" b))
        match o.minSize = o.maxSize with
        | true  -> initFixSizeBitOrOctString p.arg.p (p.arg.getAcces l) arrsBytes
        | false -> initFixVarSizeBitOrOctString p.arg.p (p.arg.getAcces l) (BigInteger arrsBytes.Length) arrsBytes
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createBooleanInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.Boolean     ) (typeDefinition:TypeDefintionOrReference) iv = 
    let initBoolean = match l with C -> init_c.initBoolean | Ada -> init_a.initBoolean
    let funcBody (p:CallerScope) v = 
        let vl = 
            match v with
            | BooleanValue iv   -> iv
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initBoolean (p.arg.getValue l) vl
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createEnumeratedInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.Enumerated  )  (typeDefinition:TypeDefintionOrReference) iv = 
    let initEnumerated = match l with C -> init_c.initEnumerated | Ada -> init_a.initEnumerated
    let funcBody (p:CallerScope) v = 
        let vl = 
            match v with
            | EnumValue iv      -> o.items |> Seq.find(fun x -> x.Name.Value = iv)
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initEnumerated (p.arg.getValue l) (vl.getBackendName (Some typeDefinition) l)
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createSequenceOfInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.SequenceOf  ) (typeDefinition:TypeDefintionOrReference) (childType:Asn1Type) iv = 
    let initFixedSequenceOf = match l with C -> init_c.initFixedSequenceOf | Ada -> init_a.initFixedSequenceOf
    let initVarSizeSequenceOf = match l with C -> init_c.initVarSizeSequenceOf | Ada -> init_a.initVarSizeSequenceOf
    let funcBody (p:CallerScope) v = 
        let vl = 
            match v with
            | SeqOfValue childVals ->
                childVals |> 
                List.mapi(fun i chv -> 
                    let ret = childType.initFunction.initFuncBody ({p with arg = p.arg.getArrayItem l ((i+l.ArrayStartIndex).ToString()) childType.isIA5String}) chv.kind
                    match l with
                    | C     -> ret
                    | Ada   when i>0 -> ret
                    | Ada   -> 
                        // in the first array we have to emit a pragma Annotate false_positive, otherwise gnatprove emit an error
                        let pragma = init_a.initSequence_pragma p.arg.p
                        ret + pragma
                    )
            | _               -> raise(BugErrorException "UnexpectedValue")
        match o.minSize = o.maxSize with
        | true  -> initFixedSequenceOf vl
        | false -> initVarSizeSequenceOf p.arg.p (p.arg.getAcces l) (BigInteger vl.Length) vl
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createSequenceInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.Sequence) (typeDefinition:TypeDefintionOrReference) (children:SeqChildInfo list) iv = 
    let initSequence                = match l with C -> init_c.initSequence | Ada -> init_a.initSequence
    let initSequence_optionalChild  = match l with C -> init_c.initSequence_optionalChild | Ada -> init_a.initSequence_optionalChild
    let funcBody (p:CallerScope) v = 
        let dummy =
            match (typeDefinition.longTypedefName l) = "MyPDU" with
            | true  -> 1
            | false -> 0

        let childrenRet = 
            match v with
            | SeqValue iv     -> 
                children |>
                List.choose(fun seqChild ->
                    match seqChild with
                    | Asn1Child seqChild   ->
                        match iv |> Seq.tryFind(fun chv -> chv.name = seqChild.Name.Value) with
                        | None  ->
                            match seqChild.Optionality with
                            | None      -> None
                            | Some _    -> Some (initSequence_optionalChild p.arg.p (p.arg.getAcces l) seqChild.c_name "0" "")
                        | Some chv  ->
                            let chContent = seqChild.Type.initFunction.initFuncBody ({p with arg = p.arg.getSeqChild l seqChild.c_name seqChild.Type.isIA5String}) chv.Value.kind
                            match seqChild.Optionality with
                            | None      -> Some chContent
                            | Some _    -> Some (initSequence_optionalChild p.arg.p (p.arg.getAcces l) seqChild.c_name "1" chContent)
                    | AcnChild _     -> None)

            | _               -> raise(BugErrorException "UnexpectedValue")
        initSequence childrenRet
    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createChoiceInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.Choice) (typeDefinition:TypeDefintionOrReference) (children:ChChildInfo list) iv =     
    //let initChoice = match l with C -> init_c.initChoice | Ada -> init_a.initChoice

    let funcBody (p:CallerScope) v = 
        let childrenOut = 
            match v with
            | ChValue iv     -> 
                children |> 
                List.choose(fun chChild -> 
                    match chChild.Name.Value = iv.name with
                    | false -> None
                    | true  ->
                        match l with
                        | C ->
                            let chContent = chChild.chType.initFunction.initFuncBody ({p with arg = p.arg.getChChild l chChild.c_name chChild.chType.isIA5String}) iv.Value.kind
                            Some (init_c.initChoice p.arg.p (p.arg.getAcces l) chContent (chChild.presentWhenName (Some typeDefinition) l)) 
                        | Ada ->
                            let sChildTypeName = chChild.chType.typeDefintionOrReference.longTypedefName l
//                                match chChild.chType.inheritInfo with
//                                | Some tasInfo  -> ToC2(r.args.TypePrefix + tasInfo.tasName)
//                                | None          ->
//                                    match chChild.chType.Kind with
//                                    | ReferenceType ref ->     ToC2(r.args.TypePrefix + ref.baseInfo.tasName.Value)
//                                    | _                 ->
//                                        chChild.chType.typeDefinition.typeDefinitionBodyWithinSeq
                            let sChildTempVarName = (ToC chChild.chType.id.AsString) + "_tmp"
                            let sChoiceTypeName = typeDefinition.longTypedefName l
//                                match t.tasInfo with
//                                | Some tasInfo  -> ToC2(r.args.TypePrefix + tasInfo.tasName)
//                                | None          ->
//                                    match chChild.chType.Kind with
//                                    | ReferenceType ref -> ToC2(r.args.TypePrefix + ref.baseInfo.tasName.Value)
//                                    | _                 -> typeDefinition.typeDefinitionBodyWithinSeq
                            let sChildName = chChild.c_name
                            let chContent = chChild.chType.initFunction.initFuncBody ({CallerScope.modName = t.id.ModName; arg = VALUE sChildTempVarName}) iv.Value.kind
                            Some (init_a.initChoice p.arg.p (p.arg.getAcces l) chContent (chChild.presentWhenName (Some typeDefinition) l) sChildTempVarName sChildTypeName sChoiceTypeName sChildName) 
                        ) 

            | _               -> raise(BugErrorException "UnexpectedValue")
        childrenOut |> Seq.head

    createInitFunctionCommon r l t typeDefinition funcBody iv 

let createReferenceType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (t:Asn1AcnAst.Asn1Type) (o :Asn1AcnAst.ReferenceType) (baseType:Asn1Type) =
    baseType.initFunction