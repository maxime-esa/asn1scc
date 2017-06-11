module DAstInitialize
open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open DAst
open DAstUtilFunctions


(*
create c and Ada procedures that initialize an ASN.1 type.
Currently this code is not used since it is no longer required (it was originally written to handle the 'data might not be initialized' errors of spark
However, now with the 'pragma Annotate (GNATprove, False_Positive)' we can handle this case.
*)
let getFuncName (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:Asn1AcnAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.args.TypePrefix + x.tasName + "_Initialize"))

let createInitFunctionCommon (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage)  (o:Asn1AcnAst.Asn1Type) (typeDefinition:TypeDefinitionCommon) funcBody iv =
    let funcName            = getFuncName r l o.tasInfo
    let p = o.getParamType l CommonTypes.Codec.Decode
    let initTypeAssignment = match l with C -> init_c.initTypeAssignment | Ada -> init_a.initTypeAssignment
    let initTypeAssignment_def = match l with C -> init_c.initTypeAssignment_def | Ada -> init_a.initTypeAssignment_def
    let varName = p.p
    let sStar = p.getStar l

    let  func  = 
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let content = funcBody p iv
                Some(initTypeAssignment varName sStar funcName  typeDefinition.name content )
    let  funcDef  = 
            match funcName with
            | None              -> None
            | Some funcName     -> 
                Some(initTypeAssignment_def varName sStar funcName  typeDefinition.name)


    {
        initFuncName            = funcName
        initFunc                = func
        initFuncDef             = funcDef
        initFuncBody            = funcBody
    }

let createIntegerInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o:Asn1AcnAst.Integer) (typeDefinition:TypeDefinitionCommon) iv =
    let initInteger = match l with C -> init_c.initInteger | Ada -> init_a.initInteger
    let funcBody (p:FuncParamType) v = 
        let vl = 
            match v with
            | IntegerValue iv   -> iv.Value
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initInteger (p.getValue l) vl
    createInitFunctionCommon r l (Asn1AcnAst.Integer o) typeDefinition funcBody iv 

let createRealInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.Real) (typeDefinition:TypeDefinitionCommon) iv = 
    let initReal = match l with C -> init_c.initReal | Ada -> init_a.initReal
    let funcBody (p:FuncParamType) v = 
        let vl = 
            match v with
            | RealValue iv   -> iv.Value
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initReal (p.getValue l) vl
    createInitFunctionCommon r l (Asn1AcnAst.Real o) typeDefinition funcBody iv 

let createIA5StringInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.StringType   ) (typeDefinition:TypeDefinitionCommon) iv = 
    let initIA5String = match l with C -> init_c.initIA5String | Ada -> init_a.initIA5String
    let funcBody (p:FuncParamType) v = 
        let vl = 
            match v with
            | StringValue iv   -> 
                iv.Value
            | _                 -> raise(BugErrorException "UnexpectedValue")
        let arrNuls = [0 .. (o.maxSize- vl.Length)]|>Seq.map(fun x -> variables_a.PrintStringValueNull())
        initIA5String (p.getPointer l) (vl.Replace("\"","\"\"")) arrNuls
    createInitFunctionCommon r l (Asn1AcnAst.IA5String o) typeDefinition funcBody iv 

let createOctetStringInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.OctetString ) (typeDefinition:TypeDefinitionCommon) iv = 
    let initFixSizeBitOrOctString_bytei = match l with C -> init_c.initFixSizeBitOrOctString_bytei  | Ada -> init_a.initFixSizeBitOrOctString_bytei
    let initFixSizeBitOrOctString       = match l with C -> init_c.initFixSizeBitOrOctString        | Ada -> init_a.initFixSizeBitOrOctString
    let initFixVarSizeBitOrOctString    = match l with C -> init_c.initFixVarSizeBitOrOctString     | Ada -> init_a.initFixVarSizeBitOrOctString

    let funcBody (p:FuncParamType) v = 
        let bytes = 
            match v with
            | OctetStringValue iv -> iv.Value 
            | BitStringValue iv   -> bitStringValueToByteArray (StringLoc.ByValue iv.Value) |> Seq.toList
            | _                 -> raise(BugErrorException "UnexpectedValue")
        let arrsBytes = bytes |> List.mapi(fun i b -> initFixSizeBitOrOctString_bytei p.p (p.getAcces l) ((i+l.ArrayStartIndex).ToString()) (sprintf "%x" b))
        match o.minSize = o.maxSize with
        | true  -> initFixSizeBitOrOctString p.p (p.getAcces l) arrsBytes
        | false -> initFixVarSizeBitOrOctString p.p (p.getAcces l) (BigInteger arrsBytes.Length) arrsBytes
    createInitFunctionCommon r l (Asn1AcnAst.OctetString o) typeDefinition funcBody iv 

let createNullTypeInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.NullType    ) (typeDefinition:TypeDefinitionCommon) iv = 
    let initNull = match l with C -> init_c.initNull | Ada -> init_a.initNull
    let funcBody (p:FuncParamType) v = initNull (p.getValue l) 
    createInitFunctionCommon r l (Asn1AcnAst.NullType o) typeDefinition funcBody iv 

let createBitStringInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.BitString   ) (typeDefinition:TypeDefinitionCommon) iv = 
    let initFixSizeBitOrOctString_bytei = match l with C -> init_c.initFixSizeBitOrOctString_bytei  | Ada -> init_a.initFixSizeBitOrOctString_bytei
    let initFixSizeBitOrOctString       = match l with C -> init_c.initFixSizeBitOrOctString        | Ada -> init_a.initFixSizeBitOrOctString
    let initFixVarSizeBitOrOctString    = match l with C -> init_c.initFixVarSizeBitOrOctString     | Ada -> init_a.initFixVarSizeBitOrOctString

    let funcBody (p:FuncParamType) v = 
        let bytes = 
            match v with
            | BitStringValue iv     -> bitStringValueToByteArray (StringLoc.ByValue iv.Value) |> Seq.toList
            | OctetStringValue iv   -> iv.Value
            | _                     -> raise(BugErrorException "UnexpectedValue")
        let arrsBytes = bytes |> List.mapi(fun i b -> initFixSizeBitOrOctString_bytei p.p (p.getAcces l) ((i+l.ArrayStartIndex).ToString()) (sprintf "%x" b))
        match o.minSize = o.maxSize with
        | true  -> initFixSizeBitOrOctString p.p (p.getAcces l) arrsBytes
        | false -> initFixVarSizeBitOrOctString p.p (p.getAcces l) (BigInteger arrsBytes.Length) arrsBytes
    createInitFunctionCommon r l (Asn1AcnAst.BitString o) typeDefinition funcBody iv 

let createBooleanInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.Boolean     ) (typeDefinition:TypeDefinitionCommon) iv = 
    let initBoolean = match l with C -> init_c.initBoolean | Ada -> init_a.initBoolean
    let funcBody (p:FuncParamType) v = 
        let vl = 
            match v with
            | BooleanValue iv   -> iv.Value
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initBoolean (p.getValue l) vl
    createInitFunctionCommon r l (Asn1AcnAst.Boolean o) typeDefinition funcBody iv 

let createEnumeratedInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.Enumerated  ) (typeDefinition:TypeDefinitionCommon) iv = 
    let initEnumerated = match l with C -> init_c.initEnumerated | Ada -> init_a.initEnumerated
    let funcBody (p:FuncParamType) v = 
        let vl = 
            match v with
            | EnumValue iv      -> o.items |> Seq.find(fun x -> x.name = iv.Value)
            | _                 -> raise(BugErrorException "UnexpectedValue")
        initEnumerated (p.getValue l) (vl.getBackendName l)
    createInitFunctionCommon r l (Asn1AcnAst.Enumerated o) typeDefinition funcBody iv 

let createSequenceOfInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.SequenceOf  ) (typeDefinition:TypeDefinitionCommon) (childType:Asn1Type) iv = 
    let initFixedSequenceOf = match l with C -> init_c.initFixedSequenceOf | Ada -> init_a.initFixedSequenceOf
    let initVarSizeSequenceOf = match l with C -> init_c.initVarSizeSequenceOf | Ada -> init_a.initVarSizeSequenceOf
    let funcBody (p:FuncParamType) v = 
        let vl = 
            match v with
            | SeqOfValue iv     -> 
                iv.Value |> 
                List.mapi(fun i chv -> 
                    let ret = childType.initFunction.initFuncBody (p.getArrayItem l ((i+l.ArrayStartIndex).ToString()) childType.isIA5String) chv
                    match l with
                    | C     -> ret
                    | Ada   when i>0 -> ret
                    | Ada   -> 
                        // in the first array we have to emit a pragma Annotate false_positive, otherwise gnatprove emit an error
                        let pragma = init_a.initSequence_pragma p.p
                        ret + pragma
                    )
            | _                 -> raise(BugErrorException "UnexpectedValue")
        match o.minSize = o.maxSize with
        | true  -> initFixedSequenceOf vl
        | false -> initVarSizeSequenceOf p.p (p.getAcces l) (BigInteger vl.Length) vl
    createInitFunctionCommon r l (Asn1AcnAst.SequenceOf o) typeDefinition funcBody iv 

let createSequenceInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.Sequence) (typeDefinition:TypeDefinitionCommon) (children:SeqChildInfo list) iv = 
    let initSequence                = match l with C -> init_c.initSequence | Ada -> init_a.initSequence
    let initSequence_optionalChild  = match l with C -> init_c.initSequence_optionalChild | Ada -> init_a.initSequence_optionalChild
    let funcBody (p:FuncParamType) v = 
        let childrenRet = 
            match v with
            | SeqValue iv     -> 
                children |>
                List.choose(fun seqChild ->
                    match iv.Value |> Seq.tryFind(fun chv -> chv.name = seqChild.name) with
                    | None  ->
                        match seqChild.optionality with
                        | None      -> None
                        | Some _    -> Some (initSequence_optionalChild p.p (p.getAcces l) seqChild.c_name "0" "")
                    | Some chv  ->
                        let chContent = seqChild.chType.initFunction.initFuncBody (p.getSeqChild l seqChild.c_name seqChild.chType.isIA5String) chv.Value
                        match seqChild.optionality with
                        | None      -> Some chContent
                        | Some _    -> Some (initSequence_optionalChild p.p (p.getAcces l) seqChild.c_name "1" chContent))
            | _               -> raise(BugErrorException "UnexpectedValue")
        initSequence childrenRet
    createInitFunctionCommon r l (Asn1AcnAst.Sequence o) typeDefinition funcBody iv 

let createChoiceInitFunc (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (o :Asn1AcnAst.Choice) (typeDefinition:TypeDefinitionCommon) (children:ChChildInfo list) iv =     
    //let initChoice = match l with C -> init_c.initChoice | Ada -> init_a.initChoice
    let funcBody (p:FuncParamType) v = 
        let children = 
            match v with
            | ChValue iv     -> 
                children |> 
                List.choose(fun chChild -> 
                    match chChild.name = iv.Value.name with
                    | false -> None
                    | true  ->
                        match l with
                        | C ->
                            let chContent = chChild.chType.initFunction.initFuncBody (p.getChChild l chChild.c_name chChild.chType.isIA5String) iv.Value.Value
                            Some (init_c.initChoice p.p (p.getAcces l) chContent chChild.presentWhenName) 
                        | Ada ->
                            let sChildTempVarName = chChild.chType.typeDefinition.name.L1 + "_tmp"
                            let sChildTypeName = chChild.chType.typeDefinition.typeDefinitionBodyWithinSeq
                            let sChoiceTypeName = typeDefinition.name
                            let sChildName = chChild.c_name
                            let chContent = chChild.chType.initFunction.initFuncBody (VALUE sChildTempVarName) iv.Value.Value
                            Some (init_a.initChoice p.p (p.getAcces l) chContent chChild.presentWhenName sChildTempVarName sChildTypeName sChoiceTypeName sChildName) 
                        ) 

            | _               -> raise(BugErrorException "UnexpectedValue")
        children |> Seq.head

    createInitFunctionCommon r l (Asn1AcnAst.Choice o) typeDefinition funcBody iv 
