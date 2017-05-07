module DAstUPer
open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open Constraints
open DAst

let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + codec.suffix))

let callBaseTypeFunc l = match l with C -> uper_c.call_base_type_func | Ada -> uper_a.call_base_type_func

//TODO
//1.Decode functions (and perhaps encode function) muct check if the decode value is within the constraints (currently, implemented only for Integers and for case IntUnconstraintMax )


let createPrimitiveFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Asn1Type) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option)  (funcBody:ErroCode->FuncParamType-> (string option)) localVars childErrCodes soSparkAnnotations (us:State)  =
    let funcName            = getFuncName r l codec o.tasInfo
    let errCodeName         = ToC ("ERR_UPER" + (codec.suffix.ToUpper()) + "_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let EmitTypeAssignment_primitive = match l with C -> uper_c.EmitTypeAssignment_primitive    | Ada -> uper_a.EmitTypeAssignment
    let EmitTypeAssignment_primitive_def = match l with C -> uper_c.EmitTypeAssignment_primitive_def    | Ada -> uper_a.EmitTypeAssignment_def
    let EmitTypeAssignment_def_err_code  = match l with C -> uper_c.EmitTypeAssignment_def_err_code    | Ada -> uper_a.EmitTypeAssignment_def_err_code

    let funcBody = (funcBody errCode)
    let p = o.getParamType l codec
    let topLevAcc = p.getAcces l
    let varName = p.p
    let sStar = p.getStar l
    let isValidFuncName = match isValidFunc with None -> None | Some f -> f.funcName
    let sInitilialExp = ""
    let errCodes = errCode::childErrCodes
    let  func  = 
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let content = funcBody p  
                match content with 
                | None          -> None
                | Some content  ->
                    let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                    Some(EmitTypeAssignment_primitive varName sStar funcName isValidFuncName  typeDefinition.name lvars  content soSparkAnnotations sInitilialExp codec)
    let  funcDef  = 
            match funcName with
            | None              -> None
            | Some funcName     -> 
                match func with
                | None      -> None
                | Some _    ->
                    let errCodStr = errCodes |> List.map(fun x -> (EmitTypeAssignment_def_err_code x.errCodeName) (BigInteger x.errCodeValue))
                    Some(EmitTypeAssignment_primitive_def varName sStar funcName  typeDefinition.name errCodStr (o.uperMaxSizeInBits = 0) (BigInteger (ceil ((double o.uperMaxSizeInBits)/8.0))) (BigInteger o.uperMaxSizeInBits) codec)


    let ret = 
        {
            UPerFunction.errCodes      = errCodes      
            funcName                   = funcName
            func                       = func 
            funcDef                    = funcDef
            funcBody                   = funcBody
            localVariables             = localVars
        }
    ret, {us with currErrCode = us.currErrCode + 1}



let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with Ast.Encode -> p.getValue l | Ast.Decode -> p.getPointer l
        let IntNoneRequired         = match l with C -> uper_c.IntNoneRequired          | Ada -> (fun p min   errCode codec -> uper_a.IntFullyConstraint p min min 0I errCode codec)
        let IntFullyConstraintPos   = match l with C -> uper_c.IntFullyConstraintPos    | Ada -> uper_a.IntFullyConstraint
        let IntFullyConstraint      = match l with C -> uper_c.IntFullyConstraint       | Ada -> uper_a.IntFullyConstraint
        let IntSemiConstraintPos    = match l with C -> uper_c.IntSemiConstraintPos     | Ada -> uper_a.IntSemiConstraint
        let IntSemiConstraint       = match l with C -> uper_c.IntSemiConstraint        | Ada -> uper_a.IntSemiConstraint
        let IntUnconstraint         = match l with C -> uper_c.IntUnconstraint          | Ada -> uper_a.IntUnconstraint
        let IntUnconstraintMax      = match l with C -> uper_c.IntUnconstraintMax       | Ada -> uper_a.IntUnconstraintMax
        let IntRootExt              = match l with C -> uper_c.IntRootExt               | Ada -> uper_a.IntRootExt
        let IntRootExt2             = match l with C -> uper_c.IntRootExt2              | Ada -> uper_a.IntRootExt2
        let rootCons = o.Cons |> List.choose(fun x -> match x with RangeRootConstraint(a) |RangeRootConstraint2(a,_) -> Some(x) |_ -> None) 
        let checkExp = 
            match isValidFunc with
            | None  ->  None
            | Some fnc -> 
                match fnc.funcExp with
                | None  -> None
                | Some expFunc -> (Some (expFunc (p.getValue l)))
        let IntBod uperRange extCon =
            match uperRange with
            | uPER2.Concrete(min, max) when min=max                    -> IntNoneRequired pp min   errCode.errCodeName codec 
            | uPER2.Concrete(min, max) when min>=0I && (not extCon)    -> IntFullyConstraintPos pp min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode.errCodeName codec
            | uPER2.Concrete(min, max)                                 -> IntFullyConstraint pp min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode.errCodeName codec
            | uPER2.PosInf(a)  when a>=0I && (not extCon)  -> IntSemiConstraintPos pp a  errCode.errCodeName codec
            | uPER2.PosInf(a)               -> IntSemiConstraint pp a  errCode.errCodeName codec
            | uPER2.NegInf(max)             -> IntUnconstraintMax pp max checkExp errCode.errCodeName codec
            | uPER2.Full                    -> IntUnconstraint pp errCode.errCodeName codec

        let getValueByConstraint uperRange =
            match uperRange with
            | uPER2.Concrete(a, _)  -> a
            | uPER2.PosInf(a)       -> a
            | uPER2.NegInf(b)       -> b
            | uPER2.Full            -> 0I

        match rootCons with
        | []                            -> IntBod o.uperRange false
        | (RangeRootConstraint a)::rest      -> 
            let uperR    = uPER2.getIntTypeConstraintUperRange [a]  o.Location
            let cc = DAstValidate.foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString()) (p.getValue l) a
            IntRootExt pp (getValueByConstraint uperR) cc (IntBod uperR true) errCode.errCodeName codec
        | (RangeRootConstraint2(a,_))::rest  -> 
            let uperR    = uPER2.getIntTypeConstraintUperRange [a]  o.Location
            let cc = DAstValidate.foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString()) (p.getValue l) a
            IntRootExt2 pp (getValueByConstraint uperR) cc (IntBod uperR true) errCode.errCodeName codec 
        | _                             -> raise(BugErrorException "")
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Integer o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) [] []  soSparkAnnotations us


let createBooleanFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with Ast.Encode -> p.getValue l | Ast.Decode -> p.getPointer l
        let Boolean         = match l with C -> uper_c.Boolean          | Ada -> uper_a.Boolean
        Boolean pp errCode.errCodeName codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Boolean o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) [] [] soSparkAnnotations us

let createRealFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with Ast.Encode -> p.getValue l | Ast.Decode -> p.getPointer l
        let Real         = match l with C -> uper_c.Real          | Ada -> uper_a.Real
        Real pp errCode.errCodeName codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Real o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) [] [] soSparkAnnotations us

let createNullTypeFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.NullType) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.NullType o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> None) [] [] soSparkAnnotations us


let createEnumeratedFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with Ast.Encode -> p.getValue l | Ast.Decode -> p.getPointer l
        let Enumerated         = match l with C -> uper_c.Enumerated          | Ada -> uper_a.Enumerated
        let Enumerated_item    = match l with C -> uper_c.Enumerated_item          | Ada -> uper_a.Enumerated_item
        
        let nMin = 0I
        let nMax = BigInteger(Seq.length o.items) - 1I
        let nLastItemIndex      = nMax
        let items = 
            o.items |> List.mapi(fun i itm -> Enumerated_item (p.getValue l) (itm.getBackendName l) (BigInteger i) nLastItemIndex codec) 
        let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
        let sFirstItemName = o.items.Head.getBackendName l
        Enumerated (p.getValue l) typeDefinition.name items nMin nMax nBits errCode.errCodeName nLastItemIndex sFirstItemName codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Enumerated o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) [] [] soSparkAnnotations us


let createIA5StringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.StringType) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
    let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
    let charIndex =
        match l with
        | C     -> []
        | Ada   -> [IntegerLocalVariable ("charIndex", None)]
    let nStringLength =
        match o.minSize = o.maxSize with
        | true  -> []
        | false ->
            match l with
            | Ada  -> [IntegerLocalVariable ("nStringLength", None)]
            | C    -> [Asn1SIntLocalVariable ("nStringLength", None)]
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let InternalItem_string_no_alpha = match l with C -> uper_c.InternalItem_string_no_alpha        | Ada -> uper_a.InternalItem_string_no_alpha
        let InternalItem_string_with_alpha = match l with C -> uper_c.InternalItem_string_with_alpha        | Ada -> uper_a.InternalItem_string_with_alpha
        let str_FixedSize       = match l with C -> uper_c.str_FixedSize        | Ada -> uper_a.str_FixedSize
        let str_VarSize         = match l with C -> uper_c.str_VarSize          | Ada -> uper_a.str_VarSize
        //let Fragmentation_sqf   = match l with C -> uper_c.Fragmentation_sqf    | Ada -> uper_a.Fragmentation_sqf

        let nBits = GetNumberOfBitsForNonNegativeInteger (BigInteger (o.charSet.Length-1))
        let internalItem =
            match o.charSet.Length = 128 with
            | true  -> InternalItem_string_no_alpha p.p i  codec 
            | false -> 
                let nBits = GetNumberOfBitsForNonNegativeInteger (BigInteger (o.charSet.Length-1))
                let arrAsciiCodes = o.charSet |> Array.map(fun x -> BigInteger (System.Convert.ToInt32 x))
                InternalItem_string_with_alpha p.p typeDefinition.name i (BigInteger (o.charSet.Length-1)) arrAsciiCodes (BigInteger (o.charSet.Length)) nBits  codec
        let nSizeInBits = GetNumberOfBitsForNonNegativeInteger (BigInteger (o.maxSize - o.minSize))
        match o.minSize with
        | _ when o.maxSize < 65536 && o.maxSize=o.minSize  -> str_FixedSize p.p typeDefinition.name i internalItem (BigInteger o.minSize) nBits nBits 0I codec 
        | _ when o.maxSize < 65536 && o.maxSize<>o.minSize  -> str_VarSize p.p typeDefinition.name i internalItem (BigInteger o.minSize) (BigInteger o.maxSize) nSizeInBits nBits nBits 0I codec 
        | _                                                -> raise(Exception "fragmentation not implemented yet")
    let soSparkAnnotations = 
        match l with
        | C     -> None
        | Ada   ->
            Some(uper_a.annotations typeDefinition.name true isValidFunc.IsSome true true codec)
    createPrimitiveFunction r l codec (CAst.IA5String o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) (lv::charIndex@nStringLength) [] soSparkAnnotations  us

let createOctetStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.OctetString) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
    let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
    let nStringLength =
        match o.minSize = o.maxSize with
        | true  -> []
        | false ->
            match l with
            | Ada  -> [IntegerLocalVariable ("nStringLength", None)]
            | C    -> [Asn1SIntLocalVariable ("nCount", None)]
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let InternalItem_oct_str = match l with C -> uper_c.InternalItem_oct_str        | Ada -> uper_a.InternalItem_oct_str
        let fixedSize       = match l with C -> uper_c.octect_FixedSize        | Ada -> uper_a.octect_FixedSize
        let varSize         = match l with C -> uper_c.octect_VarSize          | Ada -> uper_a.octect_VarSize

        let nBits = 8I
        let internalItem = InternalItem_oct_str p.p (p.getAcces l) i  errCode.errCodeName codec 
        let nSizeInBits = GetNumberOfBitsForNonNegativeInteger (BigInteger (o.maxSize - o.minSize))
        match o.minSize with
        | _ when o.maxSize < 65536 && o.maxSize=o.minSize  ->  fixedSize p.p typeDefinition.name i internalItem (BigInteger o.minSize) nBits nBits 0I codec 
        | _ when o.maxSize < 65536 && o.maxSize<>o.minSize  -> varSize p.p (p.getAcces l)  typeDefinition.name i internalItem (BigInteger o.minSize) (BigInteger o.maxSize) nSizeInBits nBits nBits 0I errCode.errCodeName codec 
        | _                                                -> raise(Exception "fragmentation not implemented yet")
    let soSparkAnnotations = 
        match l with
        | C     -> None
        | Ada   ->
            Some(uper_a.annotations typeDefinition.name true isValidFunc.IsSome true true codec)
    createPrimitiveFunction r l codec (CAst.OctetString o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) (lv::nStringLength) [] soSparkAnnotations  us

let createBitStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.BitString) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
    let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
    let nStringLength =
        match o.minSize = o.maxSize with
        | true  -> []
        | false ->
            match l with
            | Ada  -> [IntegerLocalVariable ("nStringLength", None)]
            | C    -> [Asn1SIntLocalVariable ("nCount", None)]
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        match l with
        | Ada ->
            let nBits = 1I
            let internalItem = uper_a.InternalItem_bit_str p.p i  errCode.errCodeName codec 
            let nSizeInBits = GetNumberOfBitsForNonNegativeInteger (BigInteger (o.maxSize - o.minSize))
            match o.minSize with
            | _ when o.maxSize < 65536 && o.maxSize=o.minSize  -> uper_a.octect_FixedSize p.p typeDefinition.name i internalItem (BigInteger o.minSize) nBits nBits 0I codec 
            | _ when o.maxSize < 65536 && o.maxSize<>o.minSize -> uper_a.octect_VarSize p.p (p.getAcces l)  typeDefinition.name i internalItem (BigInteger o.minSize) (BigInteger o.maxSize) nSizeInBits nBits nBits 0I errCode.errCodeName codec 
            | _                                                -> raise(Exception "fragmentation not implemented yet")
        | C ->
            match o.minSize with
            | _ when o.maxSize < 65536 && o.maxSize=o.minSize   -> uper_c.bitString_FixSize p.p (p.getAcces l) (BigInteger o.minSize) errCode.errCodeName codec 
            | _ when o.maxSize < 65536 && o.maxSize<>o.minSize  -> uper_c.bitString_VarSize p.p (p.getAcces l) (BigInteger o.minSize) (BigInteger o.maxSize) errCode.errCodeName codec 
            | _                                                -> raise(Exception "fragmentation not implemented yet")
    let soSparkAnnotations = 
        match l with
        | C     -> None
        | Ada   -> Some(uper_a.annotations typeDefinition.name true isValidFunc.IsSome true true codec)
    createPrimitiveFunction r l codec (CAst.BitString o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) (lv::nStringLength) [] soSparkAnnotations  us



let createSequenceOfFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.SequenceOf) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (child:Asn1Type) (us:State)  =
    let localVariables = [child] |> List.choose(fun x -> x.getUperFunction codec) |> List.collect(fun x -> x.localVariables)
    let childErrCodes =  [child]|> List.choose(fun x -> x.getUperFunction codec) |> List.collect(fun x -> x.errCodes)
    let nStringLength =
        match o.minSize = o.maxSize with
        | true  -> []
        | false ->
            match l with
            | Ada  -> [IntegerLocalVariable ("nStringLength", None)]
            | C    -> [Asn1SIntLocalVariable ("nCount", None)]
    let baseFuncName =  match baseTypeUperFunc  with None -> None | Some baseFunc -> baseFunc.funcName
    let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
    let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        match baseFuncName with
        | None ->
            let fixedSize       = match l with C -> uper_c.octect_FixedSize        | Ada -> uper_a.octect_FixedSize
            let varSize         = match l with C -> uper_c.octect_VarSize          | Ada -> uper_a.octect_VarSize

            let chFunc = child.getUperFunction codec
            let internalItem = 
                match chFunc with
                | None  -> None
                | Some chFunc ->chFunc.funcBody (p.getArrayItem l i child.isIA5String)
            match internalItem with
            | None  -> 
                    match o.minSize with
                    | _ when o.maxSize < 65536 && o.maxSize=o.minSize  -> None
                    | _ when o.maxSize < 65536 && o.maxSize<>o.minSize -> Some "Encode only length"
                    | _                                                -> raise(Exception "fragmentation not implemented yet")
            | Some internalItem -> 
                let nSizeInBits = GetNumberOfBitsForNonNegativeInteger (BigInteger (o.maxSize - o.minSize))
                let ret = 
                    match o.minSize with
                    | _ when o.maxSize < 65536 && o.maxSize=o.minSize  -> fixedSize p.p typeDefinition.name i internalItem (BigInteger o.minSize) (BigInteger child.uperMinSizeInBits) (BigInteger child.uperMaxSizeInBits) 0I codec 
                    | _ when o.maxSize < 65536 && o.maxSize<>o.minSize  -> varSize p.p (p.getAcces l)  typeDefinition.name i internalItem (BigInteger o.minSize) (BigInteger o.maxSize) nSizeInBits (BigInteger child.uperMinSizeInBits) (BigInteger child.uperMaxSizeInBits) 0I errCode.errCodeName codec 
                    | _                                                -> raise(Exception "fragmentation not implemented yet")
                Some ret
        | Some baseFuncName ->
            Some (callBaseTypeFunc l (p.getPointer l) baseFuncName codec)
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.SequenceOf o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody (lv::(nStringLength@localVariables)) childErrCodes soSparkAnnotations  us


let nestChildItems (l:ProgrammingLanguage) (codec:Ast.Codec) children = 
    let printChild (content:string) (sNestedContent:string option) = 
        match sNestedContent with
        | None  -> content
        | Some c-> 
            match l with
            | C        -> equal_c.JoinItems content sNestedContent
            | Ada      -> uper_a.JoinItems content sNestedContent
    let rec printChildren children : Option<string> = 
        match children with
        |[]     -> None
        |x::xs  -> 
            match printChildren xs with
            | None                 -> Some (printChild x  None)
            | Some childrenCont    -> Some (printChild x  (Some childrenCont))
    printChildren children

let createSequenceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Sequence) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (children:SeqChildInfo list) (us:State)  =
    // stg macros
    let sequence_presence_bit       = match l with C -> uper_c.sequence_presence_bit        | Ada -> uper_a.sequence_presence_bit
    let sequence_presence_bit_fix   = match l with C -> uper_c.sequence_presence_bit_fix    | Ada -> uper_a.sequence_presence_bit_fix
    let sequence_mandatory_child    = match l with C -> uper_c.sequence_mandatory_child     | Ada -> uper_a.sequence_mandatory_child
    let sequence_optional_child     = match l with C -> uper_c.sequence_optional_child      | Ada -> uper_a.sequence_optional_child
    let sequence_default_child      = match l with C -> uper_c.sequence_default_child       | Ada -> uper_a.sequence_default_child
    let baseFuncName =  match baseTypeUperFunc  with None -> None | Some baseFunc -> baseFunc.funcName

    let nonAcnChildren = children |> List.filter(fun c -> not c.acnInsertetField)
    let localVariables = nonAcnChildren |> List.choose(fun x -> x.chType.getUperFunction codec) |> List.collect(fun x -> x.localVariables)
    let localVariables =
        match nonAcnChildren |> Seq.exists(fun x -> x.optionality.IsSome) with
        | true  when l = C  && codec = Ast.Decode -> (FlagLocalVariable ("presenceBit", None))::localVariables
        | _                                       -> localVariables
        
    let childErrCodes = nonAcnChildren |> List.choose(fun x -> x.chType.getUperFunction codec) |> List.collect(fun x -> x.errCodes)
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        match baseFuncName with
        | None ->
            let printPresenceBit (child:SeqChildInfo) =
                match child.optionality with
                | None                       -> None
                | Some CAst.AlwaysAbsent     -> Some (sequence_presence_bit_fix p.p (p.getAcces l) child.c_name "0" errCode.errCodeName codec)    // please note that in decode, macro uper_sequence_presence_bit_fix
                | Some CAst.AlwaysPresent    -> Some (sequence_presence_bit_fix p.p (p.getAcces l) child.c_name "1" errCode.errCodeName codec)    // calls macro uper_sequence_presence_bit (i.e. behaves like optional)
                | Some (CAst.Optional opt)   -> Some (sequence_presence_bit p.p (p.getAcces l) child.c_name  errCode.errCodeName codec)
            let printChild (child:SeqChildInfo) =
                let chFunc = child.chType.getUperFunction codec
                match chFunc with
                | None  -> None
                | Some chFunc ->
                    let childContent = chFunc.funcBody (p.getSeqChild l child.c_name child.chType.isIA5String)
                    match childContent with
                    | None              -> None
                    | Some childContent ->
                        match child.optionality with
                        | None                       -> Some (sequence_mandatory_child child.c_name childContent codec) 
                        | Some CAst.AlwaysAbsent     -> match codec with Ast.Encode -> None               | Ast.Decode -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent codec) 
                        | Some CAst.AlwaysPresent    -> match codec with Ast.Encode -> Some childContent  | Ast.Decode -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent codec)
                        | Some (CAst.Optional opt)   -> 
                            match opt.defaultValue with
                            | None                   -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent codec)
                            | Some v                 -> 
                                let defInit= child.chType.initFunction.initFuncBody (p.getSeqChild l child.c_name child.chType.isIA5String) v
                                Some (sequence_default_child p.p (p.getAcces l) child.c_name childContent defInit codec) 
            let presenseBits = nonAcnChildren |> List.choose printPresenceBit
            let childrenStatements = nonAcnChildren |> List.choose printChild
            (presenseBits@childrenStatements) |> nestChildItems l codec 
        | Some baseFuncName ->
            Some (callBaseTypeFunc l (p.getPointer l) baseFuncName codec)
            
    let soSparkAnnotations = 
        match l with
        | C     -> None
        | Ada   -> None
    createPrimitiveFunction r l codec (CAst.Sequence o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody localVariables childErrCodes soSparkAnnotations  us



let createChoiceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Choice) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (children:ChChildInfo list) (us:State)  =
    // stg macros
    let choice_child       = match l with C -> uper_c.choice_child | Ada -> uper_c.choice_child
    let choice   = match l with C -> uper_c.choice | Ada -> uper_c.choice

    let childErrCodes = children |> List.choose(fun x -> x.chType.getUperFunction codec) |> List.collect(fun x -> x.errCodes)
    let baseFuncName =  match baseTypeUperFunc  with None -> None | Some baseFunc -> baseFunc.funcName
    
    let localVariables = children |> List.choose(fun x -> x.chType.getUperFunction codec) |> List.collect(fun x -> x.localVariables)
    let sChoiceIndexName = typeDefinition.name + "_index_tmp"
    let localVariables =
        match codec with
        | Ast.Encode  -> localVariables
        | Ast.Decode  -> (Asn1SIntLocalVariable (sChoiceIndexName, None))::localVariables


    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        match baseFuncName with
        | None ->
            let childrenContent =
                children |> 
                List.mapi(fun i child ->
                    let chFunc = child.chType.getUperFunction codec
                    match chFunc with
                    | None  -> ""
                    | Some chFunc ->
                        let childContent = 
                            match chFunc.funcBody (p.getChChild l child.c_name child.chType.isIA5String) with
                            | None              -> "/*no encoding/decoding is required*/"
                            | Some childContent -> childContent
                        choice_child p.p (p.getAcces l) child.presentWhenName (BigInteger i) (BigInteger (children.Length - 1)) childContent codec)
            Some (choice p.p (p.getAcces l) childrenContent (BigInteger (children.Length - 1)) sChoiceIndexName errCode.errCodeName codec) 
        | Some baseFuncName ->
            Some (callBaseTypeFunc l (p.getPointer l) baseFuncName codec)

    let soSparkAnnotations = None

    createPrimitiveFunction r l codec (CAst.Choice o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody localVariables childErrCodes soSparkAnnotations  us
