module DAstValidate

open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open Constraints
open DAst

// TODO
// 1 single value constraints for composite types (SEQUENCE, SEQUENCE OF, CHOICE) by using the generated value and _equal function (like bit and octet strings)
// 2 simpify constraints. For example the constrains of the following type
// INT20 ::= INTEGER(-11..10 | 23 | 24)(1..20 EXCEPT 100)
// should be recalcualted as 
//   uPerRange is 1..10
// so the following simplifications must be performed
//    INT20 ::= INTEGER(1..10)(1..10)
// othwerwise the generated will have warnings



let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.args.TypePrefix + x.tasName + "_IsConstraintValid"))

let Lte (l:ProgrammingLanguage) eqIsInc  e1 e2 =
    match eqIsInc with
    | true   -> l.ExpLte e1 e2        
    | false  -> l.ExpLt  e1 e2

let foldGenericCon (l:ProgrammingLanguage) valToStrFunc  (p:String)  (c:GenericConstraint<'v>)  =
    foldGenericConstraint
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpEqual p (valToStrFunc v) ,s)
        c
        0 |> fst

let foldRangeCon (l:ProgrammingLanguage) valToStrFunc1 valToStrFunc2 (p:String)  (c:RangeTypeConstraint<'v1,'v2>)  =
    foldRangeTypeConstraint        
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpEqual p (valToStrFunc2 v) ,s)
        (fun v1 v2  minIsIn maxIsIn s   -> 
            l.ExpAnd (Lte l minIsIn (valToStrFunc1 v1) p) (Lte l maxIsIn p (valToStrFunc1 v2)), s)
        (fun v1 minIsIn s   -> Lte l minIsIn (valToStrFunc1 v1) p, s)
        (fun v2 maxIsIn s   -> Lte l maxIsIn p (valToStrFunc1 v2), s)
        c
        0 |> fst



let foldSizeRangeTypeConstraint (l:ProgrammingLanguage)  getSizeFunc (p:String) (c:PosIntTypeConstraint) = 
    foldRangeTypeConstraint        
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpEqual (getSizeFunc l p) (v.ToString()) ,s)
        (fun v1 v2  minIsIn maxIsIn s   -> 
            l.ExpAnd (Lte l minIsIn (v1.ToString()) (getSizeFunc l p)) (Lte l maxIsIn (getSizeFunc l p) (v2.ToString())), s)
        (fun v1 minIsIn s   -> Lte l minIsIn (v1.ToString()) (getSizeFunc l p), s)
        (fun v2 maxIsIn s   -> Lte l maxIsIn (getSizeFunc l p) (v2.ToString()), s)
        c
        0 


let foldSizableConstraint (l:ProgrammingLanguage) compareSingValueFunc  getSizeFunc (p:String) (c:SizableTypeConstraint<'v>) =
    foldSizableTypeConstraint2
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> (compareSingValueFunc p v) ,s)
        (fun intCon s       -> foldSizeRangeTypeConstraint l getSizeFunc p intCon)
        c
        0 |> fst



let foldStringCon (l:ProgrammingLanguage) alphaFuncName (p:String)  (c:IA5StringConstraint)  =
    foldStringTypeConstraint2
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpStringEqual p v.IDQ ,s)
        (fun intCon s       -> foldSizeRangeTypeConstraint l (fun l p -> l.StrLen p) p intCon)
        (fun alphcon s      -> sprintf "%s(%s)" alphaFuncName p,s) 
        c
        0 |> fst

let baseFuncName (baseTypeValFunc : IsValidFunction option) = 
    match baseTypeValFunc with
    | Some bsFunc   -> bsFunc.funcName 
    | None          -> None
let hasValidationFunc allCons baseFuncName =
    match allCons, baseFuncName with
    | [], None      -> false
    | _             -> true

let makeExpressionToStatement l = match l with C -> isvalid_c.makeExpressionToStatement | Ada -> isvalid_a.makeExpressionToStatement
let callBaseTypeFunc l = match l with C -> isvalid_c.call_base_type_func | Ada -> isvalid_a.call_base_type_func
let callBaseTypeFuncExp l = match l with C -> isvalid_c.call_base_type_func_exp | Ada -> isvalid_a.call_base_type_func_exp
let joinTwoIfFirstOk l = match l with C -> isvalid_c.JoinTwoIfFirstOk | Ada -> isvalid_a.JoinTwoIfFirstOk

let getAddres = DAstEqual.getAddres

let createPrimitiveFunction (r:CAst.AstRoot) (l:ProgrammingLanguage)  tasInfo (typeId:ReferenceToType) allCons  conToStrFunc (typeDefinition:TypeDefinitionCommon) (alphaFuncs : AlphaFunc list) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    let baseFuncName = baseFuncName baseTypeValFunc
    let hasValidationFunc= hasValidationFunc allCons baseFuncName
    match hasValidationFunc with
    | false            -> None, us
    | true             ->
        let funcName            = getFuncName r l tasInfo
        let errCodeName         = ToC ("ERR_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
        let errCodeValue        = us.currErrCode
        let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
        let funcExp (p:String) = 
            let allCons = allCons |> List.map (conToStrFunc p)
            match allCons, baseFuncName with
            | [], None      -> raise(BugErrorException("Invalid case"))
            | c::cs, None   -> l.ExpAndMulti allCons 
            | [], Some baseFncName      -> callBaseTypeFuncExp l p baseFncName
            | c::cs, Some baseFncName   -> 
                let e1 = callBaseTypeFuncExp l p baseFncName
                let e2 = l.ExpAndMulti allCons
                l.ExpAnd e1 e2

        let funcBody (p:String) = 
            let allCons = allCons |> List.map (conToStrFunc p)
            match allCons, baseFuncName with
            | [], None      -> raise(BugErrorException("Invalid case"))
            | c::cs, None   ->
                makeExpressionToStatement l (l.ExpAndMulti allCons) errCode.errCodeName
            | [], Some baseFncName      -> callBaseTypeFunc l p baseFncName
            | c::cs, Some baseFncName   -> 
                let s1 = callBaseTypeFunc l p baseFncName
                let s2 = makeExpressionToStatement l (l.ExpAndMulti allCons) errCode.errCodeName
                joinTwoIfFirstOk l s1 s2

        let  func  = 
                match funcName  with
                | None              -> None
                | Some funcName     -> 
                    let p = "val"
                    let exp = funcBody p  
                    match l with
                    |C     -> Some(isvalid_c.EmitTypeAssignment_primitive funcName  typeDefinition.name exp  (alphaFuncs |> List.map(fun x -> x.funcBody)) )
                    |Ada   -> Some(isvalid_a.EmitTypeAssignment_primitive funcName  typeDefinition.name exp  (alphaFuncs |> List.map(fun x -> x.funcBody)) )
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  Some(isvalid_c.EmitTypeAssignment_primitive_def funcName  typeDefinition.name errCode.errCodeName (BigInteger errCode.errCodeValue))
                    |Ada   ->  Some(isvalid_a.EmitTypeAssignment_primitive_def funcName  typeDefinition.name errCode.errCodeName (BigInteger errCode.errCodeValue))
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = [errCode]
                func                        = func
                funcDef                     = funcDef
                funcExp                     = Some funcExp
                funcBody                    = funcBody 
                funcBody2                   = (fun p acc -> funcBody p)
                alphaFuncs                  = alphaFuncs
                localVariables              = []
            }    
        Some ret, {us with currErrCode = us.currErrCode + 1}

let createBitOrOctetStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage)  tasInfo (typeId:ReferenceToType) allCons  conToStrFunc (typeDefinition:TypeDefinitionCommon) (alphaFuncs : AlphaFunc list) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    let baseFuncName = baseFuncName baseTypeValFunc
    let hasValidationFunc = hasValidationFunc allCons baseFuncName
    let baseCallStatement l p baseFncName =
        callBaseTypeFunc l (getAddres l p) baseFncName
    match hasValidationFunc with
    | false            -> None, us
    | true             ->
        let funcName            = getFuncName r l tasInfo
        let errCodeName         = ToC ("ERR_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
        let errCodeValue        = us.currErrCode
        let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}


        let funcBody (p:String) (childAccess:string)  = 
            let allCons = allCons |> List.map ((conToStrFunc childAccess) p )
            match allCons, baseFuncName with
            | [], None      -> raise(BugErrorException("Invalid case"))
            | c::cs, None   ->
                makeExpressionToStatement l (l.ExpAndMulti allCons) errCode.errCodeName
            | [], Some baseFncName      -> baseCallStatement l p baseFncName
            | c::cs, Some baseFncName   -> 
                let s1 = baseCallStatement l p baseFncName
                let s2 = makeExpressionToStatement l (l.ExpAndMulti allCons) errCode.errCodeName
                joinTwoIfFirstOk l s1 s2


        let  func  = 
                match funcName  with
                | None              -> None
                | Some funcName     -> 
                    let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
                    let exp = funcBody p  topLevAcc
                    match l with
                    |C     -> Some(isvalid_c.EmitTypeAssignment_oct_or_bit_string funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) )
                    |Ada   -> Some(isvalid_a.EmitTypeAssignment_primitive funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) )
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  Some(isvalid_c.EmitTypeAssignment_oct_or_bit_string_def funcName  typeDefinition.name errCode.errCodeName (BigInteger errCode.errCodeValue))
                    |Ada   ->  Some(isvalid_a.EmitTypeAssignment_primitive_def funcName  typeDefinition.name errCode.errCodeName (BigInteger errCode.errCodeValue))
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = [errCode]
                func                        = func
                funcExp                     = None
                funcDef                     = funcDef
                funcBody                    = (fun p -> funcBody p ".")
                funcBody2                   = funcBody
                alphaFuncs                  = alphaFuncs
                localVariables              = []
            }    
        Some ret, {us with currErrCode = us.currErrCode + 1}


let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString())) typeDefinition [] baseTypeValFunc us

let createRealFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldRangeCon l (fun v -> v.ToString("E20", NumberFormatInfo.InvariantInfo)) (fun v -> v.ToString("E20", NumberFormatInfo.InvariantInfo))) typeDefinition [] baseTypeValFunc us

let createStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    let alphafuncName = ToC (((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")) + "_CharsAreValid")
    let foldAlpha = (foldRangeCon l (fun v -> v.ToString().ISQ) (fun v -> v.ToString().ISQ))
    let alpaCons = o.AllCons |> List.choose(fun x -> match x with AlphabetContraint al-> Some al | _ -> None) |> List.map (foldAlpha (sprintf "str%s" (l.ArrayAccess "i")))
    let alphaFuncs = 
        match alpaCons with
        | []    -> []
        | _     ->
            let funcBody =
                match l with
                | C    -> isvalid_c.Print_AlphabetCheckFunc alphafuncName alpaCons
                | Ada  -> isvalid_a.Print_AlphabetCheckFunc alphafuncName alpaCons
            let alphFunc = {AlphaFunc.funcName = alphafuncName; funcBody = funcBody }
            [alphFunc]
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldStringCon l alphafuncName) typeDefinition alphaFuncs baseTypeValFunc us

let createBoolFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldGenericCon l  (fun v -> v.ToString().ToLower())) typeDefinition [] baseTypeValFunc us

let createEnumeratedFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    let printNamedItem (v:string) =
        let itm = o.items |> Seq.find (fun x -> x.name = v)
        itm.getBackendName l
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldGenericCon l  printNamedItem) typeDefinition [] baseTypeValFunc us


let exlcudeSizeConstraintIfFixedSize minSize maxSize allCons = 
    match minSize = maxSize with
    | false -> allCons
    | true  -> allCons |> List.filter(fun x -> match x with SizeContraint al-> false | _ -> true)

let createOctetStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (equalFunc:EqualFunction) (us:State)  =
    let allCons = exlcudeSizeConstraintIfFixedSize o.minSize o.maxSize o.AllCons
    let compareSingValueFunc (p:String) acc (v:OctetStringValue) =
        let vstr = 
            match acc with
            | "->"  -> getAddres l ((OctetStringValue v).getBackendName l)
            | _     -> ((OctetStringValue v).getBackendName l)
        match equalFunc.isEqualBody2 with
        | EqualBodyExpression2 eqFunc    ->
            match eqFunc p vstr acc with
            | None          -> raise(BugErrorException "unexpected case")
            | Some (ret,_)      -> ret
        | EqualBodyStatementList2  _     -> raise(BugErrorException "unexpected case")
    let foldSizeCon childAccess = foldSizableConstraint l (fun p v -> compareSingValueFunc p childAccess v) (fun l p -> l.Length p childAccess)
    createBitOrOctetStringFunction r l o.tasInfo o.id allCons foldSizeCon typeDefinition [] baseTypeValFunc us

let createBitStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString) (typeDefinition:TypeDefinitionCommon) (baseTypeValFunc : IsValidFunction option) (equalFunc:EqualFunction) (us:State)  =
    let allCons = exlcudeSizeConstraintIfFixedSize o.minSize o.maxSize o.AllCons
    let compareSingValueFunc (p:String) acc (v:BitStringValue) =
        let vstr = 
            match acc with
            | "->"  -> getAddres l ((BitStringValue v).getBackendName l)
            | _     -> ((BitStringValue v).getBackendName l)
        match equalFunc.isEqualBody2 with
        | EqualBodyExpression2 eqFunc    ->
            match eqFunc p vstr acc with
            | None          -> raise(BugErrorException "unexpected case")
            | Some (ret,_)      -> ret
        | EqualBodyStatementList2  _     -> raise(BugErrorException "unexpected case")
    let foldSizeCon childAccess = foldSizableConstraint l (fun p v -> compareSingValueFunc p childAccess v) (fun l p -> l.Length p childAccess)
    createBitOrOctetStringFunction r l o.tasInfo o.id allCons foldSizeCon typeDefinition [] baseTypeValFunc us


(*  SEQUENCE *)

let isValidSequenceChild   (l:ProgrammingLanguage) (o:CAst.SeqChildInfo) (newChild:Asn1Type) (currErrCode:int)= 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isValidFunction with
        | Some (isValidFunction)    ->
            Some((fun p childAccess ->
                    isValidFunction.funcBody (p + childAccess + c_name)), isValidFunction)
        | None      -> None
    let sInnerStatement =
        match sInnerStatement with
        | None                  -> None
        | Some (func, isValid)  ->
            match o.optionality with
            | Some _    -> 
                match l with
                | C     -> 
                    let newFunc = (fun p childAccess -> isvalid_c.Sequence_OptionalChild p childAccess c_name (func p childAccess))
                    Some (newFunc, isValid)
                | Ada   -> 
                    let newFunc = (fun p childAccess -> isvalid_a.Sequence_OptionalChild p childAccess c_name (func p childAccess))
                    Some (newFunc, isValid)
            | None      -> Some (func, isValid)
    let isAlwaysPresentStatement, finalState =
        let child_always_present_or_absent = match l with C -> isvalid_c.Sequence_optional_child_always_present_or_absent | Ada -> isvalid_a.Sequence_optional_child_always_present_or_absent
            
        match o.optionality with
        | Some(CAst.AlwaysAbsent)                     -> 
            let errCodeName = ToC ("ERR_" + ((newChild.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm"))) + "_IS_PRESENT"
            let errCodeValue        = currErrCode
            let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
            let isValidStatement = (fun p childAccess -> child_always_present_or_absent p childAccess c_name errCode.errCodeName "0")
            Some(isValidStatement, errCode), currErrCode + 1
        | Some(CAst.AlwaysPresent)                    -> 
            let errCodeName = ToC ("ERR_" + ((newChild.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm"))) + "_IS_ABSENT"
            let errCodeValue        = currErrCode
            let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
            let isValidStatement = (fun p childAccess -> child_always_present_or_absent p childAccess c_name errCode.errCodeName "1")
            Some(isValidStatement, errCode), currErrCode + 1
        | _         -> None, currErrCode

    match sInnerStatement, isAlwaysPresentStatement with
    | None, None                                       -> None , finalState
    | None, Some(isValid, errCode)                     -> 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = []; alphaFuncs = []; errCode = [errCode]}), finalState
    | Some(isValid, chFunc), None                      -> 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = chFunc.localVariables; alphaFuncs = chFunc.alphaFuncs; errCode = chFunc.errCodes}), finalState
    | Some(isValid1, chFunc), Some(isValid2, errCode)    -> 
        // isvalid_c.JoinTwo is language independent so it is used for both C and Ada
        let isValid = (fun p childAccess -> isvalid_c.JoinTwo (isValid2 p childAccess)  (isValid1 p childAccess)) 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = chFunc.localVariables; alphaFuncs = chFunc.alphaFuncs; errCode = errCode::chFunc.errCodes}), finalState


let createSequenceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Sequence) (typeDefinition:TypeDefinitionCommon) (children:SeqChildInfo list) (baseTypeValFunc : IsValidFunction option) (us:State)  =

    let funcName            = getFuncName r l o.tasInfo
    let baseFuncName = baseFuncName baseTypeValFunc

    let body =
        match baseFuncName with
        | None  ->
            let childrenConent, finalErrCode =   
                children |> 
                List.filter(fun c -> not c.acnInsertetField) |> 
                GenericFold2.foldMap (fun errCode cc -> cc.isValidBodyStats errCode) us.currErrCode
            let childrenConent = childrenConent |> List.choose id
            let deltaErrCode = finalErrCode - us.currErrCode

            match childrenConent with
            | []    -> None
            | x::xs ->
                let alphaFuncs = childrenConent |> List.collect(fun x -> x.alphaFuncs)
                let localVars = childrenConent |> List.collect(fun x -> x.localVars)
                let ercCodes = childrenConent |> List.collect(fun x -> x.errCode)
                let funcBody  (p:string)  (childAccess:string) = 
                    let printChild (content:string) (sNestedContent:string option) = 
                        match sNestedContent with
                        | None  -> content
                        | Some c-> 
                            match l with
                            | C        -> equal_c.JoinItems content sNestedContent
                            | Ada      -> isvalid_a.JoinItems content sNestedContent
                    let rec printChildren children : string option = 
                        match children with
                        |[]     -> None
                        |x::xs  -> 
                            match printChildren xs with
                            | None                 -> Some (printChild x  None)
                            | Some childrenCont    -> Some (printChild x  (Some childrenCont))

                    let isValidStatementX = x.isValidStatement p childAccess 
                    let isValidStatementXS = xs |> List.map(fun x -> x.isValidStatement  p childAccess)
                    printChild isValidStatementX (printChildren isValidStatementXS)
                Some(alphaFuncs, localVars, ercCodes, funcBody, deltaErrCode)
        | Some baseFncName    ->
            let alphaFuncs = []
            let localVars = []
            let ercCodes = []
            let funcBody  (p:string)  (childAccess:string) = 
                callBaseTypeFunc l (getAddres l p) baseFncName
            Some(alphaFuncs, localVars, ercCodes, funcBody, 0)
    match body with
    | None    -> None, us
    | Some(alphaFuncs, localVars, ercCodes, funcBody, deltaErrCode) ->
        let  func  = 
            let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let exp = funcBody p topLevAcc
                let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                match l with
                |C     -> Some(isvalid_c.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
                |Ada   -> Some(isvalid_a.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     -> 
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_c.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_c.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
                    |Ada   -> 
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_a.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_a.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = ercCodes
                func                        = func
                funcDef                     = funcDef
                funcExp                     = None
                funcBody                    = (fun p -> funcBody p ".")
                funcBody2                   = funcBody
                alphaFuncs                  = alphaFuncs
                localVariables              = localVars
            }    
        Some ret, {us with currErrCode = us.currErrCode + deltaErrCode}

(*  CHOICE *)
let isValidChoiceChild   (l:ProgrammingLanguage) (o:CAst.ChChildInfo) (newChild:Asn1Type) (currErrCode:int)= 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isValidFunction with
        | Some (isValidFunction)    ->
             Some((fun p childAccess ->isValidFunction.funcBody (p + childAccess + c_name)), isValidFunction)
        | None      -> None
    

    match sInnerStatement with
    | None  -> None , currErrCode
    | Some(isValid, chFunc)                      -> 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = chFunc.localVariables; alphaFuncs = chFunc.alphaFuncs; errCode = chFunc.errCodes}), currErrCode

let createChoiceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Choice) (typeDefinition:TypeDefinitionCommon) (children:ChChildInfo list) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    let funcName            = getFuncName r l o.tasInfo
    let baseFuncName = baseFuncName baseTypeValFunc

    let body =
        match baseFuncName with
        | None  ->
            let errCodeName         = ToC ("ERR_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
            let errCodeValue        = us.currErrCode
            let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

            let childrenConent, finalErrCode =   
                children |> 
                GenericFold2.foldMap (fun errCode cc -> 
                    let (vc,erc) = cc.isValidBodyStats errCode
                    ((cc,vc),erc)) (us.currErrCode+1)
            let deltaErrCode = finalErrCode - us.currErrCode

            let validatedComponenets = childrenConent |> List.map snd |> List.choose id
            let alphaFuncs = validatedComponenets |> List.collect(fun x -> x.alphaFuncs)
            let localVars =  validatedComponenets |> List.collect(fun x -> x.localVars)
            let ercCodes =   errCode::(validatedComponenets |> List.collect(fun x -> x.errCode))
            let funcBody  (p:string)  (childAccess:string) = 
                let childrenContent =
                    childrenConent |> 
                    List.map(fun (cc, vc) -> 
                    match l with
                    | C    -> 
                        let chBody =  
                            match vc with
                            | Some vc -> vc.isValidStatement (p+childAccess+"u")  "." 
                            | None    -> isvalid_c.always_true_statement ()
                        isvalid_c.choice_child cc.presentWhenName chBody
                    |Ada   -> 
                        let chBody = 
                            match vc with
                            | Some vc -> vc.isValidStatement p "."
                            | None    -> isvalid_a.always_true_statement ()
                        isvalid_a.choice_child cc.presentWhenName chBody)
                match l with
                | C    -> isvalid_c.choice p childAccess childrenContent errCode.errCodeName
                |Ada   -> isvalid_a.choice p childAccess childrenContent errCode.errCodeName
            Some(alphaFuncs, localVars, ercCodes, funcBody, deltaErrCode)
        | Some baseFncName    ->
            let alphaFuncs = []
            let localVars = []
            let ercCodes = []
            let funcBody  (p:string)  (childAccess:string) = 
                callBaseTypeFunc l (getAddres l p) baseFncName
            Some(alphaFuncs, localVars, ercCodes, funcBody, 0)
    match body with
    | None    -> None, us
    | Some(alphaFuncs, localVars, ercCodes, funcBody, deltaErrCode) ->
        let  func  = 
            let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let exp = funcBody p topLevAcc
                let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                match l with
                |C     -> Some(isvalid_c.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
                |Ada   -> Some(isvalid_a.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_c.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_c.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
                    |Ada   ->  
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_a.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_a.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = ercCodes
                func                        = func
                funcDef                     = funcDef
                funcExp                     = None
                funcBody                    = (fun p -> funcBody p ".")
                funcBody2                   = funcBody
                alphaFuncs                  = alphaFuncs
                localVariables              = localVars
            }    
        Some ret, {us with currErrCode = us.currErrCode + deltaErrCode}


let createSequenceOfFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.SequenceOf) (typeDefinition:TypeDefinitionCommon) (childType:Asn1Type) (baseTypeValFunc : IsValidFunction option) (us:State)  =
    let funcName            = getFuncName r l o.tasInfo
    let baseFuncName = baseFuncName baseTypeValFunc
    let bIsFixedSize = o.minSize = o.maxSize
    let hasValidationFunc = 
        match bIsFixedSize with
        | false     -> true
        | true      ->
            match childType.isValidFunction with
            | Some _  -> true
            | None    -> 
                match baseFuncName with
                | None      -> false
                | Some _    -> true

    let baseCallStatement l p baseFncName =
        callBaseTypeFunc l (getAddres l p) baseFncName

    let body =
        let allSizeCons = o.AllCons |> List.filter(fun x -> match x with SizeContraint al-> true | _ -> false)
        let foldSizeCon childAccess = foldSizableConstraint l (fun p v -> v.ToString()) (fun l p -> l.Length p childAccess)
        let sizeConstrData = 
            match bIsFixedSize with
            | true  -> None
            | false ->
                match allSizeCons with
                | []    -> None
                | _     ->
                    let errCodeName         = ToC ("ERR_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
                    let errCodeValue        = us.currErrCode
                    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
                    let sIsValidSizeExpFunc (p:string) (childAccess:string) =
                        let allCons = allSizeCons |> List.map ((foldSizeCon childAccess) p )
                        l.ExpAndMulti allCons
                    Some(errCode, sIsValidSizeExpFunc)
        match baseFuncName with
        | None  ->
            let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
            let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
            match childType.isValidFunction, sizeConstrData with
            | None, None     -> None
            | Some cvf, None ->
                let funcBody (p:String) (childAccess:string)  = 
                    let childAccesPath = p + childAccess + l.ArrName + (l.ArrayAccess i) //"[" + i + "]"
                    let innerStatement = Some(cvf.funcBody childAccesPath )
                    match l with
                    | C   -> isvalid_c.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) None None innerStatement
                    | Ada -> isvalid_a.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) None None innerStatement
                Some(cvf.alphaFuncs, lv::cvf.localVariables , cvf.errCodes, funcBody, 0)
            | None, Some(errCode, sIsValidSizeExpFunc) ->
                let funcBody (p:String) (childAccess:string)  = 
                    makeExpressionToStatement l (sIsValidSizeExpFunc p childAccess) errCode.errCodeName
                Some([],[], [errCode], funcBody, 1)
            | Some cvf, Some(errCode, sIsValidSizeExpFunc) ->
                let funcBody (p:String) (childAccess:string)  = 
                    let childAccesPath = p + childAccess + l.ArrName + (l.ArrayAccess i) //"[" + i + "]"
                    let innerStatement = Some(cvf.funcBody childAccesPath )
                    match l with
                    | C   -> isvalid_c.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) (Some (sIsValidSizeExpFunc p childAccess)) (Some errCode.errCodeName) innerStatement
                    | Ada -> isvalid_a.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) (Some (sIsValidSizeExpFunc p childAccess)) (Some errCode.errCodeName) innerStatement
                Some(cvf.alphaFuncs, lv::cvf.localVariables , cvf.errCodes@[errCode], funcBody, 1)
        | Some baseFncName    ->
            match sizeConstrData with
            | None     -> 
                let funcBody  (p:string)  (childAccess:string) = 
                    callBaseTypeFunc l (getAddres l p) baseFncName
                Some([], [], [], funcBody, 0)
            | Some(errCode, sIsValidSizeExpFunc) ->
                let funcBody (p:String) (childAccess:string)  = 
                    let s1 = callBaseTypeFunc l (getAddres l p) baseFncName
                    let s2 = makeExpressionToStatement l (sIsValidSizeExpFunc p childAccess) errCode.errCodeName
                    joinTwoIfFirstOk l s1 s2
                Some([],[], [errCode], funcBody, 1)


    match body with
    | None -> None, us
    | Some(alphaFuncs, localVars, ercCodes, funcBody, deltaErrCode) ->
(*        
        let funcName            = getFuncName r l o.tasInfo
        let errCodeName         = ToC ("ERR_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
        let errCodeValue        = us.currErrCode
        let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
        let allSizeCons = o.AllCons |> List.filter(fun x -> match x with SizeContraint al-> true | _ -> false)
        let foldSizeCon childAccess = foldSizableConstraint l (fun v -> v.ToString()) (fun l p -> l.Length p childAccess)

        let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
        let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)

        let ercCodes, localVars, alphaFuncs =
            match childType.isValidFunction with
            | None      -> [errCode], [], []
            | Some vf   -> errCode::vf.errCodes, lv::vf.localVariables, vf.alphaFuncs

        let funcBody (p:String) (childAccess:string)  = 
            let getInnerStatement i = 
                match childType.isValidFunction with
                | None    ->    None
                | Some isValidFunction ->
                    let childAccesPath = p + childAccess + l.ArrName + (l.ArrayAccess i) //"[" + i + "]"
                    Some(isValidFunction.funcBody childAccesPath )
            let soIsValidSizeExp =
                match bIsFixedSize with
                | true  -> None
                | false ->
                    match allSizeCons with
                    | []    -> None
                    | _     ->
                        let allCons = allSizeCons |> List.map ((foldSizeCon childAccess) p )
                        Some (l.ExpAndMulti allCons)
            let innerStatement = getInnerStatement i
            match l with
            | C   -> isvalid_c.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) soIsValidSizeExp (Some errCode.errCodeName) innerStatement
            | Ada -> isvalid_a.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) soIsValidSizeExp (Some errCode.errCodeName) innerStatement
*)
        let  func  = 
            let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let exp = funcBody p topLevAcc
                let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                match l with
                |C     -> Some(isvalid_c.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
                |Ada   -> Some(isvalid_a.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_c.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_c.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
                    |Ada   ->  
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_a.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_a.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)

        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = ercCodes
                func                        = func
                funcDef                     = funcDef
                funcExp                     = None
                funcBody                    = (fun p -> funcBody p ".")
                funcBody2                   = funcBody
                alphaFuncs                  = alphaFuncs
                localVariables              = localVars
            }    
        Some ret, {us with currErrCode = us.currErrCode + deltaErrCode}
