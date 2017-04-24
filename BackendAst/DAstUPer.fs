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

//TODO
//1.Decode functions (and perhaps encode function) muct check if the decode value is within the constraints (currently, implemented only for Integers and for case IntUnconstraintMax )


let createPrimitiveFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Asn1Type) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option)  (funcBody:ErroCode->FuncParamType->string) localVars soSparkAnnotations (us:State)  =
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
    let  func  = 
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let content = funcBody p  
                let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                Some(EmitTypeAssignment_primitive varName sStar funcName isValidFuncName  typeDefinition.name lvars  content soSparkAnnotations codec)
    let  funcDef  = 
            match funcName with
            | None              -> None
            | Some funcName     -> 
                Some(EmitTypeAssignment_primitive_def varName sStar funcName  typeDefinition.name [(EmitTypeAssignment_def_err_code errCode.errCodeName) (BigInteger errCode.errCodeValue)] (o.uperMaxSizeInBits = 0) (BigInteger (ceil ((double o.uperMaxSizeInBits)/8.0))) (BigInteger o.uperMaxSizeInBits) codec)


    let ret = 
        {
            UPerFunction.errCodes      = [errCode]      
            funcName                   = funcName
            func                       = func 
            funcDef                    = funcDef
            funcBody                   = funcBody
            funcBody2                  = (fun p acc -> funcBody p)
            localVariables             = localVars
        }
    ret, {us with currErrCode = us.currErrCode + 1}



let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
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
            | uPER2.Concrete(min, max) when min=max                    -> IntNoneRequired p.p min   errCode.errCodeName codec 
            | uPER2.Concrete(min, max) when min>=0I && (not extCon)    -> IntFullyConstraintPos p.p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode.errCodeName codec
            | uPER2.Concrete(min, max)                                 -> IntFullyConstraint p.p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode.errCodeName codec
            | uPER2.PosInf(a)  when a>=0I && (not extCon)  -> IntSemiConstraintPos p.p a  errCode.errCodeName codec
            | uPER2.PosInf(a)               -> IntSemiConstraint p.p a  errCode.errCodeName codec
            | uPER2.NegInf(max)             -> IntUnconstraintMax p.p max checkExp errCode.errCodeName codec
            | uPER2.Full                    -> IntUnconstraint p.p errCode.errCodeName codec

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
            let cc = DAstValidate.foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString()) p.p a
            IntRootExt p.p (getValueByConstraint uperR) cc (IntBod uperR true) errCode.errCodeName codec
        | (RangeRootConstraint2(a,_))::rest  -> 
            let uperR    = uPER2.getIntTypeConstraintUperRange [a]  o.Location
            let cc = DAstValidate.foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString()) p.p a
            IntRootExt2 p.p (getValueByConstraint uperR) cc (IntBod uperR true) errCode.errCodeName codec 
        | _                             -> raise(BugErrorException "")
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Integer o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody [] soSparkAnnotations us


let createBooleanFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let Boolean         = match l with C -> uper_c.Boolean          | Ada -> uper_a.Boolean
        Boolean p.p errCode.errCodeName codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Boolean o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody [] soSparkAnnotations us

let createRealFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let Real         = match l with C -> uper_c.Real          | Ada -> uper_a.Real
        Real p.p errCode.errCodeName codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Real o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody [] soSparkAnnotations us

let createNullTypeFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.NullType) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let Null         = match l with C -> uper_c.Null          | Ada -> uper_a.Null
        Null p.p codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.NullType o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody [] soSparkAnnotations us


let createEnumeratedFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let Enumerated         = match l with C -> uper_c.Enumerated          | Ada -> uper_a.Enumerated
        let Enumerated_item    = match l with C -> uper_c.Enumerated_item          | Ada -> uper_a.Enumerated_item
        
        let nMin = 0I
        let nMax = BigInteger(Seq.length o.items) - 1I
        let nLastItemIndex      = nMax
        let items = 
            o.items |> List.mapi(fun i itm -> Enumerated_item (p.getValue l) (itm.getBackendName l) (BigInteger i) nLastItemIndex codec) 
        let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
        let sFirstItemName = o.items.Head.getBackendName l
        Enumerated p.p typeDefinition.name items nMin nMax nBits errCode.errCodeName nLastItemIndex sFirstItemName codec
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Enumerated o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody [] soSparkAnnotations us


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
    createPrimitiveFunction r l codec (CAst.IA5String o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody (lv::charIndex@nStringLength) soSparkAnnotations  us

