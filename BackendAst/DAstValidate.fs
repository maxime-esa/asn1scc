module DAstValidate

open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open Constraints
open DAst

let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_IsConstraintValid"))

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


let foldSizableConstraint (l:ProgrammingLanguage) valToStrFunc  getSizeFunc (p:String) (c:SizableTypeConstraint<'v>) =
    foldSizableTypeConstraint2
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpStringEqual p (valToStrFunc v) ,s)
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

let createPrimitiveFunction (r:CAst.AstRoot) (l:ProgrammingLanguage)  tasInfo (typeId:ReferenceToType) allCons  conToStrFunc (typeDefinition:TypeDefinitionCommon) (alphaFuncs : AlphaFunc list) (us:State)  =
    match allCons with
    | []            -> None, us
    | _             ->
        let funcName            = getFuncName r l tasInfo
        let errCodeName         = ToC ("ERR_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
        let errCodeValue        = us.currErrCode
        let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

        let funcBody (p:String) = 
            let allCons = allCons |> List.map (conToStrFunc p)
            l.ExpAndMulti allCons

        let  func  = 
                match funcName  with
                | None              -> None
                | Some funcName     -> 
                    let p = "val"
                    let exp = funcBody p  
                    match l with
                    |C     -> Some(isvalid_c.EmitTypeAssignment_primitive funcName  typeDefinition.name exp errCode.errCodeName (alphaFuncs |> List.map(fun x -> x.funcBody)) )
                    |Ada   -> Some(isvalid_a.EmitTypeAssignment_primitive funcName  typeDefinition.name exp errCode.errCodeName (alphaFuncs |> List.map(fun x -> x.funcBody)) )
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
                funcBody                    = ValidBodyExpression funcBody 
                alphaFuncs                  = alphaFuncs
                localVariables              = []
            }    
        Some ret, {us with currErrCode = us.currErrCode + 1}

let createBitOrOctetStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage)  tasInfo (typeId:ReferenceToType) allCons  conToStrFunc (typeDefinition:TypeDefinitionCommon) (alphaFuncs : AlphaFunc list) (us:State)  =
    match allCons with
    | []            -> None, us
    | _             ->
        let funcName            = getFuncName r l tasInfo
        let errCodeName         = ToC ("ERR_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
        let errCodeValue        = us.currErrCode
        let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}


        let funcBody (p:String) (childAccess:string)  = 
            let allCons = allCons |> List.map ((conToStrFunc childAccess) p )
            l.ExpAndMulti allCons

        let  func  = 
                match funcName  with
                | None              -> None
                | Some funcName     -> 
                    let p = "pVal" 
                    let exp = funcBody p  "->"
                    match l with
                    |C     -> Some(isvalid_c.EmitTypeAssignment_oct_or_bit_string funcName  typeDefinition.name exp errCode.errCodeName (alphaFuncs |> List.map(fun x -> x.funcBody)) )
                    |Ada   -> Some(isvalid_a.EmitTypeAssignment_primitive funcName  typeDefinition.name exp errCode.errCodeName (alphaFuncs |> List.map(fun x -> x.funcBody)) )
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
                funcDef                     = funcDef
                funcBody                    = ValidBodyExpression (fun p -> funcBody p ".")
                alphaFuncs                  = alphaFuncs
                localVariables              = []
            }    
        Some ret, {us with currErrCode = us.currErrCode + 1}


let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString())) typeDefinition [] us

let createRealFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldRangeCon l (fun v -> v.ToString("E20", NumberFormatInfo.InvariantInfo)) (fun v -> v.ToString("E20", NumberFormatInfo.InvariantInfo))) typeDefinition [] us

let createStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType) (typeDefinition:TypeDefinitionCommon) (us:State)  =
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
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldStringCon l alphafuncName) typeDefinition alphaFuncs us

let createBoolFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldGenericCon l  (fun v -> v.ToString().ToLower())) typeDefinition [] us

let createEnumeratedFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let printNamedItem (v:string) =
        let itm = o.items |> Seq.find (fun x -> x.name = v)
        itm.getBackendName l
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldGenericCon l  printNamedItem) typeDefinition [] us

let createOctetStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let allCons = 
        match o.minSize = o.maxSize with
        | false -> o.AllCons
        | true  -> o.AllCons |> List.filter(fun x -> match x with SizeContraint al-> false | _ -> true)
    let foldSizeCon childAccess = foldSizableConstraint l (fun v -> v.ToString()) (fun l p -> l.Length p childAccess)
    createBitOrOctetStringFunction r l o.tasInfo o.id allCons foldSizeCon typeDefinition [] us

let createBitStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let allCons = 
        match o.minSize = o.maxSize with
        | false -> o.AllCons
        | true  -> o.AllCons |> List.filter(fun x -> match x with SizeContraint al-> false | _ -> true)
    let foldSizeCon childAccess = foldSizableConstraint l (fun v -> v.ToString()) (fun l p -> l.Length p childAccess)
    createBitOrOctetStringFunction r l o.tasInfo o.id allCons foldSizeCon typeDefinition [] us


(*  SEQUENCE *)

let isValidSequenceChild   (l:ProgrammingLanguage) (o:CAst.SeqChildInfo) (newChild:Asn1Type) (currErrCode:int)= 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isValidFunction with
        | Some (isValidFunction)    ->
            match isValidFunction.funcBody with  
            | ValidBodyExpression func  ->  
                Some((fun p childAccess ->
                let exp= func (p + childAccess + c_name)
                match l with
                | C     -> isvalid_c.makeExpressionToStatement exp isValidFunction.errCodes.Head.errCodeName
                | Ada   -> isvalid_c.makeExpressionToStatement exp isValidFunction.errCodes.Head.errCodeName), isValidFunction)
            | ValidBodyStatementList  func   -> 
                Some((fun p childAccess ->
                    func (p + childAccess + c_name)), isValidFunction)
        | None      -> None
    let isAlwaysPresentStatement, finalState =
        match o.optionality with
        | Some(CAst.AlwaysAbsent)                     -> 
            let errCodeName = ToC ("ERR_" + ((newChild.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm"))) + "_IS_PRESENT"
            let errCodeValue        = currErrCode
            let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
            let isValidStatement = (fun p childAccess -> isvalid_c.isValid_Sequence_optional_child_always_present_or_absent p childAccess c_name "0")
            Some(isValidStatement, errCode), currErrCode + 1
        | Some(CAst.AlwaysPresent)                    -> 
            let errCodeName = ToC ("ERR_" + ((newChild.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm"))) + "_IS_ABSENT"
            let errCodeValue        = currErrCode
            let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}
            let isValidStatement = (fun p childAccess -> isvalid_c.isValid_Sequence_optional_child_always_present_or_absent p childAccess c_name "1")
            Some(isValidStatement, errCode), currErrCode + 1
        | _         -> None, currErrCode

    match sInnerStatement, isAlwaysPresentStatement with
    | None, None                                       -> None , finalState
    | None, Some(isValid, errCode)                     -> 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = []; alphaFuncs = []; errCode = [errCode]}), finalState
    | Some(isValid, chFunc), None                      -> 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = chFunc.localVariables; alphaFuncs = chFunc.alphaFuncs; errCode = chFunc.errCodes}), finalState
    | Some(isValid1, chFunc), Some(isValid2, errCode)    -> 
        let isValid = (fun p childAccess -> isvalid_c.JoinTwo (isValid2 p childAccess)  (isValid1 p childAccess))
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = chFunc.localVariables; alphaFuncs = chFunc.alphaFuncs; errCode = errCode::chFunc.errCodes}), finalState

let createSequenceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Sequence) (typeDefinition:TypeDefinitionCommon) (children:SeqChildInfo list) (us:State)  =
    
    //System.Console.Out.WriteLine("{0} : {1}", o.id.ToString(), us.currErrCode)

    let funcName            = getFuncName r l o.tasInfo

    let childrenConent, finalErrCode =   
        children |> 
        List.filter(fun c -> not c.acnInsertetField) |> 
        CloneTree.foldMap (fun errCode cc -> cc.isValidBodyStats errCode) us.currErrCode
    let childrenConent = childrenConent |> List.choose id

    match childrenConent with
    | []    -> None, us
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
                    | Ada      -> equal_a.JoinItems content sNestedContent
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
        let  func  = 
            let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let exp = funcBody p topLevAcc
                let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                match l with
                |C     -> Some(isvalid_c.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
                |Ada   -> None //Some(isvalid_a.EmitTypeAssignment_composite funcName  typeDefinition.name exp ercCodes (alphaFuncs |> List.map(fun x -> x.funcBody)) )
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_c.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_c.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
                    |Ada   ->  None //Some(isvalid_a.EmitTypeAssignment_composite_def funcName  typeDefinition.name ercCodes (BigInteger errCodeValue))
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = ercCodes
                func                        = func
                funcDef                     = funcDef
                funcBody                    = ValidBodyStatementList (fun p -> funcBody p ".")
                alphaFuncs                  = alphaFuncs
                localVariables              = localVars
            }    
        Some ret, {us with currErrCode = us.currErrCode + finalErrCode}

(*  CHOICE *)
let isValidChoiceChild   (l:ProgrammingLanguage) (o:CAst.ChChildInfo) (newChild:Asn1Type) (currErrCode:int)= 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isValidFunction with
        | Some (isValidFunction)    ->
            match isValidFunction.funcBody with  
            | ValidBodyExpression func  ->  
                Some((fun p childAccess ->
                let exp= func (p + childAccess + c_name)
                match l with
                | C     -> isvalid_c.makeExpressionToStatement exp isValidFunction.errCodes.Head.errCodeName
                | Ada   -> isvalid_c.makeExpressionToStatement exp isValidFunction.errCodes.Head.errCodeName), isValidFunction)
            | ValidBodyStatementList  func   -> 
                Some((fun p childAccess ->
                    func (p + childAccess + c_name)), isValidFunction)
        | None      -> None
    

    match sInnerStatement with
    | None  -> None , currErrCode
    | Some(isValid, chFunc)                      -> 
        Some({SeqChoiceChildInfoIsValid.isValidStatement = isValid; localVars = chFunc.localVariables; alphaFuncs = chFunc.alphaFuncs; errCode = chFunc.errCodes}), currErrCode

let createChoiceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Choice) (typeDefinition:TypeDefinitionCommon) (children:ChChildInfo list) (us:State)  =

    let funcName            = getFuncName r l o.tasInfo
    let errCodeName         = ToC ("ERR_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let childrenConent, finalErrCode =   
        children |> 
        CloneTree.foldMap (fun errCode cc -> 
            let (vc,erc) = cc.isValidBodyStats errCode
            ((cc,vc),erc)) (us.currErrCode+1)

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
                let chBody = vc |> Option.map(fun vc -> vc.isValidStatement (p+childAccess+"u")  "." )
                isvalid_c.choice_child cc.presentWhenName chBody
            |Ada   -> 
                let chBody = vc |> Option.map(fun vc -> vc.isValidStatement p ".")
                isvalid_c.choice_child cc.presentWhenName chBody)
        match l with
        | C    -> isvalid_c.choice p childAccess childrenContent errCode.errCodeName
        |Ada   -> isvalid_c.choice p childAccess childrenContent errCode.errCodeName

    let  func  = 
        let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
        match funcName  with
        | None              -> None
        | Some funcName     -> 
            let exp = funcBody p topLevAcc
            let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
            match l with
            |C     -> Some(isvalid_c.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
            |Ada   -> None //Some(isvalid_a.EmitTypeAssignment_composite funcName  typeDefinition.name exp ercCodes (alphaFuncs |> List.map(fun x -> x.funcBody)) )
    let  funcDef  = 
            match funcName with
            | None              -> None
            | Some funcName     -> 
                match l with
                |C     ->  
                    let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_c.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                    Some(isvalid_c.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
                |Ada   ->  None //Some(isvalid_a.EmitTypeAssignment_composite_def funcName  typeDefinition.name ercCodes (BigInteger errCodeValue))
        
    let ret = 
        {
            IsValidFunction.funcName    = funcName
            errCodes                    = ercCodes
            func                        = func
            funcDef                     = funcDef
            funcBody                    = ValidBodyStatementList (fun p -> funcBody p ".")
            alphaFuncs                  = alphaFuncs
            localVariables              = localVars
        }    
    Some ret, {us with currErrCode = us.currErrCode + finalErrCode}


let createSequenceOfFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.SequenceOf) (typeDefinition:TypeDefinitionCommon) (childType:Asn1Type) (us:State)  =

    let bIsFixedSize = o.minSize = o.maxSize
    match bIsFixedSize && childType.isValidFunction.IsNone with
    | true  -> None, us
    | false ->
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
                    match isValidFunction.funcBody with
                    | ValidBodyExpression func  ->  
                        let exp = func childAccesPath
                        match l with
                        | C     -> Some(isvalid_c.makeExpressionToStatement exp isValidFunction.errCodes.Head.errCodeName)
                        | Ada   -> Some(isvalid_c.makeExpressionToStatement exp isValidFunction.errCodes.Head.errCodeName)
                    | ValidBodyStatementList  func   -> Some(func childAccesPath )

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
            isvalid_c.sequenceOf p childAccess i bIsFixedSize (BigInteger o.minSize) soIsValidSizeExp (Some errCode.errCodeName) innerStatement

        let  func  = 
            let topLevAcc, p =  match l with | C -> "->", "pVal" | Ada -> ".", "val"
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let exp = funcBody p topLevAcc
                let lvars = localVars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                match l with
                |C     -> Some(isvalid_c.EmitTypeAssignment_composite funcName  typeDefinition.name exp (alphaFuncs |> List.map(fun x -> x.funcBody)) lvars)
                |Ada   -> None //Some(isvalid_a.EmitTypeAssignment_composite funcName  typeDefinition.name exp ercCodes (alphaFuncs |> List.map(fun x -> x.funcBody)) )
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  
                        let arrsErrcodes = ercCodes |> List.map(fun s -> isvalid_c.EmitTypeAssignment_composite_def_err_code s.errCodeName (BigInteger s.errCodeValue))
                        Some(isvalid_c.EmitTypeAssignment_composite_def funcName  typeDefinition.name arrsErrcodes)
                    |Ada   ->  None //Some(isvalid_a.EmitTypeAssignment_composite_def funcName  typeDefinition.name ercCodes (BigInteger errCodeValue))
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCodes                    = ercCodes
                func                        = func
                funcDef                     = funcDef
                funcBody                    = ValidBodyStatementList (fun p -> funcBody p ".")
                alphaFuncs                  = alphaFuncs
                localVariables              = localVars
            }    
        Some ret, {us with currErrCode = us.currErrCode + 1}
