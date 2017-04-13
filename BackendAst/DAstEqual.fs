module DAstEqual
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst


// TODO
// 1 In sequences with default components, default value must be taken into account when empty.

let callBaseTypeFunc l = match l with C -> equal_c.call_base_type_func | Ada -> equal_c.call_base_type_func
let makeExpressionToStatement l = match l with C -> equal_c.makeExpressionToStatement | Ada -> equal_a.makeExpressionToStatement

let getAddres l p=
    match l with
    | Ada -> p
    | C  when p="pVal"          -> p
    | C  when p.Contains "&"    -> p
    | C                -> sprintf "(&(%s))" p


let isEqualBodyPrimitive (l:ProgrammingLanguage) v1 v2 =
    match l with
    | C         -> Some (sprintf "%s == %s" v1 v2  , [])
    | Ada       -> Some (sprintf "%s = %s" v1 v2   , [])

let isEqualBodyString (l:ProgrammingLanguage) v1 v2 =
    match l with
    | C         -> Some (sprintf "strcmp(%s, %s) == 0" v1 v2  , [])
    | Ada       -> Some (sprintf "%s = %s" v1 v2   , [])

let isEqualBodyOctetString (l:ProgrammingLanguage) sMin sMax (childAccess: string) v1 v2 =
    let v1 = sprintf "%s%s" v1 childAccess
    let v2 = sprintf "%s%s" v2 childAccess
    match l with
    | C         -> Some (equal_c.isEqual_OctetString v1 v2 (sMin = sMax) sMax, [])
    | Ada       -> Some (equal_a.isEqual_OctetString v1 v2 (sMin = sMax) sMax, [])

let isEqualBodyBitString (l:ProgrammingLanguage) sMin sMax (childAccess: string) v1 v2 =
    let v1 = sprintf "%s%s" v1 childAccess
    let v2 = sprintf "%s%s" v2 childAccess
    match l with
    | C         -> Some (equal_c.isEqual_BitString v1 v2 (sMin = sMax) sMax, [])
    | Ada       -> Some (equal_a.isEqual_BitString v1 v2 (sMin = sMax) sMax, [])

let isEqualBodySequenceOf  (childType:Asn1Type) (o:CAst.SequenceOf)  (l:ProgrammingLanguage) (childAccess: string) v1 v2  =
    let getInnerStatement i = 
        let childAccesPath v = v + childAccess + l.ArrName + (l.ArrayAccess i) //"[" + i + "]"
        match childType.equalFunction.isEqualBody with
        | EqualBodyExpression func  ->  
            match func (childAccesPath v1) (childAccesPath v2) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)       // ret = (boolExp);
            | None      -> None
        | EqualBodyStatementList  func   -> func (childAccesPath v1) (childAccesPath v2)

    let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
    let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
    match getInnerStatement i with
    | None when o.minSize = o.maxSize        -> None
    | None                                   ->
        match l with
        | C    -> Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) None, lv::[])
        | Ada  -> Some (equal_a.isEqual_SequenceOf_var_size v1 v2 i None, lv::[])
    | Some (innerStatement, lvars)           ->
        match l with
        | C    -> Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) (Some innerStatement), lv::lvars)
        | Ada  -> 
            match (o.minSize = o.maxSize) with
            | true  -> Some (equal_a.isEqual_SequenceOf_fix_size v1 v2 i  (BigInteger o.minSize) innerStatement, lv::lvars)
            | false -> Some (equal_a.isEqual_SequenceOf_var_size v1 v2 i  (Some innerStatement), lv::lvars)

    

let isEqualBodySequenceChild   (l:ProgrammingLanguage) (o:CAst.SeqChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.equalFunction.isEqualBody with
        | EqualBodyExpression func  ->  
            match func (v1 + childAccess + c_name) (v2 + childAccess + c_name) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)
            | None      -> None
        | EqualBodyStatementList  func   -> func (v1 + childAccess + c_name) (v2 + childAccess + c_name)

    match l with
    | C         -> 
        match sInnerStatement with
        | None  when  o.optionality.IsSome  -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name None, [])
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name (Some sInnerStatement), lvars)
    | Ada       ->
        match sInnerStatement with
        | None  when  o.optionality.IsSome  -> Some (equal_a.isEqual_Sequence_Child v1  v2  o.optionality.IsSome c_name None, [])
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_a.isEqual_Sequence_Child v1  v2  o.optionality.IsSome c_name (Some sInnerStatement), lvars)


let isEqualBodySequence  (l:ProgrammingLanguage) (children:SeqChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let printChild (content:string, lvars:LocalVariable list) (sNestedContent:string option) = 
        match sNestedContent with
        | None  -> content, lvars
        | Some c-> 
            match l with
            | C        -> equal_c.JoinItems content sNestedContent, lvars
            | Ada      -> equal_a.JoinItems content sNestedContent, lvars
    let rec printChildren children : Option<string*list<LocalVariable>> = 
        match children with
        |[]     -> None
        |x::xs  -> 
            match printChildren xs with
            | None                          -> Some (printChild x  None)
            | Some (childrenCont, lvars)    -> 
                let content, lv = printChild x  (Some childrenCont)
                Some (content, lv@lvars)
        
    let childrenConent =   children |> List.filter(fun c -> not c.acnInsertetField) |> List.choose(fun c -> c.isEqualBodyStats childAccess v1 v2 )  
    printChildren childrenConent




let isEqualBodyChoiceChild  (choiceTypeDefName:string) (l:ProgrammingLanguage) (o:CAst.ChChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let sInnerStatement, lvars = 
        let p1,p2 =
            match l with
            | C    ->
                (v1 + childAccess + o.c_name), (v2 + childAccess + o.c_name)
            | Ada  ->
                (v1 + childAccess + o.c_name), (v2 + childAccess + o.c_name)
        match newChild.equalFunction.isEqualBody with
        | EqualBodyExpression func  ->  
            match func p1 p2 with
            | Some (exp, lvars)     -> sprintf "ret %s (%s);" l.AssignOperator exp, lvars
            | None                  -> sprintf "ret %s TRUE;" l.AssignOperator, []
        | EqualBodyStatementList  func   -> 
            match func p1 p2 with
            | Some a    -> a
            | None      -> sprintf "ret %s TRUE;" l.AssignOperator, []

    match l with
    | C         -> 
        equal_c.isEqual_Choice_Child o.presentWhenName sInnerStatement, lvars
    | Ada       ->
        equal_a.isEqual_Choice_Child o.presentWhenName sInnerStatement, lvars

let isEqualBodyChoice  (typeDefinition:TypeDefinitionCommon) (l:ProgrammingLanguage) (children:ChChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let childrenConent,lvars =   
        children |> 
        List.map(fun c -> 
            match l with
            | C    ->
                c.isEqualBodyStats "." (v1+childAccess+"u") (v2+childAccess+"u") 
            |Ada   ->
                c.isEqualBodyStats "." v1 v2 
        )  |>
        List.unzip
    let lvars = lvars |> List.collect id
    match l with
    |C   -> Some(equal_c.isEqual_Choice v1 v2 childAccess childrenConent, lvars)
    |Ada -> Some(equal_a.isEqual_Choice v1 v2 typeDefinition.name childrenConent, lvars)


let getEqualFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_Equal"))

let createNullTypeEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.NullType) =
    {
        EqualFunction.isEqualFuncName  = None
        isEqualBody                    = EqualBodyExpression (fun  v1 v2 -> None)
        isEqualBody2                   = EqualBodyExpression2(fun  v1 v2 acc -> None)
        isEqualFunc                    = None
        isEqualFuncDef                 = None
    }    

let createEqualFunction_primitive (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) isEqualBody stgMacroFunc stgMacroDefFunc (baseTypeEqFunc: EqualFunction option) =
    let isEqualFuncName     = getEqualFuncName r l tasInfo
    let bodyFunc = match isEqualBody with EqualBodyExpression f -> f | EqualBodyStatementList f -> f

    let  isEqualFunc, isEqualFuncDef = 
            match isEqualFuncName with
            | None              -> None, None
            | Some funcName     -> 
                match bodyFunc "val1" "val2" with
                | Some (funcBody,_) -> 
                    Some (stgMacroFunc funcName typeDefinition.name funcBody), Some (stgMacroDefFunc funcName typeDefinition.name)
                | None     -> None, None

    {
        EqualFunction.isEqualFuncName  = isEqualFuncName
        isEqualBody                    = isEqualBody
        isEqualBody2                   = 
                    match isEqualBody with 
                    | EqualBodyExpression f -> EqualBodyExpression2 (fun p1 p2 acc -> f p1 p2)
                    | EqualBodyStatementList f -> EqualBodyStatementList2 (fun p1 p2 acc -> f p1 p2)
        isEqualFunc                    = isEqualFunc
        isEqualFuncDef                 = isEqualFuncDef

    }    

let stgPrintEqualPrimitive = function
    | C    -> equal_c.PrintEqualPrimitive
    | Ada  -> equal_a.PrintEqualPrimitive

let stgMacroPrimDefFunc = function
    | C    -> equal_c.PrintEqualDefintionPrimitive
    | Ada  -> equal_a.PrintEqualDefintion

let stgMacroCompDefFunc = function
    | C    -> equal_c.PrintEqualDefintionComposite
    | Ada  -> equal_a.PrintEqualDefintion

let createIntegerEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l) baseTypeEqFunc

let createRealEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l) baseTypeEqFunc

let createBooleanEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l) baseTypeEqFunc

let createEnumeratedEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l) baseTypeEqFunc

let createStringEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody = EqualBodyExpression (isEqualBodyString l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l) baseTypeEqFunc


let createOctetOrBitStringEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) isEqualBody stgMacroDefFunc (baseTypeEqFunc: EqualFunction option) =
    let topLevAcc, val1, val2 =  
        match l with 
        | C -> "->", "pVal1", "pVal2" 
        | Ada -> ".", "val1", "val2"

    let    isEqualFuncName, isEqualFunc, isEqualFuncDef, isEqualBody                   = 
            match baseTypeEqFunc with
            | None     -> 
                let funcName     = typeDefinition.name + "_Equal" //getEqualFuncName r l tasInfo
                match isEqualBody topLevAcc val1 val2 with
                | Some (funcBody,_) -> 
                    let eqBody acc p1 p2 = 
                        Some(callBaseTypeFunc l (getAddres l p1) (getAddres l p2) funcName, [])
                    match l with
                    | C    -> Some funcName, Some (equal_c.PrintEqualOctBit funcName typeDefinition.name funcBody), Some (stgMacroDefFunc funcName typeDefinition.name),eqBody
                    | Ada  -> Some funcName, Some (equal_a.PrintEqualPrimitive funcName typeDefinition.name funcBody), Some (stgMacroDefFunc funcName typeDefinition.name),eqBody
                | None     -> None, None, None, isEqualBody
            | Some baseEqFunc              -> 
                match baseEqFunc.isEqualFuncName with
                | None  -> None, None, None, isEqualBody
                | Some eqFnc    ->
                    let eqBody acc p1 p2 = 
                        Some(callBaseTypeFunc l (getAddres l p1) (getAddres l p2) eqFnc, [])
                    None, None, None, eqBody
    {
        EqualFunction.isEqualFuncName  = isEqualFuncName
        isEqualBody                    = EqualBodyExpression (isEqualBody ".")
        isEqualBody2                   = EqualBodyExpression2 (fun p1 p2 acc ->  isEqualBody acc p1 p2)
        isEqualFunc                    = isEqualFunc
        isEqualFuncDef                 = isEqualFuncDef
    }    

let createOctetStringEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody = isEqualBodyOctetString l (BigInteger o.minSize) (BigInteger o.maxSize)
    createOctetOrBitStringEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l) baseTypeEqFunc

let createBitStringEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString) (typeDefinition:TypeDefinitionCommon) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody = isEqualBodyBitString l (BigInteger o.minSize) (BigInteger o.maxSize)
    createOctetOrBitStringEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l) baseTypeEqFunc


let createCompositeEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) isEqualBody stgMacroDefFunc (baseTypeEqFunc: EqualFunction option) =
    //let isEqualFuncName     = getEqualFuncName r l tasInfo
    let topLevAcc, val1, val2 =  match l with | C -> "->", "pVal1", "pVal2" | Ada -> ".", "val1", "val2"
    (*
    let isEqualFunc, isEqualFuncDef = 
            match isEqualFuncName with
            | None              -> None, None
            | Some funcName     -> 
                match isEqualBody topLevAcc val1 val2 with
                | Some (funcBody, lvars) -> 
                    let lvars = lvars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                    match l with
                    | C    -> Some (equal_c.PrintEqualComposite funcName typeDefinition.name funcBody lvars), Some (stgMacroDefFunc funcName typeDefinition.name)
                    | Ada  -> Some (equal_a.PrintEqualComposite funcName typeDefinition.name funcBody lvars), Some (stgMacroDefFunc funcName typeDefinition.name)
                | None     -> None, None
  *)
    let    isEqualFuncName, isEqualFunc, isEqualFuncDef, isEqualBody                   = 
            match baseTypeEqFunc with
            | None     -> 
                let funcName     = typeDefinition.name + "_Equal" //getEqualFuncName r l tasInfo
                match isEqualBody topLevAcc val1 val2 with
                | Some (funcBody,lvars) -> 
                    let eqBody acc p1 p2 = 
                        let exp = callBaseTypeFunc l (getAddres l p1) (getAddres l p2) funcName
                        Some(makeExpressionToStatement l exp, [])
                    let lvars = lvars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                    match l with
                    | C    -> Some funcName, Some (equal_c.PrintEqualComposite funcName typeDefinition.name funcBody lvars), Some (stgMacroDefFunc funcName typeDefinition.name),eqBody
                    | Ada  -> Some funcName, Some (equal_a.PrintEqualComposite funcName typeDefinition.name funcBody lvars), Some (stgMacroDefFunc funcName typeDefinition.name),eqBody
                | None     -> None, None, None, isEqualBody
            | Some baseEqFunc              -> 
                match baseEqFunc.isEqualFuncName with
                | None  -> None, None, None, isEqualBody
                | Some eqFnc    ->
                    let eqBody acc p1 p2 = 
                        let exp = callBaseTypeFunc l (getAddres l p1) (getAddres l p2) eqFnc
                        Some(makeExpressionToStatement l exp, [])
                    None, None, None, eqBody


    {
        EqualFunction.isEqualFuncName  = isEqualFuncName
        isEqualBody                    = EqualBodyStatementList (isEqualBody ".")
        isEqualBody2                   = EqualBodyStatementList2(fun p1 p2 acc ->  isEqualBody acc p1 p2)
        isEqualFunc                    = isEqualFunc
        isEqualFuncDef                 = isEqualFuncDef
    }    

let createSequenceOfEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.SequenceOf) (typeDefinition:TypeDefinitionCommon) (childType:Asn1Type) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = isEqualBodySequenceOf childType o l
    createCompositeEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l) baseTypeEqFunc

let createSequenceEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Sequence) (typeDefinition:TypeDefinitionCommon) (children:SeqChildInfo list) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = isEqualBodySequence l children
    createCompositeEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l) baseTypeEqFunc

let createChoiceEqualFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Choice) (typeDefinition:TypeDefinitionCommon) (children:ChChildInfo list) (baseTypeEqFunc: EqualFunction option) =
    let isEqualBody         = isEqualBodyChoice typeDefinition l children
    createCompositeEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l) baseTypeEqFunc
