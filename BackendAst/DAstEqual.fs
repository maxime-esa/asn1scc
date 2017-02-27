module DAstEqual
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst


let isEqualBodyPrimitive (l:BAst.ProgrammingLanguage) v1 v2 =
    match l with
    | BAst.C         -> Some (sprintf "%s == %s" v1 v2  , [])
    | BAst.Ada       -> Some (sprintf "%s = %s" v1 v2   , [])

let isEqualBodyString (l:BAst.ProgrammingLanguage) v1 v2 =
    match l with
    | BAst.C         -> Some (sprintf "strcmp(%s, %s) == 0" v1 v2  , [])
    | BAst.Ada       -> Some (sprintf "%s = %s" v1 v2   , [])

let isEqualBodyOctetString (l:BAst.ProgrammingLanguage) sMin sMax (childAccess: string) v1 v2 =
    let v1 = sprintf "%s%s" v1 childAccess
    let v2 = sprintf "%s%s" v2 childAccess
    match l with
    | BAst.C         -> Some (equal_c.isEqual_OctetString v1 v2 (sMin = sMax) sMax, [])
    | BAst.Ada       -> Some (equal_a.isEqual_OctetString v1 v2 (sMin = sMax) sMax, [])

let isEqualBodyBitString (l:BAst.ProgrammingLanguage) sMin sMax (childAccess: string) v1 v2 =
    let v1 = sprintf "%s%s" v1 childAccess
    let v2 = sprintf "%s%s" v2 childAccess
    match l with
    | BAst.C         -> Some (equal_c.isEqual_BitString v1 v2 (sMin = sMax) sMax, [])
    | BAst.Ada       -> Some (equal_a.isEqual_BitString v1 v2 (sMin = sMax) sMax, [])

let isEqualBodySequenceOf  (childType:Asn1Type) (o:CAst.SequenceOf)  (l:BAst.ProgrammingLanguage) (childAccess: string) v1 v2  =
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
        | BAst.C    -> Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) None, lv::[])
        | BAst.Ada  -> Some (equal_a.isEqual_SequenceOf_var_size v1 v2 i None, lv::[])
    | Some (innerStatement, lvars)           ->
        match l with
        | BAst.C    -> Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) (Some innerStatement), lv::lvars)
        | BAst.Ada  -> 
            match (o.minSize = o.maxSize) with
            | true  -> Some (equal_a.isEqual_SequenceOf_fix_size v1 v2 i  (BigInteger o.minSize) innerStatement, lv::lvars)
            | false -> Some (equal_a.isEqual_SequenceOf_var_size v1 v2 i  (Some innerStatement), lv::lvars)

    

let isEqualBodySequenceChild   (l:BAst.ProgrammingLanguage) (o:CAst.SeqChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.equalFunction.isEqualBody with
        | EqualBodyExpression func  ->  
            match func (v1 + childAccess + c_name) (v2 + childAccess + c_name) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)
            | None      -> None
        | EqualBodyStatementList  func   -> func (v1 + childAccess + c_name) (v2 + childAccess + c_name)

    match l with
    | BAst.C         -> 
        match sInnerStatement with
        | None  when  o.optionality.IsSome  -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name None, [])
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name (Some sInnerStatement), lvars)
    | BAst.Ada       ->
        match sInnerStatement with
        | None  when  o.optionality.IsSome  -> Some (equal_a.isEqual_Sequence_Child v1  v2  o.optionality.IsSome c_name None, [])
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_a.isEqual_Sequence_Child v1  v2  o.optionality.IsSome c_name (Some sInnerStatement), lvars)


let isEqualBodySequence  (l:BAst.ProgrammingLanguage) (children:SeqChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let printChild (content:string, lvars:LocalVariable list) (sNestedContent:string option) = 
        match sNestedContent with
        | None  -> content, lvars
        | Some c-> 
            match l with
            | BAst.C        -> equal_c.JoinItems content sNestedContent, lvars
            | BAst.Ada      -> equal_a.JoinItems content sNestedContent, lvars
    let rec printChildren children : Option<string*list<LocalVariable>> = 
        match children with
        |[]     -> None
        |x::xs  -> 
            let aaa = printChildren xs
            match printChildren xs with
            | None                          -> Some (printChild x  None)
            | Some (childrenCont, lvars)    -> 
                let content, lv = printChild x  (Some childrenCont)
                Some (content, lv@lvars)
        
    let childrenConent =   children |> List.filter(fun c -> not c.acnInsertetField) |> List.choose(fun c -> c.isEqualBodyStats childAccess v1 v2 )  
    printChildren childrenConent




let isEqualBodyChoiceChild  (choiceTypeDefName:string) (l:BAst.ProgrammingLanguage) (o:CAst.ChChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let sInnerStatement, lvars = 
        let p1,p2 =
            match l with
            | BAst.C    ->
                (v1 + childAccess + o.c_name), (v2 + childAccess + o.c_name)
            | BAst.Ada  ->
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
    | BAst.C         -> 
        equal_c.isEqual_Choice_Child o.presentWhenName sInnerStatement, lvars
    | BAst.Ada       ->
        equal_a.isEqual_Choice_Child o.presentWhenName sInnerStatement, lvars

let isEqualBodyChoice  (typeDefinition:TypeDefinitionCommon) (l:BAst.ProgrammingLanguage) (children:ChChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let childrenConent,lvars =   
        children |> 
        List.map(fun c -> 
            match l with
            | BAst.C    ->
                c.isEqualBodyStats "." (v1+childAccess+"u") (v2+childAccess+"u") 
            |BAst.Ada   ->
                c.isEqualBodyStats "." v1 v2 
        )  |>
        List.unzip
    let lvars = lvars |> List.collect id
    match l with
    |BAst.C   -> Some(equal_c.isEqual_Choice v1 v2 childAccess childrenConent, lvars)
    |BAst.Ada -> Some(equal_a.isEqual_Choice v1 v2 typeDefinition.name childrenConent, lvars)


let getEqualFuncName (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_Equal"))

let createNullTypeEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.NullType) =
    {
        EqualFunction.isEqualFuncName  = None
        isEqualBody                    = EqualBodyExpression (fun  v1 v2 -> None)
        isEqualFunc                    = None
        isEqualFuncDef                 = None
    }    

let createEqualFunction_primitive (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) isEqualBody stgMacroFunc stgMacroDefFunc =
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
        isEqualFunc                    = isEqualFunc
        isEqualFuncDef                 = isEqualFuncDef
    }    

let stgPrintEqualPrimitive = function
    | BAst.C    -> equal_c.PrintEqualPrimitive
    | BAst.Ada  -> equal_a.PrintEqualPrimitive

let stgMacroPrimDefFunc = function
    | BAst.C    -> equal_c.PrintEqualDefintionPrimitive
    | BAst.Ada  -> equal_a.PrintEqualDefintion

let stgMacroCompDefFunc = function
    | BAst.C    -> equal_c.PrintEqualDefintionComposite
    | BAst.Ada  -> equal_a.PrintEqualDefintion

let createIntegerEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l)

let createRealEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l)

let createBooleanEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l)

let createEnumeratedEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody         = EqualBodyExpression (isEqualBodyPrimitive l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l)

let createStringEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.StringType) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody = EqualBodyExpression (isEqualBodyString l)
    createEqualFunction_primitive r l o.tasInfo typeDefinition isEqualBody (stgPrintEqualPrimitive l) (stgMacroPrimDefFunc l)


let createOctetOrBitStringEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) isEqualBody stgMacroDefFunc =
    let isEqualFuncName     = getEqualFuncName r l tasInfo
    let topLevAcc, val1, val2 =  match l with | BAst.C -> "->", "pVal1", "pVal2" | BAst.Ada -> ".", "val1", "val2"
    let    isEqualFunc, isEqualFuncDef                   = 
            match isEqualFuncName with
            | None              -> None, None
            | Some funcName     -> 
                match isEqualBody topLevAcc val1 val2 with
                | Some (funcBody,_) -> 
                    match l with
                    | BAst.C    -> Some (equal_c.PrintEqualOctBit funcName typeDefinition.name funcBody), Some (stgMacroDefFunc funcName typeDefinition.name)
                    | BAst.Ada  -> Some (equal_a.PrintEqualPrimitive funcName typeDefinition.name funcBody), Some (stgMacroDefFunc funcName typeDefinition.name)
                | None     -> None, None
    {
        EqualFunction.isEqualFuncName  = isEqualFuncName
        isEqualBody                    = EqualBodyExpression (isEqualBody ".")
        isEqualFunc                    = isEqualFunc
        isEqualFuncDef                 = isEqualFuncDef
    }    

let createOctetStringEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.OctetString) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody = isEqualBodyOctetString l (BigInteger o.minSize) (BigInteger o.maxSize)
    createOctetOrBitStringEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l)

let createBitStringEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.BitString) (typeDefinition:TypeDefinitionCommon) =
    let isEqualBody = isEqualBodyBitString l (BigInteger o.minSize) (BigInteger o.maxSize)
    createOctetOrBitStringEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l)


let createCompositeEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) isEqualBody stgMacroDefFunc =
    let isEqualFuncName     = getEqualFuncName r l tasInfo
    let topLevAcc, val1, val2 =  match l with | BAst.C -> "->", "pVal1", "pVal2" | BAst.Ada -> ".", "val1", "val2"
    let isEqualFunc, isEqualFuncDef = 
            match isEqualFuncName with
            | None              -> None, None
            | Some funcName     -> 
                match isEqualBody topLevAcc val1 val2 with
                | Some (funcBody, lvars) -> 
                    let lvars = lvars |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                    match l with
                    | BAst.C    -> Some (equal_c.PrintEqualComposite funcName typeDefinition.name funcBody lvars), Some (stgMacroDefFunc funcName typeDefinition.name)
                    | BAst.Ada  -> Some (equal_a.PrintEqualComposite funcName typeDefinition.name funcBody lvars), Some (stgMacroDefFunc funcName typeDefinition.name)
                | None     -> None, None
    {
        EqualFunction.isEqualFuncName  = isEqualFuncName
        isEqualBody                    = EqualBodyStatementList (isEqualBody ".")
        isEqualFunc                    = isEqualFunc
        isEqualFuncDef                 = isEqualFuncDef
    }    

let createSequenceOfEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.SequenceOf) (typeDefinition:TypeDefinitionCommon) (childType:Asn1Type) =
    let isEqualBody         = isEqualBodySequenceOf childType o l
    createCompositeEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l)

let createSequenceEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Sequence) (typeDefinition:TypeDefinitionCommon) (children:SeqChildInfo list) =
    let isEqualBody         = isEqualBodySequence l children
    createCompositeEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l)

let createChoiceEqualFunction (r:CAst.AstRoot) (l:BAst.ProgrammingLanguage) (o:CAst.Choice) (typeDefinition:TypeDefinitionCommon) (children:ChChildInfo list) =
    let isEqualBody         = isEqualBodyChoice typeDefinition l children
    createCompositeEqualFunction r l o.tasInfo typeDefinition isEqualBody (stgMacroCompDefFunc l)
