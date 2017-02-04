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
    | BAst.Ada       -> Some (equal_c.isEqual_OctetString v1 v2 (sMin = sMax) sMax, [])

let isEqualBodyBitString (l:BAst.ProgrammingLanguage) sMin sMax (childAccess: string) v1 v2 =
    let v1 = sprintf "%s%s" v1 childAccess
    let v2 = sprintf "%s%s" v2 childAccess
    match l with
    | BAst.C         -> Some (equal_c.isEqual_BitString v1 v2 (sMin = sMax) sMax, [])
    | BAst.Ada       -> Some (equal_c.isEqual_BitString v1 v2 (sMin = sMax) sMax, [])

let isEqualBodySequenceOf  (childType:Asn1Type) (o:CAst.SequenceOf)  (l:BAst.ProgrammingLanguage) (childAccess: string) v1 v2  =
    let getInnerStatement i = 
        let childAccesPath v = v + childAccess + "arr" + (l.ArrayAccess i) //"[" + i + "]"
        match childType.isEqualBody with
        | Expression, func  ->  
            match func (childAccesPath v1) (childAccesPath v2) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)       // ret = (boolExp);
            | None      -> None
        | Statement,  func   -> func (childAccesPath v1) (childAccesPath v2)

    let i = sprintf "i%d" (o.id.SeqeuenceOfLevel + 1)
    let lv = SequenceOfIndex (o.id.SeqeuenceOfLevel + 1, None)
    match getInnerStatement i with
    | None when o.minSize = o.maxSize        -> None
    | None                                   ->
        Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) None, lv::[])
    | Some (innerStatement, lvars)           ->
        Some (equal_c.isEqual_SequenceOf v1 v2 childAccess i (o.minSize = o.maxSize) (BigInteger o.minSize) (Some innerStatement), lv::lvars)

    

let isEqualBodySequenceChild   (l:BAst.ProgrammingLanguage) (o:CAst.SeqChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isEqualBody with
        | Expression, func  ->  
            match func (v1 + childAccess + c_name) (v2 + childAccess + c_name) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)
            | None      -> None
        | Statement,  func   -> func (v1 + childAccess + c_name) (v2 + childAccess + c_name)

    match l with
    | BAst.C         -> 
        match sInnerStatement with
        | None  when  o.optionality.IsSome  -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name None, [])
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name (Some sInnerStatement), lvars)
    | BAst.Ada       ->
        match sInnerStatement with
        | None  when  o.optionality.IsSome  -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name None, [])
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name (Some sInnerStatement), lvars)


let isEqualBodySequence  (l:BAst.ProgrammingLanguage) (children:SeqChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let printChild (content:string, lvars:LocalVariable list) (sNestedContent:string option) = 
        match sNestedContent with
        | None  -> content, lvars
        | Some c-> equal_c.JoinItems content sNestedContent, lvars
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




let isEqualBodyChoiceChild   (l:BAst.ProgrammingLanguage) (o:CAst.ChChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isEqualBody with
        | Expression, func  ->  
            match func (v1 + childAccess + c_name) (v2 + childAccess + c_name) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)
            | None      -> None
        | Statement,  func   -> func (v1 + childAccess + c_name) (v2 + childAccess + c_name)

    match l with
    | BAst.C         -> 
        match sInnerStatement with
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_c.isEqual_Choice_Child o.presentWhenName sInnerStatement, lvars)
    | BAst.Ada       ->
        match sInnerStatement with
        | None                              -> None
        | Some (sInnerStatement, lvars)     -> Some (equal_c.isEqual_Choice_Child o.presentWhenName sInnerStatement, lvars)

let isEqualBodyChoice  (l:BAst.ProgrammingLanguage) (children:ChChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let childrenConent,lvars =   
        children |> 
        List.map(fun c -> 
            match c.isEqualBodyStats "." (v1+childAccess+"u") (v2+childAccess+"u") with
            | Some a -> a
            | None   -> sprintf "ret %s TRUE;" l.AssignOperator ,[])  |>
        List.unzip
    let lvars = lvars |> List.collect id
    match l with
    |BAst.C   -> Some(equal_c.isEqual_Choice v1 v2 childAccess childrenConent, lvars)
    |BAst.Ada -> Some(equal_c.isEqual_Choice v1 v2 childAccess childrenConent, lvars)

