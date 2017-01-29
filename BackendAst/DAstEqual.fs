module DAstEqual
open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst


let isEqualBodyPrimitive (l:ProgrammingLanguage) v1 v2 =
    match l with
    | C         -> Some (sprintf "%s == %s" v1 v2  , [])
    | Ada       -> Some (sprintf "%s = %s" v1 v2   , [])

let isEqualBodyString (l:ProgrammingLanguage) v1 v2 =
    match l with
    | C         -> Some (sprintf "strcmp(%s, %s) == 0" v1 v2  , [])
    | Ada       -> Some (sprintf "%s = %s" v1 v2   , [])

let isEqualBodySequenceOf  (childType:Asn1Type) (o:CAst.SequenceOf)  (l:ProgrammingLanguage) (childAccess: string) v1 v2  =
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

    

let isEqualBodySequenceChild   (l:ProgrammingLanguage) (o:CAst.SeqChildInfo) (newChild:Asn1Type) (childAccess: string) (v1:string) (v2:string)  = 
    let c_name = ToC o.name
    let sInnerStatement = 
        match newChild.isEqualBody with
        | Expression, func  ->  
            match func (v1 + childAccess + c_name) (v2 + childAccess + c_name) with
            | Some (exp, lvars)  -> Some (sprintf "ret %s (%s);" l.AssignOperator exp, lvars)
            | None      -> None
        | Statement,  func   -> func (v1 + childAccess + c_name) (v2 + childAccess + c_name)

    match l with
    | C         -> 
        match sInnerStatement with
        | None                           -> equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name None, []
        | Some (sInnerStatement, lvars)  -> equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name (Some sInnerStatement), lvars
    | Ada       ->
        match sInnerStatement with
        | None                           -> equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name None, []
        | Some (sInnerStatement, lvars)  -> equal_c.isEqual_Sequence_child v1  v2  childAccess o.optionality.IsSome c_name (Some sInnerStatement), lvars


let isEqualBodySequence  (l:ProgrammingLanguage) (children:SeqChildInfo list) (childAccess: string) (v1:string) (v2:string)  = 
    let printChild (c:SeqChildInfo) (sNestedContent:string option) = 
        let content, lvars = c.isEqualBodyStats childAccess v1 v2 
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
        
        
    printChildren (children |> List.filter(fun c -> not c.acnInsertetField))



