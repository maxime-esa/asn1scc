(*
* Copyright (c) 2008-2012 Semantix and (c) 2012-2015 Neuropublic
*
* This file is part of the ASN1SCC tool.
*
* Licensed under the terms of GNU General Public Licence as published by
* the Free Software Foundation.
*
*  For more informations see License.txt file
*)

module c_validate

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open c_utils




let rec PrintTypeContraint (t:ConstraintType) (path:list<string>) (c:Asn1Constraint) alphaName (m:Asn1Module) (r:AstRoot) = 
    let p = GetConstraintTypeAccessPath path  t r 
    let tasName = path.Tail.Head
    match c with
    | SingleValueContraint(v)     -> 
        match t with
        | AlphabetOf(_) -> 
            match (GetValueAstring v r).Length with
            | 1     -> c_src.SingleValContraint p (c_variables.PrintValue v t tasName m r)
            | _     -> c_src.stringContainsChar (c_variables.PrintValue v t tasName m r) p
        | _             -> 
            match t with
            |Same(actType)  ->
                let unamevar = Ast.GetValueID v
                match actType.Kind with
                | BitString -> 
                    match (GetTypeUperRange t.Type.Kind t.Type.Constraints r) with
                    | Concrete(min, max) when min = max -> c_src.SingleValContraint_bitString_fixedSize p unamevar max
                    | Concrete(min, max)                -> c_src.SingleValContraint_bitString_varSize p unamevar
                    | _                                 -> raise(BugErrorException "")
                | OctetString ->
                    match (GetTypeUperRange t.Type.Kind t.Type.Constraints r) with
                    | Concrete(min, max) when min = max -> c_src.SingleValContraint_octetString_fixedSize p unamevar max
                    | Concrete(min, max)                -> c_src.SingleValContraint_octetString_varSize p unamevar
                    | _                                 -> raise(BugErrorException "")
                | _             -> c_src.SingleValContraint p (c_variables.PrintValue v t tasName m r)
            | _             -> c_src.SingleValContraint p (c_variables.PrintValue v t tasName m r)
    | RangeContraint(a,b,minIsIn,maxIsIn)         -> 
        let tActual = Ast.GetActualTypeAllConsIncluded t.Type r
        match tActual.Kind with
        | Integer ->
            let intType = Ast.getIntType (uPER.GetTypeUperRange tActual.Kind tActual.Constraints r)
            match intType with
            | UINT when minIsIn -> 
                match a.Kind with
                | IntegerValue(a) when a.Value = 0I -> c_src.RangeContraint_MIN_val p (c_variables.PrintValue b t tasName m r) maxIsIn
                | _                                 -> c_src.RangeContraint p (c_variables.PrintValue a t tasName m r) (c_variables.PrintValue b t tasName m r) minIsIn maxIsIn    
            | _                 -> c_src.RangeContraint p (c_variables.PrintValue a t tasName m r) (c_variables.PrintValue b t tasName m r) minIsIn maxIsIn
        | _             -> c_src.RangeContraint p (c_variables.PrintValue a t tasName m r) (c_variables.PrintValue b t tasName m r) minIsIn maxIsIn
    | RangeContraint_val_MAX(a,minIsIn)   -> 
        let tActual = Ast.GetActualTypeAllConsIncluded t.Type r
        match tActual.Kind with
        | Integer ->
            let intType = Ast.getIntType (uPER.GetTypeUperRange tActual.Kind tActual.Constraints r)
            match intType with
            | UINT when minIsIn -> 
                match a.Kind with
                | IntegerValue(a) when a.Value = 0I -> "TRUE"
                | _                                 -> c_src.RangeContraint_val_MAX p (c_variables.PrintValue a t tasName m r) minIsIn
            | _                                     -> c_src.RangeContraint_val_MAX p (c_variables.PrintValue a t tasName m r) minIsIn
        | _                                         -> c_src.RangeContraint_val_MAX p (c_variables.PrintValue a t tasName m r) minIsIn
    | RangeContraint_MIN_val(b,maxIsIn)   -> c_src.RangeContraint_MIN_val p (c_variables.PrintValue b t tasName m r) maxIsIn
    | RangeContraint_MIN_MAX      -> raise(BugErrorException "This constraint should have been removed")
    | SizeContraint(inCon)        -> PrintTypeContraint  (LengthOf t.Type) path inCon alphaName m r
    | AlphabetContraint(inCon)    -> c_src.callAlphaFunc alphaName p
    | UnionConstraint(c1, c2,_)     -> c_src.OR_Constraint (PrintTypeContraint t path c1 alphaName m r) (PrintTypeContraint t path c2 alphaName m r)
    | IntersectionConstraint(c1,c2)-> c_src.AND_Constraint (PrintTypeContraint t path c1 alphaName m r) (PrintTypeContraint t path c2 alphaName m r)
    | AllExceptConstraint(c1)      -> c_src.AllExceptConstraint (PrintTypeContraint t path c1 alphaName m r)
    | ExceptConstraint(c1,c2)      -> c_src.ExceptConstraint (PrintTypeContraint t path c1 alphaName m r) (PrintTypeContraint t path c2 alphaName m r)
    | RootConstraint(c1)           -> (PrintTypeContraint t path c1 alphaName m r)
    | RootConstraint2(c1,c2)       -> c_src.OR_Constraint (PrintTypeContraint t path c1 alphaName m r) (PrintTypeContraint t path c2 alphaName m r)
    | TypeInclusionConstraint(modName,tasName) ->
        let actualType = GetActualTypeByNameAllConsIncluded modName tasName r
        let arrCons = actualType.Constraints |> Seq.map(fun c -> PrintTypeContraint t path c alphaName m r)
        c_src.PrintMultipleConstraints arrCons
    | WithComponentConstraint(_)    -> raise(BugErrorException "Unexpected Constraint")
    | WithComponentsConstraint(_)   -> raise(BugErrorException "Unexpected Constraint")


let PrintAlphaFunction (t:ConstraintType) (path:list<string>) (cons:list<Asn1Constraint>) (m:Asn1Module) alphaName (r:AstRoot) = 
    let arrCons = cons |> List.map(fun c -> PrintTypeContraint t path c alphaName m r)
    match (GetTypeConstraintsErrorCode cons path r) with
    | None  -> raise(BugErrorException "This type does not have constraints, so no ErrorCode exists")
    | Some(errCodeName) ->    c_src.Print_AlphabetCheckFunc alphaName arrCons 
    

let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
    match t.Kind with
    | SequenceOf(child) -> 
        let nCurLevel =  (Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1
        let nAllocatedLevel = state |> Seq.filter(fun lv -> match lv with SEQUENCE_OF_INDEX(_)->true |_ -> false )|>Seq.length
        if nCurLevel>nAllocatedLevel then
            (SEQUENCE_OF_INDEX (nCurLevel))::state
        else
            state
    | _             -> state

let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) =
    let lvs = VisitType t [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []
    let emitLocalVariable  = function
        | SEQUENCE_OF_INDEX(i) -> c_src.Emit_local_variable_SQF_Index (BigInteger i) 
        | _                 -> ""
    lvs |> Seq.map emitLocalVariable


let EmitTypeBodyBase (t:ConstraintType) (path:list<string>)  (m:Asn1Module) (r:AstRoot)  =
    let alphaFuncName = ToC ((path |> Seq.skip 1).StrJoin("_").Replace("#","elem"))
    let arrCons = t.Type.Constraints |> Seq.map(fun c -> PrintTypeContraint t path c alphaFuncName m r)
    match (GetTypeConstraintsErrorCode t.Type.Constraints path r) with
    | None  -> c_src.Emit_fixedSize_constraint()
    | Some(errCodeName) ->    c_src.Emit_type  arrCons errCodeName        



let rec EmitTypeBody (t:ConstraintType) (path:list<string>)  (m:Asn1Module) (r:AstRoot)  =
    let p = GetConstraintTypeAccessPath path t r 
    let SizeableTypeUperRange (t:Asn1TypeKind) cons=
            match (GetTypeUperRange t cons r) with
            |Concrete(min, max)        -> min,max
            |_                         -> raise(BugErrorException "SEQUENCE OF or OCTET STRING etc has no constraints")
    match t.Type.Kind with
    |Sequence(children) ->
        let itemsToCheck = 
            seq {
                for c in children |> Seq.filter(fun x-> not(x.AcnInsertedField)) do
                    match c.Optionality with
                    | None                              -> yield (0, c)      // 0 = check component
                    | Some(Optional) | Some(Default(_)) -> yield (1, c)      // 1 = check optional compoent
                    | Some(AlwaysPresent)               -> yield (2, c)      // 2 = check component is always present
                                                           yield (0, c) 
                    | Some(AlwaysAbsent)                -> yield (3, c)      // 3 = check component is always absent
            } |> Seq.toList

        let printChild (k:int, c:ChildInfo) sNestedContent = 
            let chKey = (path@[c.Name.Value])
            let errCode = match Ast.GetChildInfoErrorCode c  chKey r with
                          |Some(s)  -> s
                          |None     -> ""
            let sChildBody = EmitTypeBody (Same c.Type) chKey m r
            let sChildName = c.CName ProgrammingLanguage.C
            let content = 
                match k with
                | 0     -> sChildBody 
                | 1     -> c_src.Emit_sequence_optional_component p sChildName sChildBody
                | 2     -> c_src.Emit_sequence_check_component_is_always_present_or_absent p sChildName 1I errCode
                | 3     -> c_src.Emit_sequence_check_component_is_always_present_or_absent p sChildName 0I errCode
                | _     -> raise(BugErrorException "")
            c_src.JoinItems content sNestedContent

        let rec printChildren  = function
            |[]     -> null
            |x::xs  -> printChild x  (printChildren xs)

        printChildren itemsToCheck
    |Choice(children)  -> 
        let printChild (c:ChildInfo) = 
            let chKey = (path@[c.Name.Value])
            let errCode = match Ast.GetChildInfoErrorCode c  chKey r with
                          |Some(s)  -> s
                          |None     -> ""
            let sChildBody = EmitTypeBody (Same c.Type) chKey m r
            c_src.Emit_choice_child (c.CName_Present C) sChildBody

        let arrChildren = children |> List.map printChild 
        let sTasName = GetTasCName (path |> Seq.nth 1) r.TypePrefix
        c_src.Emit_choice p arrChildren (GetChoiceErrorCode path r)
    |SequenceOf(child) -> 
        let min, max = SizeableTypeUperRange t.Type.Kind t.Type.Constraints
        let sizeCons = match min=max with
                       | false  -> EmitTypeBodyBase  (LengthOf t.Type) path m r
                       | true   -> c_src.Emit_fixedSize_constraint()
        let getIndexNameByPath (path:string list) =
            "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
        let sSizeCon = sizeCons
        let sChildBody = EmitTypeBody (Same child) (path@["#"]) m r
        let sI = getIndexNameByPath path
            
        c_src.Emit_sequence_of sI p max sSizeCon sChildBody (min=max) 
    |ReferenceType(modName,tasName, _) -> 
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        let ptr = GetConstraintTypeAccessPathPtr path t r
        match modName.Value = m.Name.Value with
        | true  -> c_src.Emit_Reference1 ptr tsName
        | false -> c_src.Emit_Reference2 ptr (ToC modName.Value) tsName
    |_                  -> EmitTypeBodyBase  t path m r





let CollectAlphaFuncs (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) =
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<string>) = 
        let alphaCons = t.Constraints |> List.choose(fun c -> match c with |AlphabetContraint(x) -> Some x |_ -> None )
        let alphaFuncName = ToC ((path |> Seq.skip 1).StrJoin("_").Replace("#","elem"))
        let alphaFuncs = 
            match alphaCons with
            | []    -> []
            | _     -> [PrintAlphaFunction (AlphabetOf t) path alphaCons m alphaFuncName r]
        state@alphaFuncs
    VisitType tas.Type [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []

let PrintTypeAss (tas:TypeAssignment) (m:Asn1Module) (f:Asn1File) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) = 
    let sName = tas.GetCName r.TypePrefix
    let t = RemoveWithComponents tas.Type r
    let sStar = (TypeStar tas.Type r)
    let localVars = CollectLocalVars t tas m r
    let sContent = EmitTypeBody (Same t) [m.Name.Value; tas.Name.Value] m r
    let arrsAlphaCheckFunctions = CollectAlphaFuncs tas m r
    c_src.PrintIsConstraintValid sName sStar localVars sContent arrsAlphaCheckFunctions
