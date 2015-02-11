module spark_equal

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils



let rec EmitTypeBody (t:Asn1Type) (path:list<string>)  (m:Asn1Module) (r:AstRoot) (tas:TypeAssignment) =

    //let p1 = GetTypeAccessPathPriv "pVal1" path  r
    let p1 = GetAccessFldPriv "val1" path (Same t) r
    //let p2 = GetTypeAccessPathPriv "pVal2" path  r
    let p2 = GetAccessFldPriv "val2" path (Same t) r
    match t.Kind with
    | Integer           -> si.isEqual_Integer p1 p2
    | Enumerated(_)     -> si.isEqual_Enumerated p1 p2
    | Boolean           -> si.isEqual_Boolean p1 p2
    | Real              -> si.isEqual_Real p1 p2
    | NullType          -> si.isEqual_NullType ()
    | IA5String         -> si.isEqual_IA5String p1 p2
    | NumericString     -> si.isEqual_NumericString p1 p2
    | OctetString       ->
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) when  a=b   -> si.isEqual_OctetString p1 p2 true a
        | Concrete(a,b)             -> si.isEqual_OctetString p1 p2 false a
        | NegInf(_)                 -> raise (BugErrorException("Negative size"))
        | PosInf(_)                 -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full                      -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty                     -> raise (BugErrorException("I do not known how this is handled"))      
    | BitString         ->
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) when  a=b   -> si.isEqual_BitString p1 p2 true a
        | Concrete(a,b)             -> si.isEqual_BitString p1 p2 false a
        | NegInf(_)                 -> raise (BugErrorException("Negative size"))
        | PosInf(_)                 -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full                      -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty                     -> raise (BugErrorException("I do not known how this is handled"))      
    | Choice(children)  ->
        let arrChildre = 
            children |> 
            Seq.map(fun c -> si.isEqual_Choice_Child (c.CName_Present C) 
                                                     (EmitTypeBody c.Type (path@[c.Name.Value]) m r tas))
        si.isEqual_Choice p1 p2 arrChildre (tas.GetCName r.TypePrefix)
    | ReferenceType(md,ts, _)  ->
        //let ptr1 = GetTypeAccessPathPrivPtr "pVal1" path  r
        //let ptr2 = GetTypeAccessPathPrivPtr "pVal2" path  r
        let tsName = Ast.GetTasCName ts.Value r.TypePrefix
        //si.isEqual_ReferenceType ptr1 ptr2 tsName
        si.isEqual_ReferenceType p1 p2 tsName
    | SequenceOf(child)     -> 
        let getIndexNameByPath (path:string list) =
            "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
        let index = getIndexNameByPath path
        let sInnerType = EmitTypeBody child (path@["#"]) m r tas
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) when  a=b   -> si.isEqual_SequenceOf p1 p2 index true a sInnerType
        | Concrete(a,b)             -> si.isEqual_SequenceOf p1 p2 index false a sInnerType
        | NegInf(_)                 -> raise (BugErrorException("Negative size"))
        | PosInf(_)                 -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full                      -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty                     -> raise (BugErrorException("I do not known how this is handled"))
    | Sequence(children)    ->
        let asn1Children = children |> List.filter(fun x -> not x.AcnInsertedField)
        let arrChildren =
            asn1Children |> Seq.map(fun c -> si.isEqual_Sequence_Child p1 p2 c.Optionality.IsSome c.CName)

        si.isEqual_Sequence p1 p2 arrChildren


let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
    match t.Kind with
    | SequenceOf(child) -> 
        let nCurLevel =  (Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1
        let nAllocatedLevel = state |> Seq.filter(fun lv -> match lv with SEQUENCE_OF_INDEX(_)->true |_ -> false )|>Seq.length
        if nCurLevel>nAllocatedLevel then
            SEQUENCE_OF_INDEX(nCurLevel,true)::state
        else
            state
    | _             -> state

let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) =
    let lvs = VisitType t [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []
    let emitLocalVariable  = function
        | SEQUENCE_OF_INDEX (i,b) -> sc.Emit_local_variable_SQF_Index (BigInteger i) b
        | _                 -> ""
    lvs |> Seq.map emitLocalVariable

let PrintTypeAssEqual2 (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) = 
    let sName = tas.GetCName r.TypePrefix
    let t = RemoveWithComponents tas.Type r
    let localVars = CollectLocalVars t tas m r
    let sContent = EmitTypeBody t [m.Name.Value; tas.Name.Value] m r tas
    si.PrintTypeAssignment_Equal sName sContent localVars 


