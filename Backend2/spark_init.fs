module spark_init

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils

type State = {
    nErrorCode:int
}

//    let t = RemoveWithComponents t r


let rec PrintInitValueByType (t:Asn1Type) (tasName:string) (m:Asn1Module) (r:AstRoot) = 
    let sTasName = GetTasCName tasName r.TypePrefix
    let initVal = 
        match t.Kind with
        | SequenceOf(child)         -> 
            let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
            let chVals = [] 
            { Asn1Value.Kind = SeqOfValue []; Location = emptyLocation}
        | _                         -> Asn1Values.GetDefaultValueByType (RemoveWithComponents t r) m r 
    
    let rec PrintAsn1Value (v:Asn1Value) (t:Asn1Type) (tasName:string) (m:Asn1Module) (r:AstRoot) = 
        match v.Kind, t.Kind with
        |  SeqOfValue(childValues), SequenceOf(childType)    -> 
            let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
            let childTasName = spark_variables.GetTasNameByKind childType.Kind m r
            let arrChVals = []    
            let defValue = Asn1Values.GetDefaultValueByType (RemoveWithComponents childType r) m r
            let sDefValue = PrintAsn1Value defValue childType childTasName m r
            sv.PrintSequenceOfValue sTasName (min=max) min arrChVals sDefValue
        | _ -> spark_variables.PrintAsn1Value v false true t (tasName,0) m r
    
    PrintAsn1Value initVal t sTasName m r
    


let PrintChoiceGetters (t:TypeAssignment) (m:Asn1Module) (r:AstRoot)  = 
    match t.Type.Kind with
    |Choice(children) ->
        let sTasName = GetTasCName t.Name.Value r.TypePrefix
        let printChild (c:ChildInfo) =
            let typeDecl,_ = spark_spec.PrintType c.Type [m.Name.Value; t.Name.Value; c.Name.Value] (Some t.Type) (TypeAssignment t,m,r) {spark_spec.State.nErrorCode = 0}
            si.CHOICE_setters_body_child sTasName c.CName typeDecl (c.CName_Present Spark)
        si.CHOICE_setters_body sTasName (children |> Seq.map printChild)
    |_              -> ""
        

let PrintTypeAss (t:TypeAssignment) (m:Asn1Module) (r:AstRoot) (state:State) = 
    let sName = t.GetCName r.TypePrefix
    let hasChoice = IsOrContainsChoice t.Type r
    let init = si.PrintTypeAssignment sName (PrintInitValueByType t.Type t.Name.Value m r) hasChoice
    let sChoice = PrintChoiceGetters t m r 
    sChoice+init,state


let PrintTypeEqualBody (t:Asn1Type) (tasName:string) path (m:Asn1Module) (r:AstRoot) = 
    let p1 = GetAccessFldPriv "val1" path (Same t) r
    let p2 = GetAccessFldPriv "val2" path (Same t) r
    match t.Kind with
    | Integer -> si.isEqual_Integer p1 p2
    | Real -> si.isEqual_Real p1 p2
    | IA5String -> si.isEqual_IA5String p1 p2
    | NumericString -> si.isEqual_NumericString p1 p2
    | OctetString ->
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) when  a=b   -> si.isEqual_OctetString p1 p2 true
        | Concrete(a,b)             -> si.isEqual_OctetString p1 p2 false
        | NegInf(_)                 -> raise (BugErrorException("Negative size"))
        | PosInf(_)                 -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full                      -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty                     -> raise (BugErrorException("I do not known how this is handled"))
    | SequenceOf(_) ->
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) when  a=b   -> si.isEqual_SequenceOf p1 p2 true
        | Concrete(a,b)             -> si.isEqual_SequenceOf p1 p2 false
        | NegInf(_)                 -> raise (BugErrorException("Negative size"))
        | PosInf(_)                 -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full                      -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty                     -> raise (BugErrorException("I do not known how this is handled"))
    | NullType -> si.isEqual_NullType ()
    | Boolean -> si.isEqual_Boolean p1 p2
    | BitString -> 
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) when  a=b   -> si.isEqual_BitString p1 p2 true
        | Concrete(a,b)             -> si.isEqual_BitString p1 p2 false
        | NegInf(_)                 -> raise (BugErrorException("Negative size"))
        | PosInf(_)                 -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full                      -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty                     -> raise (BugErrorException("I do not known how this is handled"))
    | _     -> si.PrimitiveEqual p1 p2

let PrintTypeAssEqual (t:TypeAssignment) (m:Asn1Module) (r:AstRoot)  = 
    let sName = t.GetCName r.TypePrefix
    si.PrintTypeAssignment_Equal sName (PrintTypeEqualBody t.Type t.Name.Value [m.Name.Value; t.Name.Value] m r) 


