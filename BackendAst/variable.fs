module variable



open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
//open c_utils
open BackendAst


let rec getBackendPrimaryNumericExpression (v:Asn1Value) (t:Asn1Type)  (m:Asn1Module) (r:AstRoot) : BackendPrimaryNumericExpression= 
    match v.Kind, t.Kind with
    |_,ReferenceType(modName,tsName, _)           ->
        let baseType = Ast.GetBaseTypeConsIncluded t r
        let newTasName = match modName.Value = m.Name.Value with
                         | true -> Ast.GetTasCName tsName.Value r.TypePrefix
                         | false -> (ToC modName.Value) + "." + Ast.GetTasCName tsName.Value r.TypePrefix
        getBackendPrimaryNumericExpression v  baseType  m r
    |IntegerValue(a), Integer                   -> IntegerLiteral (a.Value, "")
    |IntegerValue(a), Real                      -> RealLiteral (double a.Value)
    |RealValue(a), Real                         -> RealLiteral a.Value
    | _                                         -> raise(BugErrorException "Invalid Combination int function getBackendPrimaryNumericExpression()")


let rec getBackendPrimaryExpression (v:Asn1Value) (t:Asn1Type)  (m:Asn1Module) (r:AstRoot) : BackendPrimaryExpression= 
    match v.Kind, t.Kind with
    |_,ReferenceType(modName,tsName, _)           ->
        let baseType = Ast.GetBaseTypeConsIncluded t r
        let newTasName = match modName.Value = m.Name.Value with
                         | true -> Ast.GetTasCName tsName.Value r.TypePrefix
                         | false -> (ToC modName.Value) + "." + Ast.GetTasCName tsName.Value r.TypePrefix
        getBackendPrimaryExpression v  baseType  m r
    |IntegerValue(a), Integer                   -> BackendPrimaryNumericExpression (IntegerLiteral (a.Value, ""))
    |IntegerValue(a), Real                      -> BackendPrimaryNumericExpression (RealLiteral (double a.Value))
    |RealValue(a), Real                         -> BackendPrimaryNumericExpression (RealLiteral a.Value)
    |RefValue(modName,vasName), Enumerated(items)   -> 
        let enmItem = items |> Seq.find(fun x -> x.Name.Value = vasName.Value)
        EnumeratedTypeLiteral (enmItem.CEnumName r C)
    |RefValue(modName,vasName), _               -> 
        ReferenceToVas(modName.Value, vasName.Value )
    |StringValue(a), IA5String
    |StringValue(a), NumericString              -> 
        StringLiteral (a.Value.Replace("\"","\"\"")) 
    |BooleanValue(a), Boolean                   -> BooleanLiteral a.Value
    |OctetStringValue(bytes), _                 -> raise(BugErrorException "Invalid Case: OctetStringValue")
    |BitStringValue(bitVal), _                  -> raise(BugErrorException "Invalid Case: BitStringValue")
    | SeqOfValue(childValues), _                -> raise(BugErrorException "Invalid Case: SeqOfValue")
    | SeqValue(childVals), _                    -> raise(BugErrorException "Invalid Case: SeqValue")
    | ChValue(altName,altVal), Choice(children) -> raise(BugErrorException "Invalid Case: ChValue")
    | NullValue, NullType                       -> NullTypeLiteral
    | _                                         -> raise(BugErrorException "Invalid Combination in funcion getBackendPrimaryExpression()")


