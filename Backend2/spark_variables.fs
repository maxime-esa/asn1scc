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

module spark_variables

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open Asn1Values



let GetRealVarName (str:string) =
    "MINUS" + str.Replace('.','_').Replace("-","_minus_").Replace("+","_plus_").Replace("__","_")

let printRealValue (vl:double) =
    match System.Double.IsInfinity vl with
    | true  -> if vl < 0.0 then "adaasn1rtl.MINUS_INFINITY" else "adaasn1rtl.PLUS_INFINITY"
    | false -> sv.PrintRealValue vl


let PrintRealValueAux (a:double) =
    match a<0.0 with
    | false -> printRealValue a
    | true  -> GetRealVarName (printRealValue a)



let GetTasNameByKind kind (m:Asn1Module) (r:AstRoot) = 
    match kind with
    |Integer                            -> ss.Declare_Integer()
    |ReferenceType(modName, tasName, _)    -> 
        match m.Name.Value = modName.Value with
        | true  ->  Ast.GetTasCName tasName.Value r.TypePrefix
        | false ->  (ToC modName.Value) + "." + (Ast.GetTasCName tasName.Value r.TypePrefix)
    |Boolean                            -> ss.Declare_BOOLEAN()
    |Real                               -> ss.Declare_REAL()
    |NullType                           -> ss.Declare_NULL()
    |_          -> raise(BugErrorException (sprintf "%A tt cannot appear inline" kind))




let rec PrintAsn1Value (v:Asn1Value) bChoicesInline bPrintRealNegsAsStrings (t:Asn1Type) (tasName:string, dummy:int) (m:Asn1Module) (r:AstRoot) = 
//    let tActual = Ast.GetActualTypeAllConsIncluded t r
//    let sTasName = GetTasCName tasName r.TypePrefix
    let ToC (str:string) =  str.Replace('-','_')
    let sTasName = tasName 

    match v.Kind, t.Kind with
//    | ChValue(altName,altVal), ReferenceType(modName,tsName)     -> 
//        match bChoicesInline with
//        | true  -> 
//            let baseType = Ast.GetBaseTypeConsIncluded t r
//            PrintAsn1Value v bChoicesInline bPrintRealNegsAsStrings baseType (Ast.GetTasCName tsName.Value r.TypePrefix,0)  m r
//        | false ->
//            match (Ast.GetBaseTypeConsIncluded t r).Kind with
//            | Choice(children)  ->
//                let ch = children |> Seq.find(fun c -> c.Name.Value = altName.Value)
//                let chVal = PrintAsn1Value altVal bChoicesInline bPrintRealNegsAsStrings ch.Type (GetTasNameByKind ch.Type.Kind r) m r
//                let ret = sv.PrintChoiceValue_setters sTasName ch.CName chVal
//                match m.Name.Value = modName.Value with
//                | true -> ret
//                | false -> (ToC modName.Value) + "." + ret
//            | _                                         -> raise(BugErrorException "Invalid Compination")
    |_,ReferenceType(modName,tsName, _)           ->
        let baseType = Ast.GetBaseTypeConsIncluded t r
        let newTasName = match modName.Value = m.Name.Value with
                         | true -> Ast.GetTasCName tsName.Value r.TypePrefix
                         | false -> (ToC modName.Value) + "." + Ast.GetTasCName tsName.Value r.TypePrefix
        PrintAsn1Value v bChoicesInline bPrintRealNegsAsStrings baseType (newTasName,0)  m r
    |IntegerValue(a), Integer                   -> sv.PrintIntValue a.Value
    |IntegerValue(a), Real                      -> if bPrintRealNegsAsStrings then PrintRealValueAux (double a.Value) else printRealValue (double a.Value)
    |RealValue(a), Real                         -> if bPrintRealNegsAsStrings then PrintRealValueAux a.Value else printRealValue a.Value
    |RefValue(modName,vasName), Enumerated(items)   -> 
        let enmItem = items |> Seq.find(fun x -> x.Name.Value = vasName.Value)
        match modName.Value = m.Name.Value with
        | true      -> sv.PrintEnumValue (enmItem.CEnumName r Spark)
        | false     -> (ToC modName.Value) + "." + (sv.PrintEnumValue (enmItem.CEnumName r Spark))
    |RefValue(modName,vasName), _               -> 
        let vas = (r.GetModuleByName modName).ValueAssignments |> Seq.find(fun x -> x.Name.Value = vasName.Value)
        match modName.Value = m.Name.Value with
        | true      -> sv.PrintRefValue1 vas.ada_name
        | false     -> sv.PrintRefValue2 (ToC modName.Value) vas.ada_name
    |StringValue(a), IA5String
    |StringValue(a), NumericString              -> 
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let arrNuls = [0I..max-(BigInteger a.Value.Length)]|>Seq.map(fun x -> sv.PrintStringValueNull())
        sv.PrintStringValue (a.Value.Replace("\"","\"\"")) arrNuls
    |BooleanValue(a), Boolean                   -> sv.PrintBooleanValue a.Value
    |OctetStringValue(bytes), BitString         -> PrintAsn1Value (Ast.ConvertOctetStringValue_to_BitStringValue v) bChoicesInline bPrintRealNegsAsStrings t (tasName,dummy) m r
    |OctetStringValue(bytes), OctetString       ->
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let arBytes = bytes |> Seq.map(fun a -> a.Value) 
        sv.PrintOctetStringValue (ToC sTasName) (min=max) arBytes (BigInteger bytes.Length)
    | BitStringValue(bitVal), BitString -> 
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let arBits = bitVal.Value.ToCharArray() |> Array.map(fun x -> x.ToString())
        sv.PrintBitStringValue (ToC sTasName) (min=max) arBits (BigInteger arBits.Length)
    | BitStringValue(bitVal), OctetString ->    PrintAsn1Value (Ast.ConvertBitStringValue_to_OctetStringValue v) bChoicesInline bPrintRealNegsAsStrings t (tasName,dummy) m r
    |  SeqOfValue(childValues), SequenceOf(childType)    -> 
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let childTasName = GetTasNameByKind childType.Kind m r
        let arrChVals = childValues |> Seq.map(fun x-> PrintAsn1Value x bChoicesInline bPrintRealNegsAsStrings childType (childTasName,0) m r )    
        let defValue = GetDefaultValueByType childType m r
        let sDefValue = PrintAsn1Value defValue bChoicesInline bPrintRealNegsAsStrings childType (childTasName,0) m r
        sv.PrintSequenceOfValue (ToC sTasName) (min=max) (BigInteger (Seq.length childValues)) arrChVals sDefValue
    | SeqValue(childVals), Sequence(children)   ->
        let optChildren = seq {
            for ch in children |> Seq.filter(fun c -> c.Optionality.IsSome) do
                match ch.Optionality, childVals |> Seq.tryFind(fun (chName, _)  -> chName.Value = ch.Name.Value) with
                | _,Some(_)             -> yield sv.PrintSequenceValue_child_exists (ch.CName ProgrammingLanguage.Spark) "1"
                | Some(Default(_)),_    -> yield sv.PrintSequenceValue_child_exists (ch.CName ProgrammingLanguage.Spark) "1"
                | _,None                -> yield sv.PrintSequenceValue_child_exists (ch.CName ProgrammingLanguage.Spark) "0"  } 
        let arrChildren = seq {
            for ch in children  do
                match childVals |> Seq.tryFind(fun (chName, _)  -> chName.Value = ch.Name.Value) with
                | Some(chName, chVal)       -> yield sv.PrintSequenceValueChild (ch.CName ProgrammingLanguage.Spark) (PrintAsn1Value chVal bChoicesInline bPrintRealNegsAsStrings ch.Type (GetTasNameByKind ch.Type.Kind m r, 0) m r)
                | None                      -> 
                    match ch.Optionality with
                    |Some(Default(defVal))  ->  yield sv.PrintSequenceValueChild (ch.CName ProgrammingLanguage.Spark) (PrintAsn1Value defVal bChoicesInline bPrintRealNegsAsStrings ch.Type (GetTasNameByKind ch.Type.Kind m r, 0) m r)
                    |Some(Optional)         ->  
                        let initVal = GetDefaultValueByType ch.Type m r 
                        yield sv.PrintSequenceValueChild (ch.CName ProgrammingLanguage.Spark) (PrintAsn1Value initVal bChoicesInline bPrintRealNegsAsStrings ch.Type (GetTasNameByKind ch.Type.Kind m r, 0) m r)
                    |_                      -> () } |> Seq.toList
        let allChildren = match Seq.isEmpty optChildren with
                          | true     -> arrChildren
                          | false    -> arrChildren @ [sv.PrintSequenceValue_Exists (ToC sTasName) optChildren]
        sv.PrintSequenceValue (ToC sTasName) allChildren
    | ChValue(altName,altVal), Choice(children)     -> 
        let ch = children |> Seq.find(fun c -> c.Name.Value = altName.Value)
        let chVal = PrintAsn1Value altVal bChoicesInline bPrintRealNegsAsStrings ch.Type (GetTasNameByKind ch.Type.Kind m r, 0) m r
        match bChoicesInline with
        | true  -> sv.PrintChoiceValue  (ToC sTasName) (ch.CName ProgrammingLanguage.Spark) chVal (ch.CName_Present Spark)
        | false -> sv.PrintChoiceValue_setters (ToC sTasName) (ch.CName ProgrammingLanguage.Spark) chVal
    | NullValue, NullType                           -> "0"
    | _                                         -> raise(BugErrorException "Invalid combination")




let rec PrintValue (v:Asn1Value) (t:ConstraintType) (tasName:string) (m:Asn1Module)  (r:AstRoot)=
    let tActual = Ast.GetActualTypeAllConsIncluded t.Type r
    match t with
    | Same(_) -> PrintAsn1Value v true true t.Type (tasName,1) m r
    | LengthOf(_) -> 
        match v.Kind with
        |IntegerValue(a)               -> sv.PrintIntValue a.Value
        |RefValue(modName,vasName)     -> 
            match m.Name.Value = modName.Value with
            | true  -> sv.PrintRefValue_lengthOf (ToC vasName.Value)
            | false -> sv.PrintRefValue_lengthOf ((ToC modName.Value) + "." + (ToC vasName.Value))
        | _                            -> raise(BugErrorException "Invalid combination type/value")
    | AlphabetOf(_) ->
        match v.Kind with
        | StringValue(a)               -> 
            match a.Value.Length with
            | 1  -> sv.PrintStringValueChar a.Value
            | _  -> sv.PrintStringValue (a.Value.Replace("\"","\"\"")) []
        | RefValue(modName,vasName)     -> PrintValue (Ast.GetActualValue modName vasName r)  t tasName m r
        | _                             -> raise(BugErrorException "Invalid combination type/value")
