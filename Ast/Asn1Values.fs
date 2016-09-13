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

module Asn1Values

open System.Numerics
open FsUtils
open Ast
open uPER






let rec GetDefaultValueByType (maxSize:BigInteger option) (t:Asn1Type) (m:Asn1Module) (r:AstRoot) = 
    let getVal vKind = { Asn1Value.Kind = vKind; Location = emptyLocation}
    let upperBound (min:BigInteger) =
        match maxSize with
        | None          -> min
        | Some maxSize  -> if maxSize < min then maxSize else min

    match t.Kind with
    | Integer   ->
        match (GetTypeUperRange t.Kind t.Constraints r) with
        |Concrete(a, _)         
        |NegInf(a)              
        |PosInf(a)             -> getVal (IntegerValue (loc a))
        |Full                   
        |Empty                 -> getVal (IntegerValue (loc 0I))
    | Real     ->                 getVal (RealValue (loc 0.0))
    | IA5String | NumericString ->
        let chr = GetTypeUperRangeFrom(t.Kind,t.Constraints, r) |> Seq.filter(fun c -> not (System.Char.IsControl c)) |> Seq.head
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        getVal (StringValue (loc (System.String(chr,int min)) ))
    | OctetString               ->
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r

        let chVals = 
            [1I .. (upperBound min)] |> List.map(fun i -> ByteLoc.ByValue 0uy)
        getVal (OctetStringValue chVals)
    | BitString                 ->
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        getVal (BitStringValue (loc (System.String('0',int min)) ))
    | Boolean                   ->getVal (BooleanValue (loc false))
    | Enumerated(items)         ->
        match items |> Seq.tryFind (fun itm -> 
            let checkCon c = CheckAsn1.IsValueAllowed c (getVal (RefValue (m.Name, itm.Name) )) true r
            t.Constraints |> List.fold(fun state cn -> state && (checkCon cn)) true) with
        | Some itm -> getVal (RefValue (m.Name, itm.Name))
        | None     -> 
            System.Console.Error.WriteLine("Warning File:{0}, Line:{1}: No initial value for enumerated type could be obtained.\nPossibly the ASN.1 enumerated type has been constraint to void. The generated code may not compile or crash in runtime.", t.Location.srcFilename, t.Location.srcLine)
            getVal (RefValue (m.Name, items.Head.Name))
    | SequenceOf(child)         ->
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let chVals = [1I .. (upperBound min)] |> List.map(fun i -> GetDefaultValueByType maxSize child m r )
        getVal (SeqOfValue chVals)
    | Choice(children)          ->
        let fc = children.Head
        getVal (ChValue (fc.Name, GetDefaultValueByType maxSize fc.Type m r))
    | Sequence(children)        ->
        let getChildValue (c:ChildInfo) =
            match c.Optionality with
            |Some(Default(v))   -> c.Name, v
            | _                 -> c.Name, (GetDefaultValueByType maxSize c.Type m r)
        let chVals = children |> List.filter(fun x-> not x.AcnInsertedField) |> List.map getChildValue
        getVal (SeqValue chVals)
    | NullType                  -> getVal NullValue
    |ReferenceType(modName,tasName, _) ->
        let newModule = r.GetModuleByName modName
        let baseType = Ast.GetActualTypeAllConsIncluded t r
        GetDefaultValueByType maxSize baseType newModule r