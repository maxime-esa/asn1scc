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

module genericBackend

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils

let GetMinMax uperRange =
    match uperRange with
    | Concrete(min, max)      -> min.ToString(), max.ToString()
    | PosInf(a)               -> a.ToString(), "MAX"
    | NegInf(max)             -> "MIN", max.ToString()
    | Full                    -> "MIN", "MAX"
    | Empty                   -> raise(BugErrorException "[genericBackend] GetMinMax error")

let handTypeWithMinMax name uperRange func stgFileName =
    let sMin, sMax = GetMinMax uperRange
    func name sMin sMax (sMin=sMax) stgFileName

let PrintCustomAsn1Value (vas: Ast.ValueAssignment) stgFileName =
    let rec PrintValue (v: Asn1Value) =
        match v.Kind with
        |IntegerValue(v)         -> gen.Print_IntegerValue v.Value stgFileName
        |RealValue(v)            -> gen.Print_RealValue v.Value stgFileName
        |StringValue(v)          -> gen.Print_StringValue v.Value stgFileName
        |BooleanValue(v)         -> if v.Value = true then gen.Print_TrueValue () stgFileName else gen.Print_FalseValue () stgFileName
        |BitStringValue(v)       -> gen.Print_BitStringValue v.Value stgFileName
        |OctetStringValue(v)     -> gen.Print_OctetStringValue (v |> Seq.map(fun x -> x.Value) |> Seq.toArray) stgFileName
        |RefValue(mn,nm)         -> gen.Print_RefValue nm.Value stgFileName
        |SeqOfValue(vals)        -> gen.Print_SeqOfValue (vals |> Seq.map PrintValue |> Seq.toArray) stgFileName
        |SeqValue(vals)          -> gen.Print_SeqValue (vals |> Seq.map(fun (nm, v) -> gen.Print_SeqValue_Child nm.Value (PrintValue v) stgFileName ) |> Seq.toArray) stgFileName
        |ChValue(nm,v)           -> gen.Print_ChValue nm.Value (PrintValue v) stgFileName
        |NullValue               -> gen.Print_NullValue() stgFileName
    PrintValue vas.Value


let PrintContract (tas:Ast.TypeAssignment) (r:AstRoot) (stgFileName:string) =
    let PrintPattern (tas:Ast.TypeAssignment) =
        let t = tas.Type
        match t.Kind with
        | Integer | BitString | OctetString | Real | IA5String | NumericString | SequenceOf(_)     -> gen.TypePatternCommonTypes () stgFileName
        | Boolean | NullType  | Enumerated(_)      | Choice(_)                                     -> null
        | Sequence(children)    ->
            let emitChild (c:ChildInfo) =
                gen.SequencePatternChild c.Name.Value (ToC c.Name.Value) stgFileName
            gen.TypePatternSequence tas.Name.Value (ToC tas.Name.Value) (children |> Seq.map emitChild) stgFileName
        | ReferenceType(_, _, _) -> null
    let rec PrintExpression (t:Asn1Type) (pattern:string) =
        match t.Kind with
        | Integer               -> handTypeWithMinMax pattern (GetTypeUperRange t.Kind t.Constraints r) gen.ContractExprMinMax stgFileName
        | Real                  -> handTypeWithMinMax pattern (GetTypeRange_real t.Kind t.Constraints r) gen.ContractExprMinMax stgFileName
        | OctetString | IA5String | NumericString | BitString -> handTypeWithMinMax pattern (GetTypeUperRange t.Kind t.Constraints r) gen.ContractExprSize stgFileName
        | Boolean
        | NullType
        | Choice(_)
        | Enumerated(_)         -> null
        | Sequence(children)    ->
             let emitChild (c:ChildInfo) =
                 PrintExpression c.Type (gen.SequencePatternChild c.Name.Value (ToC c.Name.Value) stgFileName)
             let childArray = children |> Seq.map emitChild |> Seq.filter (fun x -> x <> null)
             gen.ContractExprSequence childArray stgFileName
        | SequenceOf(_)         ->
            let sMin, sMax = GetMinMax (GetTypeUperRange t.Kind t.Constraints r)
            gen.ContractExprSize pattern sMin sMax (sMin = sMax) stgFileName
        | ReferenceType(_,_, _) -> null

    let pattern = PrintPattern tas
    let expression = PrintExpression tas.Type pattern
    gen.Contract pattern (if String.length(expression) > 0 then expression else null) stgFileName


let rec PrintType (t:Asn1Type) modName (r:AstRoot) (stgFileName:string) =
    let PrintTypeAux (t:Asn1Type) =
        match t.Kind with
        | Integer               -> handTypeWithMinMax (gen.IntegerType () stgFileName)         (GetTypeUperRange t.Kind t.Constraints r) gen.MinMaxType stgFileName
        | BitString             -> handTypeWithMinMax (gen.BitStringType () stgFileName)       (GetTypeUperRange t.Kind t.Constraints r) gen.MinMaxType2 stgFileName
        | OctetString           -> handTypeWithMinMax (gen.OctetStringType () stgFileName)     (GetTypeUperRange t.Kind t.Constraints r) gen.MinMaxType2 stgFileName
        | Real                  -> handTypeWithMinMax (gen.RealType () stgFileName)            (GetTypeRange_real t.Kind t.Constraints r) gen.MinMaxType stgFileName
        | IA5String             -> handTypeWithMinMax (gen.IA5StringType () stgFileName)       (GetTypeUperRange t.Kind t.Constraints r) gen.MinMaxType2 stgFileName
        | NumericString         -> handTypeWithMinMax (gen.NumericStringType () stgFileName)   (GetTypeUperRange t.Kind t.Constraints r) gen.MinMaxType2 stgFileName
        | Boolean               -> gen.BooleanType () stgFileName
        | NullType              -> gen.NullType () stgFileName
        | Choice(children)      ->
            let emitChild (c:ChildInfo) =
                gen.ChoiceChild c.Name.Value (ToC c.Name.Value) (BigInteger c.Name.Location.srcLine) (BigInteger c.Name.Location.charPos) (PrintType c.Type modName r stgFileName) (c.CName_Present C) stgFileName
            gen.ChoiceType (children |> Seq.map emitChild) stgFileName
        | Sequence(children)    ->
            let emitChild (c:ChildInfo) =
                match c.Optionality with
                | Some(Default(vl)) -> gen.SequenceChild c.Name.Value (ToC c.Name.Value) true (PrintAsn1.PrintAsn1Value vl) (BigInteger c.Name.Location.srcLine) (BigInteger c.Name.Location.charPos) (PrintType c.Type modName r stgFileName) stgFileName
                | _                 -> gen.SequenceChild c.Name.Value (ToC c.Name.Value) c.Optionality.IsSome null (BigInteger c.Name.Location.srcLine) (BigInteger c.Name.Location.charPos) (PrintType c.Type modName r stgFileName) stgFileName
            gen.SequenceType (children |> Seq.map emitChild) stgFileName
        | Enumerated(items)     ->
            let emitItem (idx: int) (it : Ast.NamedItem) =
                match it._value with
                | Some(vl)  -> gen.EnumItem it.Name.Value (ToC it.Name.Value) (Ast.GetValueAsInt vl r) (BigInteger it.Name.Location.srcLine) (BigInteger it.Name.Location.charPos) (it.CEnumName r C) stgFileName
                | None      -> gen.EnumItem it.Name.Value (ToC it.Name.Value) (BigInteger idx) (BigInteger it.Name.Location.srcLine) (BigInteger it.Name.Location.charPos) (it.CEnumName r C) stgFileName
            gen.EnumType (items |> Seq.mapi emitItem) stgFileName
        | SequenceOf(child)     ->
            let sMin, sMax = GetMinMax (GetTypeUperRange t.Kind t.Constraints r) 
            gen.SequenceOfType sMin sMax  (PrintType child modName r stgFileName) stgFileName
        | ReferenceType(md,ts, _) ->
            let uperRange = 
                match (Ast.GetActualType t r).Kind with
                | Integer | BitString | OctetString | IA5String | NumericString | SequenceOf(_)         -> Some (GetMinMax (GetTypeUperRange t.Kind t.Constraints r) )
                | Real                                                                                  -> Some (GetMinMax (GetTypeRange_real t.Kind t.Constraints r))
                | Boolean | NullType | Choice(_) | Enumerated(_) | Sequence(_) | ReferenceType(_)       -> None
            let sModName = if md.Value=modName then null else md.Value
            let sCModName = if sModName <> null then (ToC sModName) else null
            match uperRange with
            | Some(sMin, sMax)  -> gen.RefTypeMinMax sMin sMax ts.Value sModName (ToC ts.Value) sCModName stgFileName
            | None              -> gen.RefType ts.Value sModName (ToC ts.Value) sCModName stgFileName

    gen.TypeGeneric (BigInteger t.Location.srcLine) (BigInteger t.Location.charPos) (PrintTypeAux t) stgFileName


let DoWork (r:AstRoot) (stgFileName:string) (outFileName:string) =
    let AssigOp (t: Asn1Type) =
        match t.Kind with
        | Sequence(_) -> gen.AssigOpSpecialType () stgFileName
        | _           -> gen.AssigOpNormalType () stgFileName
    let PrintVas (vas: Ast.ValueAssignment) modName =
        gen.VasXml vas.Name.Value (BigInteger vas.Name.Location.srcLine) (BigInteger vas.Name.Location.charPos) (PrintType vas.Type modName r stgFileName) (PrintCustomAsn1Value vas stgFileName) (ToC vas.Name.Value)  stgFileName
    let PrintTas (tas:Ast.TypeAssignment) modName =
        gen.TasXml tas.Name.Value (BigInteger tas.Name.Location.srcLine) (BigInteger tas.Name.Location.charPos) (PrintType tas.Type modName r stgFileName) (ToC tas.Name.Value) (AssigOp tas.Type) (PrintContract tas r stgFileName) stgFileName
    let PrintModule (m:Asn1Module) =
        let PrintImpModule (im:Ast.ImportedModule) =
            gen.ImportedMod im.Name.Value (ToC im.Name.Value) (im.Types |> Seq.map(fun x -> x.Value)) (im.Values |> Seq.map(fun x -> x.Value)) stgFileName
        gen.ModuleXml m.Name.Value (ToC m.Name.Value) (m.Imports |> Seq.map PrintImpModule) m.ExportedTypes m.ExportedVars (m.TypeAssignments |> Seq.map (fun t -> PrintTas t m.Name.Value)) (m.ValueAssignments |> Seq.map (fun t -> PrintVas t m.Name.Value)) stgFileName
    let PrintFile (f:Asn1File) =
        gen.FileXml f.FileName (f.Modules |> Seq.map PrintModule) stgFileName
    let content = gen.RootXml (r.Files |> Seq.map PrintFile) stgFileName
    File.WriteAllText(outFileName, content.Replace("\r",""))





