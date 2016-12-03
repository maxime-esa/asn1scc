module print_debug


open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open FsUtils
open System
open System.IO
open BAst

type PRINT_CONTENT =
    | REF
    | CON

let rec printReferenceToType (r:AstRoot) (p:PRINT_CONTENT) (ReferenceToType path) =
    match p with
    | REF -> path |> Seq.skip 1 |> Seq.toList |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
    | CON  -> (PrintType r (r.typesMap.[(ReferenceToType path)])) + "--" + (path |> Seq.skip 1 |> Seq.toList |> List.map (fun x -> x.StrValue) |> Seq.StrJoin ".")

and printReferenceToValue (r:AstRoot) (p:PRINT_CONTENT) (ReferenceToValue (path, vpath)) =
    match p with
    | REF ->
        let p1 = path |> Seq.skip 1 |> Seq.toList |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
        let p2 = vpath |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
        p1 + "." + p2
    | CON ->
        PrintAsn1Value r r.valsMap.[(ReferenceToValue (path, vpath))]
    

and PrintAsn1Value (r:AstRoot) (v:Asn1Value) = 
    match v.Kind with
    |IntegerValue(v)         -> ASN.Print_IntegerValue v
    |RealValue(v)            -> ASN.Print_RealValue v
    |StringValue(v)          -> ASN.Print_StringValue v
    |EnumValue(v)            -> ASN.Print_StringValue v
    |BooleanValue(v)         -> ASN.Print_BooleanValue v
    |BitStringValue(v)       -> ASN.Print_BitStringValue v
    |OctetStringValue(v)     -> ASN.Print_OctetStringValue (v |> Seq.map(fun x -> x) |> Seq.toArray)
    |SeqOfValue(vals)        -> ASN.Print_SeqOfValue (vals |> Seq.map (printReferenceToValue r CON ) |> Seq.toArray)
    |SeqValue(vals)          -> ASN.Print_SeqValue (vals |> Seq.map(fun (nm, v) -> ASN.Print_SeqValue_Child nm (printReferenceToValue r CON v) ) |> Seq.toArray)
    |ChValue(nm,v)           -> ASN.Print_ChValue nm (printReferenceToValue r CON v)
    |NullValue               -> ASN.Print_NullValue()


and PrintConstraint (r:AstRoot) (c:Asn1Constraint) = 
    match c with
    | SingleValueContraint(v)       -> ASN.Print_SingleValueContraint (printReferenceToValue r CON v)
    | RangeContraint(v1, v2, b1, b2)        -> ASN.Print_RangeContraint (printReferenceToValue r CON v1) (printReferenceToValue r CON v2) b1 b2
    | RangeContraint_val_MAX(v, b1)     -> ASN.Print_RangeContraint_val_MAX (printReferenceToValue r CON v) b1
    | RangeContraint_MIN_val(v, b2)     -> ASN.Print_RangeContraint_MIN_val (printReferenceToValue r CON v) b2  
    | SizeContraint(c)              -> ASN.Print_SizeContraint (PrintConstraint r c)   
    | AlphabetContraint(c)          -> ASN.Print_AlphabetContraint (PrintConstraint r c)   
    | UnionConstraint(c1,c2,virtualCon)        -> 
        match virtualCon with
        | false -> ASN.Print_UnionConstraint (PrintConstraint r c1) (PrintConstraint r c2)   
        | true  -> ""
    | IntersectionConstraint(c1,c2) -> ASN.Print_IntersectionConstraint (PrintConstraint r c1) (PrintConstraint r c2)          
    | AllExceptConstraint(c)        -> ASN.Print_AllExceptConstraint (PrintConstraint r c)      
    | ExceptConstraint(c1,c2)       -> ASN.Print_ExceptConstraint (PrintConstraint r c1) (PrintConstraint r c2)                 
    | RootConstraint(c)             -> ASN.Print_RootConstraint  (PrintConstraint r c)        
    | RootConstraint2(c1,c2)        -> ASN.Print_RootConstraint2 (PrintConstraint r c1) (PrintConstraint r c2)


and PrintType (r:AstRoot) (t:Asn1Type) =
    let cons = t.Constraints |> Seq.map (PrintConstraint r)  |> Seq.toList
    let fcons = t.FromWithCompConstraints |> Seq.map (fun c -> sprintf "[%s]" (PrintConstraint r c)) |> Seq.toList
    let cons = cons@fcons
    match t.Kind with
    |Integer    -> ASN.Print_Integer cons
    |Real       -> ASN.Print_Real cons
    |Boolean    -> ASN.Print_Boolean cons
    |BitString  -> ASN.Print_BitString cons
    |OctetString-> ASN.Print_OctetString cons
    |NullType   -> ASN.Print_NullType cons
    |IA5String  -> ASN.Print_IA5String cons
    |Enumerated(items)  ->
        let printItem (it:NamedItem) = ASN.Print_Enumerated_child it.Name it.refToValue.IsSome (if it.refToValue.IsSome then (printReferenceToValue r CON it.refToValue.Value) else "")
        ASN.Print_Enumerated (items |> Seq.map printItem |> Seq.toArray) cons
    |Choice(children)   ->
        let printChild (c:ChildInfo) = ASN.Print_Choice_child c.Name (printReferenceToType r CON c.refToType)
        ASN.Print_Choice (children |> Seq.map printChild |> Seq.toArray) cons
    |Sequence(children) ->
        let printChild (c:ChildInfo) = 
            let bIsOptionalOrDefault, soDefValue = 
                match c.Optionality with
                | Some Optional   -> true, None
                | Some (Default v)    -> true, Some (printReferenceToValue r CON v)
                | Some  AlwaysAbsent  -> true, None
                | Some AlwaysPresent  -> true, None
                | None                -> false, None
            ASN.Print_Sequence_child c.Name (printReferenceToType r CON c.refToType) bIsOptionalOrDefault soDefValue
        ASN.Print_Sequence (children |> Seq.map printChild |> Seq.toArray) cons
    |SequenceOf(child)  -> ASN.Print_SequenceOf (printReferenceToType r CON child) cons


let PrintTypeAss (r:AstRoot) (t:Asn1Type)  = 
    let nm = match t.asn1Name with Some x -> x | None -> "anonymous"
    let bnm = t.baseTypeId |> Option.map (printReferenceToType r REF)
    ASN.PrintTypeAssigment2 (printReferenceToType r REF t.id) bnm nm (PrintType r t)

let PrintValueAss (r:AstRoot) (v:Asn1Value) = ASN.PrintValueAssigment (printReferenceToValue r REF v.id) (printReferenceToType r REF v.refToType) (PrintAsn1Value r v)

let PrintModule (r:AstRoot) (m:Asn1Module) =
    let exports =
        match m.Exports with
        | Ast.All               -> "ALL"
        | Ast.OnlySome exps     -> exps |> Seq.StrJoin ", "
    let importsFromModule =
        m.Imports |>
        List.map(fun im -> ASN.PrintModuleImportFromModule ( (im.Types @ im.Values) |> List.map(fun s -> s.Value)) im.Name.Value )

    let tases = m.TypeAssignments |> Seq.map(fun x -> PrintTypeAss r x ) |> Seq.toArray
    let vases = m.ValueAssignments |> Seq.map(fun x -> PrintValueAss r x )|> Seq.toArray
    ASN.PrintModule m.Name tases vases exports importsFromModule

let PrintFile (r:AstRoot) (f:Asn1File) outDir newFileExt =
    let modules = f.Modules |> Seq.map (PrintModule r)|> Seq.toArray
    let fileContent = ASN.PrintAsn1File modules
    let outFileName = Path.Combine(outDir, f.FileName+newFileExt)
    File.WriteAllText(outFileName, fileContent.Replace("\r",""))


let DoWork (r:AstRoot) outDir newFileExt=
    r.Files |> Seq.iter(fun f -> PrintFile r f outDir newFileExt)
