module print_debug


open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open FsUtils
open System
open System.IO
open BAst

let printReferenceToType (ReferenceToType path) =
    path |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
let printReferenceToValue (ReferenceToValue (path, vpath)) =
    let p1 = path |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
    let p2 = vpath |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
    p1 + "." + p2

let PrintAsn1Value (v:Asn1Value) = 
    match v.Kind with
    |IntegerValue(v)         -> ASN.Print_IntegerValue v
    |RealValue(v)            -> ASN.Print_RealValue v
    |StringValue(v)          -> ASN.Print_StringValue v
    |EnumValue(v)            -> ASN.Print_StringValue v
    |BooleanValue(v)         -> ASN.Print_BooleanValue v
    |BitStringValue(v)       -> ASN.Print_BitStringValue v
    |OctetStringValue(v)     -> ASN.Print_OctetStringValue (v |> Seq.map(fun x -> x) |> Seq.toArray)
    |SeqOfValue(vals)        -> ASN.Print_SeqOfValue (vals |> Seq.map printReferenceToValue |> Seq.toArray)
    |SeqValue(vals)          -> ASN.Print_SeqValue (vals |> Seq.map(fun (nm, v) -> ASN.Print_SeqValue_Child nm (printReferenceToValue v) ) |> Seq.toArray)
    |ChValue(nm,v)           -> ASN.Print_ChValue nm (printReferenceToValue v)
    |NullValue               -> ASN.Print_NullValue()


let rec PrintConstraint (c:Asn1Constraint) = 
    match c with
    | SingleValueContraint(v)       -> ASN.Print_SingleValueContraint (printReferenceToValue v)
    | RangeContraint(v1, v2, b1, b2)        -> ASN.Print_RangeContraint (printReferenceToValue v1) (printReferenceToValue v2) b1 b2
    | RangeContraint_val_MAX(v, b1)     -> ASN.Print_RangeContraint_val_MAX (printReferenceToValue v) b1
    | RangeContraint_MIN_val(v, b2)     -> ASN.Print_RangeContraint_MIN_val (printReferenceToValue v) b2  
    | RangeContraint_MIN_MAX        -> ASN.Print_RangeContraint_MIN_MAX()
    | SizeContraint(c)              -> ASN.Print_SizeContraint (PrintConstraint c)   
    | AlphabetContraint(c)          -> ASN.Print_AlphabetContraint (PrintConstraint c)   
    | UnionConstraint(c1,c2,virtualCon)        -> 
        match virtualCon with
        | false -> ASN.Print_UnionConstraint (PrintConstraint c1) (PrintConstraint c2)   
        | true  -> ""
    | IntersectionConstraint(c1,c2) -> ASN.Print_IntersectionConstraint (PrintConstraint c1) (PrintConstraint c2)          
    | AllExceptConstraint(c)        -> ASN.Print_AllExceptConstraint (PrintConstraint c)      
    | ExceptConstraint(c1,c2)       -> ASN.Print_ExceptConstraint (PrintConstraint c1) (PrintConstraint c2)                 
    | RootConstraint(c)             -> ASN.Print_RootConstraint  (PrintConstraint c)        
    | RootConstraint2(c1,c2)        -> ASN.Print_RootConstraint2 (PrintConstraint c1) (PrintConstraint c2)


let PrintType (t:Asn1Type) =
    let cons = t.Constraints |> Seq.map PrintConstraint |> Seq.toArray
    match t.Kind with
    |Integer    -> ASN.Print_Integer cons
    |Real       -> ASN.Print_Real cons
    |Boolean    -> ASN.Print_Boolean cons
    |BitString  -> ASN.Print_BitString cons
    |OctetString-> ASN.Print_OctetString cons
    |NullType   -> ASN.Print_NullType cons
    |IA5String  -> ASN.Print_IA5String cons
    |Enumerated(items)  ->
        let printItem (it:NamedItem) = ASN.Print_Enumerated_child it.Name it.refToValue.IsSome (if it.refToValue.IsSome then (printReferenceToValue it.refToValue.Value) else "")
        ASN.Print_Enumerated (items |> Seq.map printItem |> Seq.toArray) cons
    |Choice(children)   ->
        let printChild (c:ChildInfo) = ASN.Print_Choice_child c.Name (printReferenceToType c.refToType)
        ASN.Print_Choice (children |> Seq.map printChild |> Seq.toArray) cons
    |Sequence(children) ->
        let printChild (c:ChildInfo) = 
            let bIsOptionalOrDefault, bHasDefValue, sDefValue = 
                match c.Optionality with
                |Some(Optional(_))   -> true, false, ""
                |Some(Default(v))    -> true, true, (printReferenceToValue v)
                |_                   -> false, false, ""
            ASN.Print_Sequence_child c.Name (printReferenceToType c.refToType) bIsOptionalOrDefault bHasDefValue sDefValue
        ASN.Print_Sequence (children |> Seq.map printChild |> Seq.toArray) cons
    |SequenceOf(child)  -> ASN.Print_SequenceOf (printReferenceToType child) cons


let PrintTypeAss (t:Asn1Type)  = 
    let nm = match t.asn1Name with Some x -> x | None -> "anonymous"
    let bnm = t.baseTypeId |> Option.map printReferenceToType 
    ASN.PrintTypeAssigment2 (printReferenceToType t.id) bnm nm (PrintType t)

let PrintValueAss (v:Asn1Value) = ASN.PrintValueAssigment (printReferenceToValue v.id) (printReferenceToType v.refToType) (PrintAsn1Value v)

let PrintModule (m:Asn1Module) =
    let exports =
        match m.Exports with
        | Ast.All               -> "ALL"
        | Ast.OnlySome exps     -> exps |> Seq.StrJoin ", "
    let importsFromModule =
        m.Imports |>
        List.map(fun im -> ASN.PrintModuleImportFromModule ( (im.Types @ im.Values) |> List.map(fun s -> s.Value)) im.Name.Value )

    let tases = m.TypeAssignments |> Seq.map(fun x -> PrintTypeAss x ) |> Seq.toArray
    let vases = m.ValueAssignments |> Seq.map(fun x -> PrintValueAss x )|> Seq.toArray
    ASN.PrintModule m.Name tases vases exports importsFromModule

let PrintFile (f:Asn1File) outDir newFileExt =
    let modules = f.Modules |> Seq.map PrintModule |> Seq.toArray
    let fileContent = ASN.PrintAsn1File modules
    let outFileName = Path.Combine(outDir, f.FileName+newFileExt)
    File.WriteAllText(outFileName, fileContent.Replace("\r",""))


let DoWork (r:AstRoot) outDir newFileExt=
    r.Files |> Seq.iter(fun f -> PrintFile f outDir newFileExt)
