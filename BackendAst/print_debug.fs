module print_debug


open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open FsUtils
open System
open System.IO
open Constraints
open BAst
type PRINT_CONTENT =
    | REF
    | CON

let printUperRange (u:uperRange<'a>) =
    match u with
    | Concrete  (a,b)   -> sprintf "[%A .. %A]" a b
    | NegInf    a       -> sprintf "[MIN .. %A]" a        //(-inf, b]
    | PosInf    a       -> sprintf "[%A .. MAX]" a        //(-inf, b]
    | Full              -> "[MIN .. MAX]"                 // (-inf, +inf)


let printGenericConstraint printValue (c:GenericConstraint<'v>)  = 
    foldGenericConstraint
        (fun r1 r2 b s      -> ASN.Print_UnionConstraint r1 r2, s)
        (fun r1 r2 s        -> ASN.Print_IntersectionConstraint r1 r2 , s)
        (fun r s            -> ASN.Print_AllExceptConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_ExceptConstraint r1 r2, s)
        (fun r s            -> ASN.Print_RootConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_RootConstraint2 r1 r2, s)
        (fun v rv s         -> ASN.Print_SingleValueContraint (printValue v),s)
        c 
        0

let printRangeConstraint0 printValue printValue2  (c:RangeTypeConstraint<'v1,'v2>) = 
    foldRangeTypeConstraint
        (fun r1 r2 b s      -> ASN.Print_UnionConstraint r1 r2, s)
        (fun r1 r2 s        -> ASN.Print_IntersectionConstraint r1 r2 , s)
        (fun r s            -> ASN.Print_AllExceptConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_ExceptConstraint r1 r2, s)
        (fun r s            -> ASN.Print_RootConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_RootConstraint2 r1 r2, s)
        (fun v rv s         -> ASN.Print_SingleValueContraint (printValue2 v),s)
        (fun v1 v2  b1 b2 s -> ASN.Print_RangeContraint (printValue v1) (printValue v2) b1 b2, s)
        (fun v1 b s         -> ASN.Print_RangeContraint_val_MAX (printValue v1) b ,s )
        (fun v2 b s         -> ASN.Print_RangeContraint_MIN_val (printValue v2) b, s)
        c 
        0

let printRangeConstraint printValue (c:RangeTypeConstraint<'v1,'v1>)  = 
    printRangeConstraint0 printValue printValue c 

let printSizableConstraint printValue (c:SizableTypeConstraint<'v>)  = 
    foldSizableTypeConstraint2
        (fun r1 r2 b s      -> ASN.Print_UnionConstraint r1 r2, s)
        (fun r1 r2 s        -> ASN.Print_IntersectionConstraint r1 r2 , s)
        (fun r s            -> ASN.Print_AllExceptConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_ExceptConstraint r1 r2, s)
        (fun r s            -> ASN.Print_RootConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_RootConstraint2 r1 r2, s)
        (fun v rv s         -> ASN.Print_SingleValueContraint (printValue v),s)
        (fun sc s           -> 
            let sizeCon,_ = printRangeConstraint (fun ui -> ui.ToString()) sc 
            ASN.Print_SizeContraint sizeCon, s)
        c 
        0

let printAlphaConstraint printValue (c:IA5StringConstraint)  = 
    foldStringTypeConstraint2
        (fun r1 r2 b s      -> ASN.Print_UnionConstraint r1 r2, s)
        (fun r1 r2 s        -> ASN.Print_IntersectionConstraint r1 r2 , s)
        (fun r s            -> ASN.Print_AllExceptConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_ExceptConstraint r1 r2, s)
        (fun r s            -> ASN.Print_RootConstraint r, s)       
        (fun r1 r2 s        -> ASN.Print_RootConstraint2 r1 r2, s)
        (fun v rv s         -> ASN.Print_SingleValueContraint (printValue v),s)
        (fun sc s           -> 
            let sizeCon,_ = printRangeConstraint (fun ui -> ui.ToString()) sc 
            ASN.Print_SizeContraint sizeCon, s)
        (fun sc s           -> 
            let sizeCon,_ = printRangeConstraint0 (fun ui -> "\"" + ui.ToString() + "\"") (fun ui -> "\"" + ui.ToString() + "\"") sc 
            ASN.Print_AlphabetContraint sizeCon, s)
        c 
        0

let rec printReferenceToType (r:AstRoot) (p:PRINT_CONTENT) (ReferenceToType path) =
    match p with
    | REF -> path |> Seq.skip 1 |> Seq.toList |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
    | CON  -> (PrintType r (r.typesMap.[(ReferenceToType path)])) //+ "--" + (path |> Seq.skip 1 |> Seq.toList |> List.map (fun x -> x.StrValue) |> Seq.StrJoin ".")

and printReferenceToValue (r:AstRoot) (p:PRINT_CONTENT) (ReferenceToValue (path, vpath)) =
    match p with
    | REF ->
        let p1 = path |> Seq.skip 1 |> Seq.toList |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
        let p2 = vpath |> List.map (fun x -> x.StrValue) |> Seq.StrJoin "."
        p1 + "." + p2
    | CON ->
        PrintAsn1GenericValue r r.valsMap.[(ReferenceToValue (path, vpath))]
    

and PrintAsn1GenericValue (r:AstRoot) (v:Asn1GenericValue) = 
    match v with
    |IntegerValue(v)         -> ASN.Print_IntegerValue v.Value
    |RealValue(v)            -> ASN.Print_RealValue v.Value
    |StringValue(v)          -> ASN.Print_StringValue v.Value
    |EnumValue(v)            -> ASN.Print_StringValue v.Value
    |BooleanValue(v)         -> ASN.Print_BooleanValue v.Value
    |BitStringValue(v)       -> ASN.Print_BitStringValue v.Value
    |OctetStringValue(v)     -> ASN.Print_OctetStringValue (v.Value |> Seq.map(fun x -> x) |> Seq.toArray)
    |SeqOfValue(v)           -> ASN.Print_SeqOfValue (v.Value |> Seq.map (fun v -> printReferenceToValue r CON v.id) |> Seq.toArray)
    |SeqValue(v)             -> ASN.Print_SeqValue (v.Value |> Seq.map(fun nv -> ASN.Print_SeqValue_Child nv.name (printReferenceToValue r CON nv.Value.id) ) |> Seq.toArray)
    |ChValue(v)              -> ASN.Print_ChValue v.Value.name (printReferenceToValue r CON v.Value.Value.id)
    |NullValue   _           -> ASN.Print_NullValue()

(*
and PrintConstraint (r:AstRoot) (c:Asn1Constraint) = 
    match c with
    | SingleValueContraint(v)       -> ASN.Print_SingleValueContraint (printReferenceToValue r CON v.id)
    | RangeContraint(v1, v2, b1, b2)        -> ASN.Print_RangeContraint (printReferenceToValue r CON v1.id) (printReferenceToValue r CON v2.id) b1 b2
    | RangeContraint_val_MAX(v, b1)     -> ASN.Print_RangeContraint_val_MAX (printReferenceToValue r CON v.id) b1
    | RangeContraint_MIN_val(v, b2)     -> ASN.Print_RangeContraint_MIN_val (printReferenceToValue r CON v.id) b2  
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
*)

and PrintType (r:AstRoot) (t:Asn1Type) =
    (*
    let rec getBaseCons (t:Asn1Type) = 
        match t.baseTypeId with
        | None  -> t.Constraints,t.FromWithCompConstraints
        | Some bid ->
            let baseCon, baseFromCom = getBaseCons (r.typesMap.[bid])
            t.Constraints@baseCon, t.FromWithCompConstraints@baseFromCom
    let constraints, fromWithCompConstraints = getBaseCons t
    let cons = constraints |> Seq.map (PrintConstraint r)  |> Seq.toList
    let fcons = fromWithCompConstraints |> Seq.map (fun c -> sprintf "[%s]" (PrintConstraint r c)) |> Seq.toList
    let cons = cons@fcons
    *)
    let printCon  printConFunc vGetter (b:bool,c:'con) =
        let s,_ = printConFunc vGetter  c
        match b with
        | true  -> sprintf "[%s]" s
        | false -> s

    match t with
    |Integer intt       -> ASN.Print_Integer (printUperRange intt.uperRange) (intt.cons |> List.map (printCon printRangeConstraint (fun x -> x.ToString()) ) )
    |Real  rCons        -> ASN.Print_Real (rCons.cons |> List.map (printCon printRangeConstraint (fun x -> x.ToString()) ) )
    |Boolean b          -> ASN.Print_Boolean (b.cons |> List.map (printCon printGenericConstraint (fun x -> x.ToString()) ) )
    |BitString bs       -> ASN.Print_BitString (bs.cons |> List.map (printCon printSizableConstraint (fun x -> x.ToString()) ) )
    |OctetString  oc    -> ASN.Print_OctetString (oc.cons |> List.map (printCon printSizableConstraint (fun x -> x.ToString()) ) )
    |NullType _         -> ASN.Print_NullType []
    |IA5String str  -> 
        ASN.Print_IA5String2 (printUperRange str.sizeUperRange) (printUperRange str.charUperRange) (str.cons |> List.map (printCon printAlphaConstraint (fun x -> x.ToString()) ) )
    |Enumerated enumItem  ->
        let items =
            enumItem.items |> List.map(fun itm -> ASN.Print_Enumerated_child itm.name true (itm.Value.ToString() ))
        let cons =
            (enumItem.cons |> List.map (printCon printGenericConstraint (fun x -> x.ToString()) ) )
        ASN.Print_Enumerated items  cons
    |Choice ch   ->
        let printChild (c:ChildInfo) = ASN.Print_Choice_child c.Name (printReferenceToType r CON c.chType.id)
        let cons =
            (ch.cons |> List.map (printCon printGenericConstraint (fun (nm,rv) -> ASN.Print_ChValue nm (printReferenceToValue r CON rv)  ) ) )
        ASN.Print_Choice (ch.children |> Seq.map printChild |> Seq.toArray) cons
    |Sequence sq ->
        let printChild (c:ChildInfo) = 
            let bIsOptionalOrDefault, soDefValue = 
                match c.Optionality with
                | Some Optional   -> true, None
                | Some (Default v)    -> true, Some (printReferenceToValue r CON v.id)
                | Some  AlwaysAbsent  -> true, None
                | Some AlwaysPresent  -> true, None
                | None                -> false, None
            ASN.Print_Sequence_child c.Name (printReferenceToType r CON c.chType.id) bIsOptionalOrDefault soDefValue
        let cons =
            (sq.cons |> List.map (printCon printGenericConstraint (fun vals -> ASN.Print_SeqValue (vals |> List.map(fun (nm, v) -> ASN.Print_SeqValue_Child nm (printReferenceToValue r CON v) ) )  ) ) )
        ASN.Print_Sequence (sq.children |> Seq.map printChild |> Seq.toArray) cons
    |SequenceOf sqOf  -> 
        let cons =
            (sqOf.cons |> List.map (printCon printSizableConstraint (fun vals -> ASN.Print_SeqOfValue (vals |> Seq.map (fun v -> printReferenceToValue r CON v) |> Seq.toArray) ) ) )
        ASN.Print_SequenceOf (printReferenceToType r CON sqOf.childType.id) cons


let PrintTypeAss (r:AstRoot) (t:Asn1Type)  = 
    let nm = match t.asn1Name with Some x -> x | None -> "anonymous"
    let bnm = t.baseType |> Option.map (fun t -> printReferenceToType r REF t.id)
    ASN.PrintTypeAssigment2 (printReferenceToType r REF t.id) bnm nm (PrintType r t)

let PrintValueAss (r:AstRoot) (v:Asn1GenericValue) = 
    ASN.PrintValueAssigment (printReferenceToValue r REF v.id) (printReferenceToType r REF v.refToType) (PrintAsn1GenericValue r v)

let PrintModule (r:AstRoot) (m:Asn1Module) =
    let exports =
        match m.Exports with
        | Ast.All               -> "ALL"
        | Ast.OnlySome exps     -> exps |> Seq.StrJoin ", "
    let importsFromModule =
        m.Imports |>
        List.map(fun im -> ASN.PrintModuleImportFromModule ( (im.Types @ im.Values) |> List.map(fun s -> s.Value)) im.Name.Value )

    let tases = r.TypeAssignments |> Seq.filter(fun x ->x.id.ModName=m.Name) |> Seq.map(fun x -> PrintTypeAss r x ) |> Seq.toArray
    let vases = r.ValueAssignments |> Seq.filter(fun x ->x.id.ModName=m.Name)|> Seq.map(fun x -> PrintValueAss r x )|> Seq.toArray
    ASN.PrintModule m.Name tases vases exports importsFromModule

let PrintFile (r:AstRoot) (f:Asn1File) outDir newFileExt =
    let modules = f.Modules |> Seq.map (PrintModule r)|> Seq.toArray
    let fileContent = ASN.PrintAsn1File modules
    let outFileName = Path.Combine(outDir, f.FileName+newFileExt)
    File.WriteAllText(outFileName, fileContent.Replace("\r",""))


let DoWork (r:AstRoot) outDir newFileExt=
    r.Files |> Seq.iter(fun f -> PrintFile r f outDir newFileExt)
