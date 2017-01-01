module print_debug


open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open FsUtils
open System
open System.IO
open Constraints
open BAst
open uPER2

type PRINT_CONTENT =
    | REF
    | CON

let printUperRange (u:uperRange<'a>) =
    match u with
    | Concrete  (a,b)   -> sprintf "[%A .. %A]" a b
    | NegInf    a       -> sprintf "[MIN .. %A]" a        //(-inf, b]
    | PosInf    a       -> sprintf "[%A .. MAX]" a        //(-inf, b]
    | Full              -> "[MIN .. MAX]"                 // (-inf, +inf)

let printCharSet (cs:char array) =
    cs|> Seq.filter (fun c -> not (Char.IsControl c)) |> Seq.StrJoin "" 

let printSizeMinMax a b = sprintf "[%d .. %d]" a b

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
    |OctetStringValue(v)     -> ASN.Print_OctetStringValue (v.Value )
    |SeqOfValue(v)           -> ASN.Print_SeqOfValue (v.Value |> Seq.map (fun v -> printReferenceToValue r CON v.id) |> Seq.toArray)
    |SeqValue(v)             -> ASN.Print_SeqValue (v.Value |> Seq.map(fun nv -> ASN.Print_SeqValue_Child nv.name (printReferenceToValue r CON nv.Value.id) ) |> Seq.toArray)
    |ChValue(v)              -> ASN.Print_ChValue v.Value.name (printReferenceToValue r CON v.Value.Value.id)
    |NullValue   _           -> ASN.Print_NullValue()



and PrintType (r:AstRoot) (t:Asn1Type) =
    let inline cmb (t : ^T) =
        let cons     = (^T : (member Cons     : ^C list)(t))
        let withcons = (^T : (member WithCons : ^C list)(t))
        (cons |> List.map(fun x -> (false,x)))@(withcons |> List.map(fun x -> (true,x)))

    let printCon  printConFunc vGetter (b:bool,c:'con) =
        let s,_ = printConFunc vGetter  c
        match b with
        | true  -> sprintf "[%s]" s
        | false -> s

    match t with
    |Integer x       -> ASN.Print_Integer (printUperRange x.uperRange) ( cmb x  |> List.map (printCon printRangeConstraint (fun x -> x.ToString()) ) )
    |Real  x         -> ASN.Print_Real (cmb x |> List.map (printCon printRangeConstraint (fun x -> x.ToString()) ) )
    |Boolean x       -> ASN.Print_Boolean (cmb x |> List.map (printCon printGenericConstraint (fun x -> x.ToString()) ) )
    |BitString x     -> ASN.Print_BitString (cmb x |> List.map (printCon printSizableConstraint (fun x -> ASN.Print_BitStringValue x.Value ) ) )
    |OctetString  x  -> ASN.Print_OctetString (cmb x  |> List.map (printCon printSizableConstraint (fun x -> ASN.Print_OctetStringValue x.Value) ) )
    |NullType _      -> ASN.Print_NullType []
    |IA5String x  -> 
        ASN.Print_IA5String2 (printSizeMinMax x.minSize x.maxSize) (printCharSet x.charSet ) (cmb x |> List.map (printCon printAlphaConstraint (fun x -> x.ToString()) ) )
    |Enumerated x  ->
        let items =
            x.items |> List.map(fun itm -> ASN.Print_Enumerated_child itm.name true (itm.Value.ToString() ))
        let cons = cmb x |> List.map (printCon printGenericConstraint (fun x -> x.ToString()) ) 
        ASN.Print_Enumerated items  cons
    |Choice x   ->
        let printChild (c:ChildInfo) = ASN.Print_Choice_child c.Name (printReferenceToType r CON c.chType.id)
        let cons = cmb x |> List.map (printCon printGenericConstraint (fun chv -> ASN.Print_ChValue chv.Value.name (printReferenceToValue r CON chv.Value.Value.id)  ) ) 
        ASN.Print_Choice (x.children |> Seq.map printChild |> Seq.toArray) cons
    |Sequence x ->
        let printChild (c:ChildInfo) = 
            let bIsOptionalOrDefault, soDefValue = 
                match c.Optionality with
                | Some Optional   -> true, None
                | Some (Default v)    -> true, Some (printReferenceToValue r CON v.id)
                | Some  AlwaysAbsent  -> true, None
                | Some AlwaysPresent  -> true, None
                | None                -> false, None
            ASN.Print_Sequence_child c.Name (printReferenceToType r CON c.chType.id) bIsOptionalOrDefault soDefValue
        let cons = cmb x |> List.map (printCon printGenericConstraint (fun sqv -> ASN.Print_SeqValue (sqv.Value |> List.map(fun nmv -> ASN.Print_SeqValue_Child nmv.name (printReferenceToValue r CON nmv.Value.id) ) )  ) ) 
        ASN.Print_Sequence (x.children |> Seq.map printChild |> Seq.toArray) cons
    |SequenceOf x  -> 
        let cons = cmb x |> List.map (printCon printSizableConstraint (fun sqofv -> ASN.Print_SeqOfValue (sqofv.Value |> Seq.map (fun v -> printReferenceToValue r CON v.id) |> Seq.toArray) ) ) 
        ASN.Print_SequenceOf (printReferenceToType r CON x.childType.id) cons


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
