module acn_backend_logic

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils

(*
1. Groups PresenseInt or PresenseString References used in Choices
2. Removes entries RefTypeArgument that point to a EncodeDecodeMode parameter (since no update is required)
*)
let GroupReferences (determinant:AcnTypes.Point)  (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  =
    let ReferenceIsPresentStringOrInt (ref:AcnTypes.LongReferenceResolved) =
        match ref.Kind with
        | AcnTypes.PresenceInt(_)   -> true
        | AcnTypes.PresenceStr(_)   -> true
        | _                         -> false
    let filterEncDecArgs (ref:AcnTypes.LongReferenceResolved) =
        match ref.Kind with
        | AcnTypes.RefTypeArgument(prmName) ->
            let otherType = GetTypeByPoint ref.decType r acn
            let newModule, newTas = match otherType.Kind with
                                    | ReferenceType(md,ts, _) -> 
                                        let m1 = r.Modules |> Seq.find(fun x -> x.Name.Value = md.Value)
                                        let t1 = m1.TypeAssignments |> Seq.find(fun x -> x.Name.Value = ts.Value)
                                        m1, t1
                                    | _                    -> raise(BugErrorException "")
            match acn.Parameters |> Seq.tryFind(fun p -> p.ModName = newModule.Name.Value && p.TasName = newTas.Name.Value && p.Name = prmName) with
            | None  -> raise(BugErrorException "")
            | Some(actPrm)  ->
                match actPrm.Mode with
                | AcnTypes.ParamMode.DecodeMode     -> true
                | AcnTypes.ParamMode.EncodeDecodeMode -> false
        | _     -> true

    let part0 = acn.References |> List.filter  filterEncDecArgs           
    let part1 = part0 |> List.filter(fun x ->  x.determinant = determinant && ReferenceIsPresentStringOrInt x)  
    let part2 = part0 |> List.filter(fun x ->  x.determinant = determinant && not (ReferenceIsPresentStringOrInt x))  

    let group1 = part1
                 |> Seq.groupBy(fun x -> match x.Kind with
                                         | AcnTypes.PresenceInt(_)   -> AcnTypes.PresenceInt(AcnTypes.IntConst(IntLoc.ByValue 0I))
                                         | AcnTypes.PresenceStr(_)   -> AcnTypes.PresenceStr("")
                                         | _                         -> x.Kind) |> Seq.toList
    let group2 = part2 |> List.map(fun x -> (x.Kind, seq {yield x}))
    group1@group2

(*
Returns true if the update function <sTasName>_ACN_Encode_update_<sParamName> has a result argument or not
*)
let rec Update_param_function_requires_result (prmName:string) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved)  =
    let p = acn.Parameters |> Seq.find(fun p -> p.ModName = m.Name.Value && p.TasName = tas.Name.Value && p.Mode = AcnTypes.DecodeMode && p.Name = prmName)
    let path = [m.Name.Value; tas.Name.Value; p.Name]
    let point = AcnTypes.Point.ParamPoint(path)
    let deps = GroupReferences point r acn
    match deps with
    | []       -> false
    | (kind,refs)::[]    -> 
        match kind with
        | AcnTypes.RefTypeArgument(newPrmName)                          -> 
            let ref = Seq.head refs
            let otherType = GetTypeByPoint ref.decType r acn
            match otherType.Kind with
            | ReferenceType(md,ts, _) -> 
                let newModule = r.Modules |> Seq.find(fun x -> x.Name.Value = md.Value)
                let newTas = newModule.TypeAssignments |> Seq.find(fun x -> x.Name.Value = ts.Value)
                Update_param_function_requires_result newPrmName newTas newModule r acn
            | _                    -> raise(BugErrorException "")
        | _ -> false
    | x::xs    -> true



(*
    Returns a sequence of Asn1Value (Asn1ValueKind actually) from a given type
*)

let GetTypeValues (t:Asn1Type) (r:AstRoot) =         
    let getValue_aux (a:Asn1Value) func =
        match a.Kind with
        | IntegerValue(intLoc)  -> {a with Kind = IntegerValue({intLoc with Value = (func intLoc.Value 1I)})}
        | _                     -> a
    let getNext a = getValue_aux a (fun a b -> a + b)
    let getPrev a = getValue_aux a (fun a b -> a - b)

    let rec Asn1ValuesFromConstraints (c:Asn1Constraint) (r:AstRoot) min max zero =
        seq {
            match c with
            | SingleValueContraint(a)       -> yield a
            | RangeContraint(a,b, minIsIn, maxIsIn)           -> 
                if minIsIn then yield a else yield (getNext a)
                if maxIsIn then yield b else yield (getPrev b)
            | RangeContraint_val_MAX(a, minIsIn)     -> 
                if minIsIn then yield a else yield (getNext a)
                yield max
            | RangeContraint_MIN_val(b, maxIsIn)     -> 
                yield min; 
                if maxIsIn then yield b else yield (getPrev b)
            | RangeContraint_MIN_MAX        -> yield min; yield zero; yield max    
            | TypeInclusionConstraint(m,ts) ->
                let act = Ast.GetActualTypeByNameAllConsIncluded m ts r
                for c in act.Constraints do
                    yield! Asn1ValuesFromConstraints c r min max zero
            | SizeContraint(sc)              -> yield! Asn1ValuesFromConstraints sc r min max zero
            | AlphabetContraint(fc)          -> yield! Asn1ValuesFromConstraints fc r min max zero
            | UnionConstraint(a1,a2,_)         -> 
                yield! Asn1ValuesFromConstraints a1 r min max zero
                yield! Asn1ValuesFromConstraints a2 r min max zero
            | IntersectionConstraint(a1,a2)  ->
                yield! Asn1ValuesFromConstraints a1 r min max zero
                yield! Asn1ValuesFromConstraints a2 r min max zero
            | AllExceptConstraint(_)          -> ()
            | ExceptConstraint(a1,_)          -> yield! Asn1ValuesFromConstraints a1 r min max zero
            | RootConstraint(a1)              -> yield! Asn1ValuesFromConstraints a1 r min max zero
            | RootConstraint2(a1,a2)          ->
                yield! Asn1ValuesFromConstraints a1 r min max zero
                yield! Asn1ValuesFromConstraints a2 r min max zero
            | WithComponentConstraint(a)      -> ()
            | WithComponentsConstraint(a)     -> ()
        } |> Seq.toList
    seq {
        let min,max,zero = 
            match (Ast.GetActualType t r).Kind with
            | Integer   -> 
                let min = {Asn1Value.Kind = IntegerValue(IntLoc.ByValue (FsUtils.MinInt())); Location=emptyLocation}
                let max = {Asn1Value.Kind = IntegerValue(IntLoc.ByValue (FsUtils.MaxInt())); Location=emptyLocation}
                let zero ={Asn1Value.Kind = IntegerValue(IntLoc.ByValue 0I); Location=emptyLocation}
                min,max,zero
            | Real      ->
                let min = {Asn1Value.Kind = RealValue(loc -1.79769313486231E+308); Location=emptyLocation}
                let max = {Asn1Value.Kind = RealValue(loc 1.79769313486231E+308); Location=emptyLocation}
                let zero ={Asn1Value.Kind = RealValue(loc 0.0); Location=emptyLocation}
                min,max,zero
            |_          -> raise(BugErrorException "")
        match t.Constraints with
        | []    -> yield min.Kind; yield zero.Kind; yield max.Kind
        | _     ->
            for c in t.Constraints do
                for v in  Asn1ValuesFromConstraints c r min max zero do
                    if CheckAsn1.CheckIfVariableViolatesTypeConstraints t v r then
                        yield v.Kind
    } |> Seq.toList

let rec GenerateValues (a:Asn1Type) modName (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let rec GetValueFromConstraint (a:Asn1Type) =
        let rec GetValueFromSingleValueConstraint (c:Asn1Constraint) =
            seq {
                match c with
                | SingleValueContraint(a)       -> yield a
                | RangeContraint(a,b, _,_)           -> ()
                | RangeContraint_val_MAX(a,_)     -> ()
                | RangeContraint_MIN_val(b,_)     -> ()
                | RangeContraint_MIN_MAX        -> ()    
                | TypeInclusionConstraint(m,ts) -> ()
                | SizeContraint(sc)             -> ()
                | AlphabetContraint(fc)         -> ()
                | UnionConstraint(a1,a2,_)        -> 
                    yield! GetValueFromSingleValueConstraint a1 
                    yield! GetValueFromSingleValueConstraint a2 
                | IntersectionConstraint(a1,a2)  -> ()
                | AllExceptConstraint(_)         -> ()
                | ExceptConstraint(a1,_)         -> ()
                | RootConstraint(a1)             -> yield! GetValueFromSingleValueConstraint a1 
                | RootConstraint2(a1,a2)         ->
                    yield! GetValueFromSingleValueConstraint a1 
                    yield! GetValueFromSingleValueConstraint a2 
                | WithComponentConstraint(a)     -> ()
                | WithComponentsConstraint(a)    -> ()
            } |> Seq.toList
        [for x in a.Constraints do
            for v in GetValueFromSingleValueConstraint x do
                yield v]
    let rec GV (kind:Asn1TypeKind) cons =
        seq {
            match kind with
            | Integer   -> 
                yield! GetTypeValues a r
            | Real     ->   yield! GetTypeValues a r
            | Enumerated(items) ->
                for it in items do
                    let dummyEnum = {a with Kind = kind; Constraints=cons}
                    let valToReturn = RefValue(modName, it.Name)
                    let dumyAsn1Vale = {Asn1Value.Kind = valToReturn; Location= emptyLocation}
                    if CheckAsn1.CheckIfVariableViolatesTypeConstraints dummyEnum dumyAsn1Vale r then
                        yield valToReturn
            | IA5String | NumericString ->
                let chr = GetTypeUperRangeFrom(kind,cons, r) |> Seq.filter(fun c -> not (System.Char.IsControl c)) |> Seq.head
                let min,max = uPER.GetSizebaleMinMax kind cons r
                yield StringValue (loc (System.String(chr,int min)) )
                if min<>max then
                    yield StringValue (loc (System.String(chr,int max)) )
            | OctetString   ->
                let valFromCons = GetValueFromConstraint a
                match valFromCons with
                | []    ->
                    let min,max = uPER.GetSizebaleMinMax kind cons r
                    yield OctetStringValue ([1I..min] |> List.map(fun i -> ByteLoc.ByValue 0uy))
                    if min <> max then
                        yield OctetStringValue ([1I..max] |> List.map(fun i -> ByteLoc.ByValue 0uy))
                | _     -> for x in valFromCons do yield x.Kind
            | BitString    ->
                let valFromCons = GetValueFromConstraint a
                match valFromCons with
                | []    ->
                    let min,max = uPER.GetSizebaleMinMax kind cons r
                    yield BitStringValue (loc (System.String('0',int min)) )
                    if min <> max then
                        yield BitStringValue (loc (System.String('0',int max)) )
                | _     -> for x in valFromCons do yield x.Kind
            | Boolean                   -> yield BooleanValue (loc false); yield BooleanValue (loc true)
            | ReferenceType(mdName, tasName, _) ->
                let tp = GetActualTypeByNameAllConsIncluded mdName tasName r
                let vals = GenerateValues (RemoveWithComponents tp r) mdName r acn
                yield  (Seq.head vals)
            | NullType                      -> yield NullValue
            | Choice(children)          ->
                for ch in children do
                    for chVal in (GenerateValues (RemoveWithComponents ch.Type r) modName r acn) do
                        yield ChValue(ch.Name, {Asn1Value.Kind=chVal; Location=emptyLocation})
            | SequenceOf(child)         ->
                let min,max = uPER.GetSizebaleMinMax kind cons r
                let chVals = (GenerateValues (RemoveWithComponents (Ast.GetActualType child r) r) modName r acn)
                for chVal in chVals do 
                    yield SeqOfValue ([1I..min] |> List.map(fun i -> {Asn1Value.Kind=chVal; Location=emptyLocation}))
                    let newMax = if max <= 100000I then max else 100000I
                    if min < newMax && min <> newMax then
                        yield SeqOfValue ([1I..newMax] |> List.map(fun i -> {Asn1Value.Kind=chVal; Location=emptyLocation}))
            
            | Sequence(childrn)    ->
                let children = childrn |> List.filter(fun x -> not x.AcnInsertedField)
                let HandleChild (ch:ChildInfo) =
                            (ch.Name, {Asn1Value.Kind=Seq.head(GenerateValues (RemoveWithComponents ch.Type r) modName r acn); Location=emptyLocation})

                yield SeqValue (children |> List.map HandleChild)
                yield SeqValue (children |> List.filter(fun c -> match c.Optionality with
                                                                 | None  | Some(AlwaysPresent) -> true
                                                                 | _                           -> false ) |> List.map HandleChild)
        }

    GV a.Kind a.Constraints



let GenerateVases (tas:TypeAssignment) modName (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let createVal k = {Asn1Value.Kind = k; Location = emptyLocation}
    let createRefType  name = {Asn1Type.Kind = ReferenceType(modName, name, false); Constraints=[]; Location = emptyLocation; AcnProperties=[]}
    let I = ref 0
    let noWithComponent = RemoveWithComponents (Ast.GetActualType tas.Type r) r
    seq {
        for v in (GenerateValues noWithComponent modName r acn) do
            I := !I + 1
            let vasName = tas.Name.Value.ToLower()+"_"+(!I).ToString()
            yield {ValueAssignment .Name = loc vasName; Type = (createRefType tas.Name); Value = createVal v; Scope = GlobalScope; c_name = ToC vasName; ada_name = ToC vasName}
    }
