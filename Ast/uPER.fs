module uPER

open System.Numerics
open FsUtils
open Ast





let min a b = if a<b then a else b
let max a b = if a>b then a else b

let rec uperUnion r1 r2 =
    match r1,r2 with
    | (Full,_)                      -> Full
    | (Empty,_)                     -> r2
    | (PosInf(a), PosInf(b))        -> PosInf(min a b)
    | (PosInf(a), NegInf(b))        -> Full
    | (PosInf(a1), Concrete(a,b))   -> PosInf(min a1 a)
    | (NegInf(a), NegInf(b))        -> NegInf(max a b)
    | (NegInf(a), PosInf(b))        -> Full
    | (NegInf(a1), Concrete(a,b))   -> NegInf(max a1 b)
    | (Concrete(a1,b1), Concrete(a2,b2)) -> Concrete(min a1 a2, max b1 b2)
    | _                             ->  uperUnion r2 r1

let rec uperIntersection (r1, r2) =
    match r1,r2 with
    | (Full,_)                      -> r2
    | (Empty,_)                     -> Empty
    | (PosInf(a), PosInf(b))        -> PosInf(max a b)
    | (PosInf(a), NegInf(b))        -> if a<=b then Concrete(a,b) else Empty
    | (PosInf(a1), Concrete(a,b))   -> if a1>b then Empty 
                                        elif a1<=a then r1 
                                        else Concrete(a1,b) 
    | (NegInf(a), NegInf(b))        -> NegInf(min a b)
    | (NegInf(a), PosInf(b))        -> if a>=b then Concrete(b,a) else Empty
    | (NegInf(a1), Concrete(a,b))   -> if a1<a then Empty
                                        elif a1<b then Concrete(a1,b)
                                        else r2
    | (Concrete(a1,b1), Concrete(a2,b2)) -> if a1<=a2 && a2<=b1 && b1<=b2 then Concrete(a2,b1)
                                            elif a2<=a1 && a1<=b2 && b2<=b1 then Concrete(a1, b2)
                                            elif a2<=a1 && b1<=b2 then r1
                                            elif a1<=a2 && b2<=b1 then r2
                                            else Empty
    | _                             ->  uperIntersection (r2, r1)



let rec GetUperRangeAux (c:Asn1Constraint)  func funcNext funcPrev (ast:AstRoot) =
    match c with
    | SingleValueContraint(v1)          -> Concrete(func v1 , func v1 )
    | RangeContraint(v1,v2, minIsIn, maxIsIn)             -> 
        let val1 = if minIsIn then (func v1) else (funcNext (func v1))
        let val2 = if maxIsIn then (func v2) else (funcPrev (func v2))
        Concrete(val1 , val2)
    | RangeContraint_val_MAX(v1, minIsIn)        -> 
        let val1 = if minIsIn then (func v1) else (funcNext (func v1))
        PosInf(val1)
    | RangeContraint_MIN_val(v2, maxIsIn)        -> 
        let val2 = if maxIsIn then (func v2) else (funcPrev (func v2))
        NegInf(val2)
    | RangeContraint_MIN_MAX            -> Full
    | UnionConstraint(c1,c2,_)            -> uperUnion (GetUperRangeAux c1 func  funcNext funcPrev ast) (GetUperRangeAux c2 func  funcNext funcPrev ast)
    | IntersectionConstraint(c1,c2)     -> uperIntersection(GetUperRangeAux c1 func  funcNext funcPrev ast, GetUperRangeAux c2 func  funcNext funcPrev ast)
    | AllExceptConstraint(c1)           -> Full
    | ExceptConstraint(c1,c2)           -> GetUperRangeAux c1 func  funcNext funcPrev ast
    | RootConstraint(c1)                -> Full
    | RootConstraint2(c1,c2)            -> Full
    | WithComponentConstraint(_)        -> raise (BugErrorException(""))
    | WithComponentsConstraint(_)       -> raise (BugErrorException(""))
    | AlphabetContraint(_)              -> raise (BugErrorException(""))
    | SizeContraint(_)                  -> raise (BugErrorException(""))
    | TypeInclusionConstraint(modName, typeName)   -> 
        let actType = GetActualTypeByNameAllConsIncluded modName typeName ast
        actType.Constraints |> Seq.fold(fun agr c -> uperIntersection(agr, GetUperRangeAux c func  funcNext funcPrev ast)) Full


let rec GetUperRange (c:Asn1Constraint) (ast:AstRoot) = 
    let getValAsInt v = GetValueAsInt v ast
    GetUperRangeAux c getValAsInt (fun x -> x + 1I) (fun x -> x - 1I) ast 



let rec GetTypeUperRange (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) (ast:AstRoot) =
    let Intersect (cns) = cns |> Seq.fold(fun agr c -> uperIntersection(agr,GetUperRange c ast)) Full
    let GetSizeConstraintsContent(cns:seq<Asn1Constraint>) =
        seq {
            for c in cns do
                match c with 
                | SizeContraint(c1) -> yield c1
                | SingleValueContraint(asn1Val) ->
                    let asn1Val =  Ast.GetActualValue2 asn1Val ast  
                    let length = 
                        match kind, asn1Val.Kind with
                        | BitString, BitStringValue(bitVal)     -> bitVal.Value.Length
                        | BitString, OctetStringValue(bytes)    -> 8*bytes.Length
                        | OctetString, OctetStringValue(bytes)  -> bytes.Length
                        | IA5String , StringValue(strVal)   
                        | NumericString , StringValue(strVal)   -> strVal.Value.Length
                        | SequenceOf(_), SeqOfValue(vals)       -> vals.Length
                        | _                                     ->  raise (BugErrorException("Invalid combination"))
                    let vl = {Asn1Value.Kind = IntegerValue (loc length.AsBigInt); Location = emptyLocation}
                    yield SingleValueContraint vl
                | _                 -> ()
        } 
    match kind with
    | Integer       -> cons |> Intersect
    | BitString |IA5String | NumericString |OctetString  |SequenceOf(_) -> cons |> GetSizeConstraintsContent |> Intersect
    | Boolean | Choice(_)| Enumerated(_) | NullType | Real |Sequence(_)  -> raise (BugErrorException(""))
    | ReferenceType(modName,tasName, _)       -> 
        let parType = GetBaseTypeByName modName tasName ast
        let mergedCons = parType.Constraints @ cons
        GetTypeUperRange parType.Kind mergedCons ast



let rec GetTypeRange_real (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) (ast:AstRoot) =
    let rec GetUperRangeReal (c:Asn1Constraint) (ast:AstRoot) = 
        let getValAsReal v = GetValueAsDouble v ast
        GetUperRangeAux c getValAsReal (fun x -> x) (fun x -> x) ast
    match kind with
    | Real  -> cons |> Seq.fold(fun agr c -> uperIntersection(agr,GetUperRangeReal c ast)) Full
    | ReferenceType(modName,tasName, _)       -> 
        let parType = GetBaseTypeByName modName tasName ast
        let mergedCons = parType.Constraints @ cons
        GetTypeRange_real parType.Kind mergedCons ast
    | _     -> raise(BugErrorException "unexpected type")


type CharSet = array<char>
    

let GetDefaultCharSet(kind:Asn1TypeKind) =
    match kind with
    | NumericString     -> [| ' ';'0';'1';'2';'3';'4';'5';'6';'7';'8';'9'|]
    | IA5String         -> [|for i in 0..127 -> System.Convert.ToChar(i) |]
    | _                 -> raise ( BugErrorException("") )

let GetCharSetFromString(t, str:string) = str.ToCharArray() |> Seq.distinct |> Seq.toArray

let CharSetUnion(s1:CharSet, s2:CharSet) = [s1;s2] |>Seq.concat |> Seq.distinct |> Seq.toArray

let IntersectArrays(s1:array<'a>, s2:array<'a>) = 
    let cache = System.Collections.Generic.HashSet<'a>(s2)
    s1 |> Array.filter(fun ch -> cache.Contains(ch))
    
let GetCharSetFromMinMax(kind:Asn1TypeKind, a, b, minIsIn, maxIsIn) = 
    let defaultCharSet = GetDefaultCharSet(kind)
    let a1 = defaultCharSet |> Array.findIndex(fun ch -> ch = a)
    let a2 = defaultCharSet |> Array.findIndex(fun ch -> ch = b)
    let a1 = if minIsIn then a1 else a1+1
    let a2 = if maxIsIn then a2 else a2-1
    defaultCharSet.[a1..a2]


let rec GetUperRangeFrom (kind:Asn1TypeKind, c:Asn1Constraint, ast:AstRoot) =
    let rec GetRefValAsString (v:Asn1Value) =
        match v.Kind with
        | StringValue(a)             -> a.Value
        | RefValue(modName,valName)             -> GetRefValAsString (GetActualValue modName valName ast)
        | _                 -> raise (BugErrorException(""))
    match c with
    | SingleValueContraint(v1)        -> GetCharSetFromString(kind, GetRefValAsString(v1))
    | RangeContraint(v1,v2,minIsIn,maxIsIn)           -> 
        
        let a = GetRefValAsString(v1).ToCharArray().[0]
        let b = GetRefValAsString(v2).ToCharArray().[0]
        
        GetCharSetFromMinMax(kind, a, b,minIsIn,maxIsIn)
    | RangeContraint_val_MAX(v1, minIsIn)       ->
        let defaultSet = GetDefaultCharSet(kind)
        let a = GetRefValAsString(v1).ToCharArray().[0]
        GetCharSetFromMinMax(kind, a, defaultSet.[defaultSet.Length-1], minIsIn, true)
    | RangeContraint_MIN_val(v2, maxIsIn)       ->
        let defaultSet = GetDefaultCharSet(kind)
        let b = GetRefValAsString(v2).ToCharArray().[0]
        GetCharSetFromMinMax(kind, defaultSet.[0], b,true,maxIsIn)
    | RangeContraint_MIN_MAX           -> GetDefaultCharSet(kind)
    | UnionConstraint(c1,c2,_)            -> CharSetUnion(GetUperRangeFrom(kind,c1,ast), GetUperRangeFrom(kind,c2,ast))
    | IntersectionConstraint(c1,c2)     -> IntersectArrays(GetUperRangeFrom(kind,c1,ast), GetUperRangeFrom(kind,c2,ast))
    | AllExceptConstraint(c1)           -> GetDefaultCharSet(kind)
    | ExceptConstraint(c1,c2)           -> GetUperRangeFrom(kind,c1,ast)
    | RootConstraint(c1)                -> GetUperRangeFrom(kind,c1,ast)
    | RootConstraint2(c1,c2)            -> GetUperRangeFrom(kind,c1,ast)
    | WithComponentConstraint(_)        -> raise (BugErrorException(""))
    | WithComponentsConstraint(_)       -> raise (BugErrorException(""))
    | AlphabetContraint(_)              -> raise (BugErrorException(""))
    | SizeContraint(_)                  -> raise (BugErrorException(""))
    | TypeInclusionConstraint(modName, typeName)   -> 
        let actType = GetBaseTypeByName modName typeName ast
        let defaultCharSet = GetDefaultCharSet(kind)
        actType.Constraints |> Seq.fold (fun agr c -> IntersectArrays(agr,GetUperRangeFrom(kind, c, ast))) defaultCharSet

let rec GetTypeUperRangeFrom(kind:Asn1TypeKind, cons:list<Asn1Constraint>, ast) =
    let defaultCharSet = GetDefaultCharSet(kind)
    let Intersect (cns) = cns |> Seq.fold(fun agr c -> IntersectArrays(agr,GetUperRangeFrom(kind, c, ast))) defaultCharSet
    let GetAlphabetConstraintsContent(cns:seq<Asn1Constraint>) =
        seq {
            for c in cns do
                match c with 
                | AlphabetContraint(c1) -> yield c1
                | _                 -> ()
        } 
    match kind with
    | IA5String | NumericString -> cons |> GetAlphabetConstraintsContent |> Intersect
    | Integer | BitString |OctetString  |SequenceOf(_)  | Boolean | Choice(_)| Enumerated(_) | NullType | Real |Sequence(_)  
        -> raise (BugErrorException(""))
    | ReferenceType(modName, tasName, _)       -> 
        let parType = GetBaseTypeByName modName tasName ast
        let mergedCons = parType.Constraints @ cons
        GetTypeUperRangeFrom(parType.Kind, mergedCons, ast)







let AddSize (a,b) =
    match a,b with
    | (Bounded(a1), Bounded(b1))    -> Bounded(a1+b1)
    | _                             -> Infinite

let MaxSize(a,b) =
    match a,b with
    | (Bounded(a1), Bounded(b1))    -> Bounded(max a1 b1)
    | _                             -> Infinite

let MinSize(a,b) =
    match a,b with
    | (Bounded(a1), Bounded(b1))    -> Bounded(min a1 b1)
    | (Infinite, Bounded(b1))       -> Bounded(b1)
    | (Bounded(b1), Infinite)       -> Bounded(b1)
    | Infinite, Infinite            -> Infinite

let Asn1Size_to_String asn1Size = 
    match asn1Size with
    | Bounded(a)        -> a.ToString()
    | Infinite          -> "Infinite"



let rec uperGetSizableTypeInternalItemSizeInBits getTypeSize (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) (ast:AstRoot)=
    match kind with
    | OctetString               ->  Bounded(8I)
    | BitString(_)              ->  Bounded(1I)
    | IA5String  | NumericString  ->  
        let charSet = GetTypeUperRangeFrom(kind, cons, ast)
        let charSize = GetNumberOfBitsForNonNegativeInteger (BigInteger (charSet.Length-1))
        Bounded(charSize)
    | SequenceOf(innerType)     ->  
        (getTypeSize innerType.Kind innerType.Constraints ast)
    | _                         -> raise(BugErrorException "")



let rec uperGetMaxSizeInBits (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) (ast:AstRoot)=
    let GetIntegerSize uperRange =
        match uperRange with
        | Concrete(a,b)                   -> GetNumberOfBitsForNonNegativeInteger(b-a)
        | Empty                           -> BigInteger.Zero
        | Full | PosInf(_) |  NegInf(_)   -> (IntegerSize()+1I)*8I

    match kind with
    | Integer                   ->  
        let noRootConstraints = cons |> Seq.filter(fun c -> match c with RootConstraint(_) | RootConstraint2(_,_) -> true | _ -> false) |> Seq.isEmpty
        let size = GetIntegerSize(GetTypeUperRange kind cons ast)
        match noRootConstraints with
        |true ->   Bounded size
        |false ->  Bounded(size+1I)
    | Real                      ->  Bounded((5I+IntegerSize())*8I)
    | Enumerated(children)      ->  Bounded(GetNumberOfBitsForNonNegativeInteger(BigInteger((Seq.length children) - 1)))
    | NullType                  ->  Bounded(0I)
    | Boolean                   ->  Bounded(1I)
    | Sequence(children)        ->  
        let optionalChildren = children |> Seq.filter(fun c -> c.Optionality.IsSome)
        let optionalBitMaskSize = Bounded(BigInteger(Seq.length optionalChildren))
        let childrenSize = children |> 
                           Seq.filter(fun x -> not x.AcnInsertedField) |>
                           Seq.fold(fun accSize ch -> 
                                                    let childSize = uperGetMaxSizeInBits ch.Type.Kind ch.Type.Constraints ast
                                                    AddSize(accSize,childSize )) (Bounded(BigInteger(0)))
        AddSize (optionalBitMaskSize,childrenSize)
    | Choice(children)                 ->  
        let indexSize = Bounded(GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children)))
        let maxChildSize = children |> Seq.fold(fun accSize ch -> MaxSize(accSize, (uperGetMaxSizeInBits ch.Type.Kind ch.Type.Constraints ast) )) (Bounded(0I))
        AddSize(indexSize, maxChildSize)
    | ReferenceType(modName, tasName, _)       -> 
        let parType = GetBaseTypeByName modName tasName ast
        let mergedCons = parType.Constraints @ cons
        uperGetMaxSizeInBits parType.Kind mergedCons ast
    | OctetString               
    | BitString(_)              
    | IA5String  
    | NumericString             
    | SequenceOf(_)     ->  
        let innerItemSize = uperGetSizableTypeInternalItemSizeInBits uperGetMaxSizeInBits kind cons ast
        let uper = GetTypeUperRange kind cons ast
        match uper, innerItemSize  with
        | Empty, _                                          -> Bounded(0I)
        | _        , Infinite                               -> Infinite
        | Concrete(a,b), Bounded(v) when a=b && b<65536I    -> Bounded(b*v)
        | Concrete(a,b), Bounded(v) when a<>b  && b<65536I  -> Bounded(b*v + GetIntegerSize(uper))
        | Concrete(a,b), Bounded(v)                         -> Bounded(b*v + (b / 65536I + 3I) * 8I)
        | PosInf(a), Bounded(v)                             -> Infinite
        | Full,Bounded(v)                                   -> Infinite
        | NegInf(_), Bounded(v)                             -> raise(BugErrorException "")


let rec uperGetMinSizeInBits (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) (ast:AstRoot)=
    let GetIntegerSize uperRange =
        match uperRange with
        | Concrete(a,b)                   -> GetNumberOfBitsForNonNegativeInteger(b-a)
        | Empty                           -> BigInteger.Zero
        | Full | PosInf(_) |  NegInf(_)   -> 8I
    match kind with
    | Integer                   ->  
        let noRootConstraints = cons |> Seq.filter(fun c -> match c with RootConstraint(_) | RootConstraint2(_,_) -> true | _ -> false) |> Seq.isEmpty
        let size = GetIntegerSize(GetTypeUperRange kind cons ast)
        match noRootConstraints with
        |true   ->  Bounded size
        |false  ->  Bounded(size+1I)
    | Real                      ->  Bounded(8I)
    | NullType                  ->  Bounded(0I)
    | Boolean                   ->  Bounded(1I)
    | Enumerated(children)      ->  Bounded(GetNumberOfBitsForNonNegativeInteger(BigInteger((Seq.length children) - 1)))
    | Sequence(children)        ->  
        let optionalChildren = children |> Seq.filter(fun c -> c.Optionality.IsSome)
        let optionalBitMaskSize = Bounded(BigInteger(Seq.length optionalChildren))
        let childrenSize = children |> 
                           Seq.filter(fun x -> not x.AcnInsertedField) |>
                           Seq.filter(fun x -> x.Optionality.IsNone) |>
                           Seq.fold(fun accSize ch -> 
                                        let childSize = uperGetMinSizeInBits ch.Type.Kind ch.Type.Constraints ast
                                        AddSize(accSize,childSize )) (Bounded(0I))
        AddSize (optionalBitMaskSize,childrenSize)
    | Choice(children)                 ->  
        let indexSize = Bounded(GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children)))
        let minChildSize = children |> Seq.fold(fun accSize ch -> MinSize(accSize, (uperGetMaxSizeInBits ch.Type.Kind ch.Type.Constraints ast) )) (Infinite)
        AddSize(indexSize, minChildSize)
    | ReferenceType(modName, tasName, _)       -> 
        let parType = GetBaseTypeByName modName tasName ast
        let mergedCons = parType.Constraints @ cons
        uperGetMinSizeInBits parType.Kind mergedCons ast
    | OctetString                   
    | BitString(_)                  
    | IA5String  
    | NumericString    
    | SequenceOf(_)     ->  
        let innerItemSize = uperGetSizableTypeInternalItemSizeInBits uperGetMinSizeInBits kind cons ast
        let uper = GetTypeUperRange kind cons ast
        match uper, innerItemSize  with
        | Empty, _                                          -> Bounded(0I)
        | _        , Infinite                               -> Infinite
        | Concrete(a,b), Bounded(v) when a=b && b<65536I    -> Bounded(a*v)
        | Concrete(a,b), Bounded(v)                         -> Bounded(a*v + GetIntegerSize(uper))
        | PosInf(a), Bounded(v)                             -> Bounded(a*v + GetIntegerSize(uper))
        | Full,Bounded(v)                                   -> Bounded(8I)
        | NegInf(_), Bounded(v)                             -> raise(BugErrorException "")
    


let uperGetMaxSizeInBitsAsInt (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) loc (ast:AstRoot) =
    match (uperGetMaxSizeInBits kind cons ast) with
    | Bounded(a)        ->  a
    | Infinite          -> raise(SemanticError(loc,"Declared type may have infinite size. Use size constraints to limit the upper bound"))


let uperGetMaxSizeInBytesAsInt (kind:Asn1TypeKind) (cons:list<Asn1Constraint>) loc (ast:AstRoot)=
    let nBits = uperGetMaxSizeInBitsAsInt kind cons loc ast
    BigInteger(System.Math.Ceiling(double(nBits)/8.0))



let GetSizebaleMinMax typeKind cons r =
        match (GetTypeUperRange typeKind cons r) with
        |Concrete(min, max)        -> min, max
        |_                        -> raise(BugErrorException "SEQUENCE OF or OCTET STRING etc has no constraints")
