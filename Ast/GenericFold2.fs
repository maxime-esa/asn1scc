module GenericFold2
open Ast
open Monads
open FsUtils

let enumIntegerType = 
    {
        Asn1Type.Kind = Integer
        Constraints = []
        AcnProperties = []
        Location = FsUtils.emptyLocation
    }

let stringType = 
    {
        Asn1Type.Kind = IA5String
        Constraints = []
        AcnProperties = []
        Location = FsUtils.emptyLocation
    }

let sizeIntegerType = 
    {
        Asn1Type.Kind = Integer
        Constraints = [RangeContraint_val_MAX ({Asn1Value.Kind = IntegerValue(FsUtils.IntLoc.ByValue 0I); Location=FsUtils.emptyLocation},true)]
        AcnProperties = []
        Location = FsUtils.emptyLocation
    }





type ScopeNode =
    | MD of string      //MODULE
    | TA of string      //TYPE ASSIGNMENT
    | VA of string      //VALUE ASSIGNMENT
    | CH of string      //SEQUENCE OF CHOICE CHILD
    | SQF               //SEQUENCE OF CHILD
    | WITH_COMP              // WITH COMPONENT
    | WITH_COMPS of string  // WITH COMPONENTS
    | REF_TYPE of string*string //pass through ref type
    with
        member this.StrValue =
            match this with
            | MD strVal
            | TA strVal
            | VA strVal
            | CH strVal     -> strVal
            | SQF           -> "#"
            | WITH_COMP     -> "WCP"
            | WITH_COMPS strVal -> sprintf "%s(WC)" strVal
            | REF_TYPE  (s1,s2)    -> sprintf "%s.%s" s1 s2


type VarScopNode =
    | DV        //DEFAULT VALUE
    | NI  of string      //NAMED ITEM VALUE (enum)
    | CON of int         // constraint index
    | SQOV              //SEQUENCE OF VALUE
    | SQCHILD   of string   //child value (SEQUENCE, CHOICE)
    | VL of int         //value index
    with
        member this.StrValue =
            match this with
            | DV        -> "DV"
            | NI    ni  -> ni
            | VL   idx  -> "v" + idx.ToString()    
            | CON idx   -> "c" + idx.ToString()
            | SQOV      -> "#"
            | SQCHILD  s-> s

type Scope = {
    asn1TypeName : string option
    asn1VarName : string option
    typeID : ScopeNode list
    varID : VarScopNode list
}


let visitModule (md:Asn1Module) =
    {Scope.typeID=[MD md.Name.Value]; asn1TypeName=None; asn1VarName=None;varID=[]}

let visitTas (s:Scope) (ts:TypeAssignment) =
    {s with typeID=s.typeID@[TA ts.Name.Value]; asn1TypeName=Some ts.Name.Value; asn1VarName=None; varID=[]}

let visitVas (s:Scope) (vs:ValueAssignment) =
    {s with typeID=s.typeID@[VA vs.Name.Value]; asn1TypeName=None;asn1VarName=Some vs.Name.Value; varID=[]}

let visitRefType (md:string) (ts:string) =
    {Scope.typeID=[MD md; TA ts]; asn1TypeName=Some ts; asn1VarName=None;varID=[]}

let visitRefTypeThatHasWithCompCons (s:Scope) (md:string) (ts:string) =
    {s with typeID=s.typeID@[REF_TYPE (md,ts)]; asn1TypeName=None;asn1VarName=None; varID=[]}

let visitRevValue (md:string) (vs:string) =
    {Scope.typeID=[MD md; VA vs]; asn1TypeName=None; asn1VarName=Some vs;varID=[]}

let visitSeqOrChoiceChild (s:Scope) (ch:ChildInfo) =
    {s with typeID=s.typeID@[CH ch.Name.Value]; asn1TypeName=None;asn1VarName=None; varID=[]}

let visitSeqOfChild (s:Scope) =
    {s with typeID=s.typeID@[SQF]; asn1TypeName=None;asn1VarName=None; varID=[]}

let visitWithComponentChild (s:Scope) =
    {s with typeID=s.typeID@[WITH_COMP]; asn1TypeName=None;asn1VarName=None; varID=[]}

let visitDefaultValue (s:Scope) = 
    {s with varID=[DV]}

let visitNamedItemValue (s:Scope) (nm:NamedItem) = 
    {s with varID=[NI nm.Name.Value]}

let visitConstraint (s:Scope) = 
    {s with varID=s.varID@[CON 0]}

let visitSilbingConstraint (s:Scope) = 
    let idx, xs = 
        match s.varID |> List.rev with
        | (CON idx)::xs  -> idx, xs
        | _              -> raise(System.Exception "invalid call to visitSilbingConstraint")
    {s with varID=xs@[CON (idx+1)]}


let visitValue (s:Scope) = 
    {s with varID=s.varID@[VL 0]}

let visitSilbingValue (s:Scope) = 
    let idx, xs = 
        match s.varID |> List.rev with
        | (VL idx)::xs  -> idx, xs
        | _              -> raise(System.Exception "invalid call to visitSilbingConstraint")
    {s with varID=xs@[VL (idx+1)]}

let visitSeqOfValue (s:Scope) =
    {s with varID=s.varID@[SQOV]}

let visitSeqChildValue (s:Scope) childName =
    {s with varID=s.varID@[SQCHILD childName ]}

let error (loc: SrcLoc) format = 
    let doAfter s = 
        raise (SemanticError (loc, s))
    Printf.ksprintf doAfter format 

type CheckContext =
    | CheckContent
    | CheckSize          
    | CheckCharacter    


let foldAstRoot 
    rootFunc                    
    fileFunc        
    modFunc 
    tasFunc 
    vasFunc 
    refTypeFunc 
    integerFunc 
    realFunc
    ia5StringFunc
    numericStringFunc
    octetStringFunc
    nullTypeFunc
    bitStringFunc
    booleanFunc
    enumeratedFunc
    enmItemFunc 
    seqOfTypeFunc 
    seqTypeFunc 
    chTypeFunc 
    sequenceChildFunc 
    alwaysAbsentFunc
    alwaysPresentFunc
    optionalFunc
    defaultFunc
    choiceChildFunc 
    refValueFunc  
    enumValueFunc 
    intValFunc 
    realValFunc 
    ia5StringValFunc 
    numStringValFunc 
    boolValFunc 
    octetStringValueFunc 
    bitStringValueFunc 
    nullValueFunc 
    seqOfValueFunc 
    seqValueFunc 
    chValueFunc
    singleValueContraintFunc 
    rangeContraintFunc 
    rangeContraint_val_MAXFunc
    rangeContraint_MIN_valFunc
    rangeContraint_MIN_MAXFunc
    typeInclConstraintFunc
    unionConstraintFunc
    intersectionConstraintFunc
    allExceptConstraintFunc
    exceptConstraintFunc
    rootConstraintFunc
    rootConstraint2Func
    sizeContraint 
    alphabetContraint
    withComponentConstraint
    (r:AstRoot) =
    
    let rec loopAstRoot (r:AstRoot) =
        let files = r.Files |> List.map (loopFile r)
        rootFunc r files
    and loopFile (r:AstRoot) (f:Asn1File) =
        let modules = f.Modules |> List.map (loopModule r f)
        fileFunc r f modules
    and loopModule (r:AstRoot) (f:Asn1File) (m:Asn1Module) =
        let s = visitModule m
        let tases = m.TypeAssignments |> List.map (loopTypeAssignment s r f m)
        let vases = m.ValueAssignments |> List.map  (loopValueAssignments s r f m)
        modFunc r f m tases vases
    and loopTypeAssignment (s:Scope) (r:AstRoot) (f:Asn1File) (m:Asn1Module) (tas:TypeAssignment) =
        let s = visitTas s tas
        let asn1Type = loopType (s,tas.Type)
        tasFunc r f m tas asn1Type
    and loopValueAssignments (s:Scope) (r:AstRoot) (f:Asn1File) (m:Asn1Module) (vas:ValueAssignment) =
        let s = visitVas s vas
        let actType = GetActualType vas.Type  r
        let asn1Type = loopType (s, vas.Type)
        let asn1Value = loopAsn1Value (s, actType) (s,vas.Value)
        vasFunc r f m vas asn1Type asn1Value
    and loopType (s:Scope, t:Asn1Type) =
        let conScope = visitConstraint s
        let newCons = t.Constraints |> List.map  (fun c -> loopConstraint (s,t) CheckContent (conScope,c))
        match t.Kind with
        | ReferenceType (mdName,tasName, tabularized) -> 
            let withCompCons = t.Constraints |> List.choose(fun c -> match c with WithComponentConstraint _ -> Some c| WithComponentsConstraint _ -> Some c | _ -> None)
            match withCompCons with
            | [] ->
                let refTypeScope = visitRefType mdName.Value tasName.Value
                let oldBaseType = (Ast.GetBaseType t r)
                let baseType = loopType (refTypeScope, {oldBaseType with Constraints = oldBaseType.Constraints@withCompCons})
                refTypeFunc s t newCons baseType mdName tasName tabularized false
            | _  -> 
                let refTypeScope = visitRefTypeThatHasWithCompCons s mdName.Value tasName.Value
                let oldBaseType = (Ast.GetBaseType t r)
                let baseType = loopType (refTypeScope, {oldBaseType with Constraints = oldBaseType.Constraints@withCompCons})
                refTypeFunc s t newCons baseType mdName tasName tabularized true
        | Integer       ->  integerFunc s t newCons
        | Real          ->  realFunc s t newCons
        | IA5String     ->  ia5StringFunc s  t newCons
        | NumericString    -> numericStringFunc s  t newCons
        | OctetString    -> octetStringFunc s t newCons
        | NullType    -> nullTypeFunc s t newCons
        | BitString    -> bitStringFunc s t newCons
        | Boolean           ->booleanFunc s t newCons
        | Enumerated (enmItems) ->  
            let newEnmItems = enmItems |> List.map (fun ni -> loopNamedItem s ni)
            enumeratedFunc s  t newCons newEnmItems 
        | SequenceOf (innerType)  ->
            let childScope = visitSeqOfChild s
            let withCompCons = t.Constraints |> List.choose(fun c -> match c with WithComponentConstraint wc -> Some wc | _ -> None)
            let newInnerType = 
                match withCompCons with
                | []    -> loopType (childScope, innerType)
                | _     -> loopType (visitWithComponentChild childScope, {innerType with Constraints = innerType.Constraints@withCompCons})
            seqOfTypeFunc s  t newCons newInnerType 
        | Sequence (children)     ->
            let newChildren = 
                children |> List.map  (fun chInfo -> 
                    let childScope = visitSeqOrChoiceChild s chInfo
                    loopSequenceChild childScope chInfo)
            seqTypeFunc s  t newCons newChildren 
        | Choice (children)       ->
            let newChildren = 
                children |> List.map  (fun chInfo ->
                    let childScope = visitSeqOrChoiceChild s chInfo
                    loopChoiceChild childScope chInfo)
            chTypeFunc s  t newCons newChildren 
    and loopNamedItem (s:Scope) (ni:NamedItem) =
            match ni._value with
            | Some v    ->
                let newValue = loopAsn1Value (s, enumIntegerType) ((visitNamedItemValue s ni),v)
                enmItemFunc  ni (Some newValue)
            | None      ->
                enmItemFunc  ni  None
    and loopSequenceChild (ts:Scope)  (chInfo:ChildInfo) =
            let newType = loopType (ts,chInfo.Type)
            let newOptionality = 
                    match chInfo.Optionality with
                    | Some Asn1Optionality.AlwaysAbsent     -> Some (alwaysAbsentFunc ts)
                    | Some Asn1Optionality.AlwaysPresent    -> Some (alwaysPresentFunc ts)
                    | Some Asn1Optionality.Optional         -> Some (optionalFunc ts)
                    | None                                  -> None
                    | Some  (Asn1Optionality.Default   vl)  ->
                        let eqType = GetActualType chInfo.Type r
                        let newValue = loopAsn1Value  (ts, eqType) ((visitDefaultValue ts), vl)
                        Some (defaultFunc ts newValue)
            sequenceChildFunc ts chInfo newType newOptionality

    and loopChoiceChild (ts:Scope)  (chInfo:ChildInfo) =
            let newType = loopType (ts, chInfo.Type)
            choiceChildFunc ts   chInfo newType
    and loopAsn1Value (ts:Scope, t:Asn1Type) (vs:Scope, v:Asn1Value) =
        match v.Kind, t.Kind with
        | RefValue (md,vas), Enumerated (enmItems)   ->
                match enmItems |> Seq.tryFind (fun x -> x.Name.Value = vas.Value) with
                | Some enmItem    ->
                        enumValueFunc ts vs v vas            
                | None          ->
                    
                        let actValue = GetBaseValue md vas r
                        let newActVal = loopAsn1Value (ts,t) (visitRevValue md.Value vas.Value,actValue)
                        refValueFunc ts vs v (md, vas) newActVal            
        | RefValue (md,vas), _   ->
                        let actValue = GetBaseValue md vas r
                        let newActVal = loopAsn1Value (ts,t) (visitRevValue md.Value vas.Value,actValue)
                        refValueFunc ts vs v (md, vas) newActVal            
        | IntegerValue bi, Integer          ->
            intValFunc ts vs v bi
        | IntegerValue bi, Real  _           ->
            let dc:double = (double)bi.Value
            realValFunc ts vs v {Value=dc;Location=v.Location}
        | RealValue dc , Real   _                  -> 
            realValFunc ts vs v dc
        | StringValue str, IA5String _   -> 
                ia5StringValFunc ts vs v str
        | StringValue str , NumericString _   -> 
                numStringValFunc ts vs v str
        | BooleanValue b, Boolean _       ->
                boolValFunc ts vs v b
        | OctetStringValue b, OctetString _         ->
                octetStringValueFunc ts vs v b
        | OctetStringValue b, BitString _        ->
                octetStringValueFunc ts vs v b
        | BitStringValue b, BitString _           ->
                bitStringValueFunc ts vs v b 
        | NullValue , NullType _   ->
                nullValueFunc ts vs v
        | SeqOfValue  vals, SequenceOf chType    ->
                let eqType = GetActualType chType r
                let newTSCh = visitSeqOfChild ts
                let newVals = vals |> List.map  (fun chVal -> loopAsn1Value (newTSCh, eqType) ((visitSeqOfValue vs), chVal))
                seqOfValueFunc ts vs v  newVals
        | SeqValue    namedValues, Sequence children ->
                let newValues =  namedValues |> List.map  (loopSeqValueChild ts children vs )
                seqValueFunc ts vs v newValues
        | ChValue (name,vl), Choice children         ->
            match children |> Seq.tryFind(fun ch -> ch.Name.Value = name.Value) with
            | Some chType   ->
                    let chTs = visitSeqOrChoiceChild ts chType
                    let eqType = GetActualType chType.Type r 
                    let newValue = loopAsn1Value (chTs,eqType) ((visitSeqChildValue vs name.Value),vl)
                    chValueFunc ts vs v name newValue
            | None  -> 
                error name.Location "Invalid alternative name '%s'" name.Value
        | _         ->
            error v.Location "Invalid combination ASN.1 type and ASN.1 value"


    and loopSeqValueChild (ts:Scope)  (children: list<ChildInfo>)  (vs:Scope) (nm:StringLoc, chv:Asn1Value) = 
            let child = 
                match children |> Seq.tryFind (fun ch -> ch.Name.Value = nm.Value) with
                | Some ch -> ch
                | None    -> error nm.Location "Invalid child name '%s'" nm.Value
            let chTs = visitSeqOrChoiceChild ts child
            let eqType = GetActualType child.Type r
            let newValue = loopAsn1Value (chTs,eqType) ((visitSeqChildValue vs nm.Value),chv)
            (nm,newValue)

    and loopConstraint (ts:Scope, t:Asn1Type) (checContent:CheckContext) (cs:Scope, c:Asn1Constraint) =
        let vtype =
            match checContent with
            | CheckSize         -> sizeIntegerType
            | CheckCharacter    -> stringType
            | CheckContent      -> GetActualType t r

        match c with
        | SingleValueContraint v        ->
                let newValue = loopAsn1Value (ts,vtype) (visitValue cs,v)
                singleValueContraintFunc ts t checContent newValue
        | RangeContraint(v1,v2,b1,b2)   -> 
                let vs1 = visitValue cs
                let vs2 = visitSilbingValue vs1
                let newValue1 = loopAsn1Value (ts,vtype) (vs1,v1)
                let newValue2 = loopAsn1Value (ts,vtype) (vs2,v2)
                rangeContraintFunc ts t checContent newValue1 newValue2 b1 b2
        | RangeContraint_val_MAX (v,b)  ->
                let newValue = loopAsn1Value (ts,vtype) (visitValue cs,v)
                rangeContraint_val_MAXFunc ts t checContent newValue b
        | RangeContraint_MIN_val (v,b)  ->
                let newValue = loopAsn1Value (ts,vtype) (visitValue cs,v)
                rangeContraint_MIN_valFunc ts t checContent newValue  b
        | RangeContraint_MIN_MAX             -> 
                rangeContraint_MIN_MAXFunc ts t checContent 
        | TypeInclusionConstraint (md,tas)  ->
                let actTypeAllCons = GetActualTypeByNameAllConsIncluded md tas r
                let agrCon = 
                    match actTypeAllCons.Constraints with
                    | []    -> None
                    | x::[] -> Some x
                    | x::xs -> 
                        let aa = xs |> List.fold(fun s cc -> IntersectionConstraint (s,cc)) x
                        Some aa
                match agrCon with
                | Some c1 ->
                    let nc = loopConstraint (ts,t) checContent ((visitConstraint cs),c1)
                    typeInclConstraintFunc ts t (Some nc)
                | None -> typeInclConstraintFunc ts t None
        | UnionConstraint (c1,c2, virtualCon)      ->
                let cs1 = visitConstraint cs
                let cs2 = visitSilbingConstraint cs1
                let nc1 = loopConstraint (ts,t) checContent (cs1,c1)
                let nc2 = loopConstraint (ts,t) checContent (cs2,c2)
                unionConstraintFunc ts t nc1 nc2 virtualCon
        | IntersectionConstraint(c1,c2)         ->
                let cs1 = visitConstraint cs
                let cs2 = visitSilbingConstraint cs1
                let nc1 = loopConstraint (ts,t) checContent (cs1,c1)
                let nc2 = loopConstraint (ts,t) checContent (cs2,c2)
                intersectionConstraintFunc ts t nc1 nc2
        | AllExceptConstraint c1 ->
                let nc = loopConstraint (ts,t) checContent ((visitConstraint cs),c1)
                allExceptConstraintFunc ts t nc
        | ExceptConstraint (c1,c2)  ->
                let cs1 = visitConstraint cs
                let cs2 = visitSilbingConstraint cs1
                let nc1 = loopConstraint (ts,t) checContent (cs1,c1)
                let nc2 = loopConstraint (ts,t) checContent (cs2,c2)
                exceptConstraintFunc ts t nc1 nc2
        | RootConstraint c1  ->
                let nc = loopConstraint (ts,t) checContent ((visitConstraint cs),c1)
                rootConstraintFunc ts t nc 
        | RootConstraint2 (c1,c2)  ->
                let cs1 = visitConstraint cs
                let cs2 = visitSilbingConstraint cs1
                let nc1 = loopConstraint (ts,t) checContent (cs1,c1)
                let nc2 = loopConstraint (ts,t) checContent (cs2,c2)
                rootConstraint2Func ts t nc1 nc2
        | SizeContraint(sc)         -> 
                let nc = loopConstraint (ts,t) CheckSize (visitConstraint cs,sc)
                sizeContraint ts t nc
        | AlphabetContraint c       -> 
                let nc = loopConstraint (ts, t) CheckCharacter (visitConstraint cs,c)
                alphabetContraint ts t nc
        | WithComponentConstraint c          -> withComponentConstraint ts t
        | WithComponentsConstraint _         -> raise(BugErrorException "This constraint should have been removed")
                

    loopAstRoot r 


