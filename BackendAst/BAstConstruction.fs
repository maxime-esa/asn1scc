module BAstConstruction
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open Constraints
open FsUtils
open BAst

type State = {
    anonymousTypes : Asn1Type list
    anonymousValues : Asn1GenericValue list
}
with 
    member this.add (other:State) =
        {State.anonymousTypes = this.anonymousTypes@other.anonymousTypes; anonymousValues = this.anonymousValues@other.anonymousValues}


let combineStates (states:State list)= 
    states |> List.fold (fun s c -> {State.anonymousTypes = s.anonymousTypes@c.anonymousTypes; anonymousValues = s.anonymousValues@c.anonymousValues}) {State.anonymousTypes =[]; anonymousValues = []}

let addValue (s:State) (v:Asn1GenericValue)=
    {s with anonymousValues=s.anonymousValues@[v]}

let smap = CloneTree.foldMap



let createAstRoot (s:State) (sr:Ast.AstRoot) (dfiles: Asn1File list)  =
    {
        AstRoot.Files = dfiles 
        Encodings = sr.Encodings
        GenerateEqualFunctions = sr.GenerateEqualFunctions
        TypePrefix = sr.TypePrefix
        AstXmlAbsFileName = sr.AstXmlAbsFileName
        IcdUperHtmlFileName = sr.IcdUperHtmlFileName
        IcdAcnHtmlFileName = sr.IcdAcnHtmlFileName
        CheckWithOss = sr.CheckWithOss
        mappingFunctionsModule = sr.mappingFunctionsModule
        TypeAssignments = s.anonymousTypes 
        ValueAssignments = s.anonymousValues 
        valsMap = 
            let aa = s.anonymousValues |> List.map(fun v -> v.id, v) 
            aa |> Seq.groupBy(fun (id,t) -> id) |> Seq.filter(fun (id, gr) -> gr |> (*Seq.distinct |>*) Seq.length > 1) |> Seq.iter (fun x -> printfn "%A" x)
            aa |> Map.ofList
        typesMap = 
            let aa = s.anonymousTypes |> List.map(fun v -> v.id, v)
            aa |> Seq.groupBy(fun (id,t) -> id) |> Seq.filter(fun (id, gr) -> gr |> (*Seq.distinct |>*) Seq.length > 1) |> Seq.iter (fun x -> printfn "%A" x)
            aa |> Map.ofList

    }

let createAsn1File (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (newMods:Asn1Module list)  = 
    {
        Asn1File.FileName = f.FileName;
        Tokens = f.Tokens
        Modules  = newMods 
    },s

let createAsn1Module (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (newtases: Asn1Type list ) (vases:Asn1GenericValue list ) = 
    {
        Asn1Module.Name = m.Name.Value
        Imports = m.Imports
        Exports = m.Exports
        Comments = m.Comments
    }, s


let createTypeAssignment (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (tas:Ast.TypeAssignment) (newType:Asn1Type) = 
    newType,s

let createValueAssignment (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (vas:Ast.ValueAssignment) (t:Asn1Type) (v:Asn1GenericValue) = 
    v, s

     

let createChildInfo (st:State) s (ch:Ast.ChildInfo) (newType:Asn1Type) (newOptionality:Asn1Optionality option) = 
    {
        ChildInfo.Name = ch.Name.Value
        refToType = newType.id
        Optionality = newOptionality
        Comments = ch.Comments
    }, st

let createChoiceChildInfo (st:State) s (ch:Ast.ChildInfo) (newType:Asn1Type) = 
    {
        ChildInfo.Name = ch.Name.Value
        refToType = newType.id
        Optionality = None
        Comments = ch.Comments
    }, st

let createType (s:State) (ts:GenericFold2.UserDefinedTypeScope) (oldType:Ast.Asn1Type) (newCons:((Asn1AnyConstraint) option ) list, fromWithComps:((Asn1AnyConstraint) option ) list) (baseTypeId : ReferenceToType option) (newKind:Asn1Type)=
    let tranformCons func =
        let a = newCons |> List.choose id |> List.map (fun c -> false, func c)
        let b = fromWithComps |> List.choose id |> List.map (fun c -> true, func c)
        a@b
    //; Location=emptyLocation; id=ReferenceToType []        
    let ret = 
        match newKind with
        | Integer       t              -> 
            let cons = tranformCons ConstraintsMapping.getIntegerTypeConstraint 
            let uperR = 
                let uperCons = cons |> List.filter(fun (withCom, c) -> not withCom) |> List.map snd
                getIntTypeConstraintUperRange uperCons oldType.Location
            Integer      {t with cons = cons; uperRange = uperR; Location=oldType.Location; id=ReferenceToType ts}
        | Real          t              -> 
            let cons = tranformCons ConstraintsMapping.getRealTypeConstraint 
            let uperR = 
                let uperCons = cons |> List.filter(fun (withCom, c) -> not withCom) |> List.map snd
                getRealTypeConstraintUperRange uperCons oldType.Location
            Real         {t with cons = cons; uperRange = uperR; Location=oldType.Location; id=ReferenceToType ts}
        | IA5String     n              -> 
            let cons = n.cons@(tranformCons ConstraintsMapping.getIA5StringConstraint)
            let uperCons = cons |> List.filter(fun (withCom, c) -> not withCom) |> List.map snd
            let sizeUperRange = getSrtingSizeUperRange uperCons oldType.Location
            let charUperRange = getSrtingAlphaUperRange uperCons oldType.Location
            IA5String    {n with cons = cons; sizeUperRange=sizeUperRange; charUperRange=charUperRange; Location=oldType.Location; id=ReferenceToType ts}
        | OctetString   t              -> 
            let cons = tranformCons ConstraintsMapping.getOctetStringConstraint
            let uperCons = cons |> List.filter(fun (withCom, c) -> not withCom) |> List.map snd
            let sizeUperRange = getOctetStringUperRange uperCons oldType.Location
            OctetString  {t with OctetString.cons = cons; sizeUperRange=sizeUperRange; Location=oldType.Location; id=ReferenceToType ts}
        | NullType     t              -> NullType {t with  Location=oldType.Location; id=ReferenceToType ts}
        | BitString    t               -> 
            let cons = tranformCons ConstraintsMapping.getBitStringConstraint
            let uperCons = cons |> List.filter(fun (withCom, c) -> not withCom) |> List.map snd
            let sizeUperRange = getBitStringUperRange uperCons oldType.Location
            BitString    {t with cons = cons; sizeUperRange=sizeUperRange; Location=oldType.Location; id=ReferenceToType ts}
        | Boolean      t               -> 
            Boolean    {t with cons=tranformCons ConstraintsMapping.getBoolConstraint; Location=oldType.Location; id=ReferenceToType ts}
        | Enumerated   enum            -> 
            Enumerated  {enum with cons = tranformCons ConstraintsMapping.getEnumConstraint; Location=oldType.Location; id=ReferenceToType ts}
        | SequenceOf    sqOf           -> 
            let cons = tranformCons ConstraintsMapping.getSequenceOfConstraint
            let uperCons = cons |> List.filter(fun (withCom, c) -> not withCom) |> List.map snd
            let sizeUperRange = getSequenceOfUperRange uperCons oldType.Location
            SequenceOf  {sqOf with cons=cons; sizeUperRange = sizeUperRange; Location=oldType.Location; id=ReferenceToType ts}
        | Sequence      sq             -> 
            Sequence    {sq with cons=tranformCons ConstraintsMapping.getSequenceConstraint; Location=oldType.Location; id=ReferenceToType ts }
        | Choice        ch             -> 
            Choice      {ch with cons=tranformCons ConstraintsMapping.getChoiceConstraint; Location=oldType.Location; id=ReferenceToType ts }

    //printfn "Creating type with id %s" (ret.id.ToString())
    ret, {s with anonymousTypes = s.anonymousTypes@[ret]}

let createValue (us:State) (asn1ValName:(StringLoc*StringLoc) option) (ts:GenericFold2.UserDefinedTypeScope) (vs:GenericFold2.UserDefinedVarScope) (v:Asn1GenericValue) =
    (*let ret = 
        {
            Asn1GenericValue.asn1Name = asn1ValName 
            id = ReferenceToValue (ts, vs)
            //baseValue = baseValue
            refToType = ReferenceToType ts
            Kind = kind
        }
    ret, {us with anonymousValues=us.anonymousValues@[ret]}
    *)
    v, {us with anonymousValues=us.anonymousValues@[v]}


let createValidationAst (lang:Ast.ProgrammingLanguage) (app:Ast.AstRoot)  =
    let l_aux (asn1ValName: (StringLoc*StringLoc) option) = 
        match asn1ValName with
        | None          -> Literal
        | Some (md,vs)  ->  ReferenceToAsn1NamedValue  {Asn1ValueName.moduName=md.Value; vasName=vs.Value}
    let s_aux v us = 
        v, {us with anonymousValues=us.anonymousValues@[v]}
    GenericFold2.foldAstRoot
        //1. rootFunc r files
        createAstRoot

        //2. fileFunc r f modules
        createAsn1File

        //3. modFunc r f m tases vases
        createAsn1Module

        //4. tasFunc r f m tas asn1Type
        createTypeAssignment
        
        //5. vasFunc r f m vas asn1Type asn1Value
        createValueAssignment

        //6. typeFunc s t newTypeKind baseTypeId (newCons,fromWithComps)
        (fun ustate s t newTypeKind baseTypeId (newCons,fromWithComps) -> 
            createType ustate s t (newCons,fromWithComps) (baseTypeId |> Option.map(fun  x -> ReferenceToType x)) newTypeKind )

        //7. refTypeFunc s mdName tasName tabularized 
        (fun ustate  mdName tasName tabularized newBaseType -> 
            let retKind = 
                match newBaseType with
                | Integer      ti   -> Integer      {ti with baseType = Some ti}
                | Real         ti   -> Real         {ti with baseType = Some ti}
                | IA5String    ti   -> IA5String    {ti with baseType = Some ti}
                | OctetString  ti   -> OctetString  {ti with baseType = Some ti}
                | NullType     ti   -> NullType     {ti with baseType = Some ti} 
                | BitString    ti   -> BitString    {ti with baseType = Some ti}
                | Boolean      ti   -> Boolean      {ti with baseType = Some ti}
                | Enumerated   ti   -> Enumerated   {ti with baseType = Some ti}
                | SequenceOf   ti   -> SequenceOf   {ti with baseType = Some ti}
                | Sequence     ti   -> Sequence     {ti with baseType = Some ti}
                | Choice       ti   -> Choice       {ti with baseType = Some ti}
            retKind, ustate)

        //8 integerFunc s 
        (fun ustate  ->  Integer {Integer.cons=[]; uperRange=Full; baseType=None; Location=emptyLocation; id=ReferenceToType []},ustate)

        //9 realFunc s 
        (fun ustate  -> Real {Real.cons = []; uperRange = Full; baseType=None; Location=emptyLocation; id=ReferenceToType []}, ustate)

        //10 ia5StringFunc s 
        (fun ustate  -> IA5String {StringType.cons = []; sizeUperRange=Full; charUperRange=Full; baseType=None; Location=emptyLocation; id=ReferenceToType []}, ustate)

        //11 numericStringFunc s
        (fun ustate  -> 
            let zeroToNine = Constraints.RangeContraint (('0',None), ('9',None),true,true)
            let space      = Constraints.RangeSingleValueConstraint (" ", None)
            let numericCon = Constraints.AlphabetContraint (Constraints.RangeUnionConstraint (zeroToNine, space, true))
            let strType = {StringType.cons = [false,numericCon]; sizeUperRange=Full; charUperRange=Full; baseType=None; Location=emptyLocation; id=ReferenceToType []}
            IA5String strType, ustate)

        //12 octetStringFunc
        (fun ustate -> OctetString {OctetString.cons = []; sizeUperRange=Full; baseType=None; Location=emptyLocation; id=ReferenceToType []}, ustate)

        //13 nullTypeFunc
        (fun ustate -> NullType {NullType.baseType=None; Location=emptyLocation; id=ReferenceToType []}, ustate)

        //14 bitStringFunc
        (fun ustate -> BitString {BitString.cons = []; sizeUperRange=Full; baseType=None; Location=emptyLocation; id=ReferenceToType []}, ustate)

        //15 booleanFunc
        (fun ustate -> Boolean {Boolean.cons=[]; baseType=None; Location=emptyLocation; id=ReferenceToType []}, ustate)

        //16 enumeratedFunc 
        (fun ustate (enmItems : Ast.NamedItem list)-> 
            let newEnmItems, userDefinedValues = 
                match enmItems |> Seq.exists (fun nm -> nm._value.IsSome) with
                | false ->
                    enmItems |> List.mapi(fun i x -> {EnumItem.name = x.Name.Value;  Value = BigInteger i; comments = x.Comments|> Seq.toList} ), false
                | true  ->
                    let withVals = RemoveNumericStringsAndFixEnums.allocatedValuesToAllEnumItems enmItems app 
                    withVals |> List.mapi(fun i x -> {EnumItem.name = x.Name.Value;  Value = BigInteger i; comments = x.Comments|> Seq.toList} ), true
            (Enumerated {Enumerated.items = newEnmItems; userDefinedValues = userDefinedValues; cons=[]; baseType=None; Location=emptyLocation; id=ReferenceToType []}), ustate)

        //17 enmItemFunc
        (fun ustate ni newVal -> 0, ustate)

        //18 seqOfTypeFunc 
        (fun ustate newInnerType -> 
            (SequenceOf {SequenceOf.childTypeRef=newInnerType.id; cons=[]; sizeUperRange=Full; baseType=None; Location=emptyLocation; id=ReferenceToType []}), ustate)

        //19 seqTypeFunc 
        (fun ustate newChildren -> 
            (Sequence {Sequence.children=newChildren; cons=[]; baseType=None; Location=emptyLocation; id=ReferenceToType []}) , ustate)

        //20 chTypeFunc 
        (fun ustate newChildren -> 
            (Choice {Choice.children=newChildren; cons=[]; baseType=None; Location=emptyLocation; id=ReferenceToType []}), ustate)

        //21 sequenceChildFunc 
        createChildInfo

        //22 alwaysAbsentFunc
        (fun s -> Asn1Optionality.AlwaysAbsent)

        //23 alwaysPresentFunc
        (fun s -> Asn1Optionality.AlwaysPresent)

        //24 optionalFunc
        (fun s -> Asn1Optionality.Optional)

        //25 defaultFunc
        (fun s (newValue) -> 
            Asn1Optionality.Default newValue)

        //26 choiceChildFunc
        createChoiceChildInfo

        //27 refValueFunc 
        (fun _ -> 0) 

        //28 enumValueFunc
        (fun us asn1ValName ts vs v nmItem -> 
            let ret = EnumValue {EnumValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=nmItem.Value}
            s_aux ret us)

        //29 intValFunc
        (fun us asn1ValName ts vs v bi -> 
            let ret = IntegerValue {IntegerValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=bi.Value}
            s_aux ret us)

        //30 realValFunc
        (fun us asn1ValName ts vs v bi -> 
            let ret = RealValue {RealValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=bi.Value}
            s_aux ret us)

        //31 ia5StringValFunc 
        (fun us asn1ValName ts vs v str -> 
            let ret = StringValue {StringValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=str.Value}
            s_aux ret us)

        //32 numStringValFunc 
        (fun us asn1ValName ts vs v str -> 
            let ret = StringValue {StringValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=str.Value}
            s_aux ret us)

        //33 boolValFunc 
        (fun us asn1ValName ts vs v b -> 
            let ret = BooleanValue {BooleanValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=b.Value}
            s_aux ret us)

        //34 octetStringValueFunc
        (fun us asn1ValName ts vs v bytes -> 
            let ret = OctetStringValue {OctetStringValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=bytes |> List.map(fun b->b.Value)}
            s_aux ret us)
            //createValue us asn1ValName ts vs  (OctetStringValue (bytes |> List.map(fun b->b.Value))) )

        //35 bitStringValueFunc
        (fun us asn1ValName ts vs v b -> 
            let ret = BitStringValue {BitStringValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=b.Value}
            s_aux ret us)

        //36 nullValueFunc
        (fun us asn1ValName  ts vs v  -> 
            let ret = NullValue {NullValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=()}
            s_aux ret us)

        //37 seqOfValueFunc s t v actType  newVals
        (fun us asn1ValName ts vs v  newVals -> 
            let ret = SeqOfValue {SeqOfValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=newVals}
            s_aux ret us)

        //38 seqValueFunc 
        (fun us asn1ValName ts vs v  newVals -> 
            let newVals = newVals |> List.map (fun (nm, (v)) -> {NamedValue.name=nm.Value;Value=v})
            let ret = SeqValue {SeqValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value=newVals}
            s_aux ret us)

        //39 chValueFunc s t v actType name newValue
        (fun us asn1ValName ts vs v name newChValue -> 
            let ret = ChValue {ChValue.litOrRef=l_aux asn1ValName; id=ReferenceToValue (ts, vs); refToType=ReferenceToType ts; Value={NamedValue.name=name.Value;Value=newChValue}}
            s_aux ret us)

        //40 singleValueContraintFunc s t checContent actType newValue
        (fun us ts t checContent newValue-> 
            Some (AnySingleValueContraint newValue), us)

        //41 rangeContraintFunc s t checContent actType newValue1 newValue2 b1 b2
        (fun us ts t checContent (newValue1) (newValue2) b1 b2 -> 
            Some (AnyRangeContraint(newValue1, newValue2, b1, b2)), us)

        //42 rangeContraint_val_MAXFunc s t checContent actType newValue  b
        (fun us ts t checContent (newValue) b -> 
            Some (AnyRangeContraint_val_MAX (newValue,b)), us)

        //43 rangeContraint_MIN_valFunc s t checContent actType newValue  b
        (fun us ts t checContent (newValue) b  -> 
            Some (AnyRangeContraint_MIN_val(newValue,b)), us )

        //44 rangeContraint_MIN_MAXFunc  s t checContent actType
        (fun us ts t checContent -> None, us)

        //45 typeInclConstraintFunc s t actType (md,tas)
        (fun us ts t otherCon -> 
            match otherCon with
            | Some x -> x, us
            | None    -> None, us
         )

        //46 unionConstraintFunc s t actType nc1 nc2
        (fun us ts t x1 x2 virtualCon -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)  -> Some (AnyUnionConstraint (nc1, nc2, virtualCon)), us
            | Some (nc1), None        -> None, us
            | None, Some (nc2)        -> None, us
            | None, None              -> None, us)

        //47 intersectionConstraintFunc s t actType nc1 nc2
        (fun us ts t x1 x2 -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)  -> Some (AnyIntersectionConstraint (nc1,nc2)), us
            | Some (nc1), None        -> Some (nc1), us
            | None, Some (nc2)        -> Some (nc2), us
            | None, None              -> None, us)

        //48 allExceptConstraintFunc s t actType nc
        (fun  us ts t x1 -> 
            match x1 with
            | Some (nc1)   -> Some (AnyAllExceptConstraint nc1), us
            | None            -> raise(SemanticError(t.Location, (sprintf "EXCEPT constraint makes type to allow no values. Consider changing the EXCET part"))) )

        //49 exceptConstraintFunc s t actType nc1 nc2
        (fun us ts t x1 x2 -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)  -> Some (AnyExceptConstraint(nc1,nc2)), us
            | Some (nc1), None           -> raise(SemanticError(t.Location, (sprintf "EXCEPT constraint makes type to allow no values. Consider changing the EXCET part")))
            | None, Some (nc2)           -> Some (nc2), us
            | None, None                 -> raise(SemanticError(t.Location, (sprintf "EXCEPT constraint makes type to allow no values. Consider changing the EXCET part")))
        )

        //50 rootConstraintFunc s t actType nc
        (fun us ts t x1 -> x1 |> Option.map (fun (nc) -> AnyRootConstraint nc), us )

        //51 rootConstraint2Func s t actType nc1 nc2
        (fun us ts t x1 x2 -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)     -> Some (AnyRootConstraint2 (nc1,nc2)), us
            | Some (nc1), None           -> None, us
            | None, Some (nc2)           -> None, us
            | None, None                 -> None, us)
        
        //52 sizeContraint 
        (fun us ts t x1 -> x1 |> Option.map (fun (nc) -> AnySizeContraint nc), us )
        
        //53 alphabetContraint
        (fun us ts t x1 -> x1 |> Option.map (fun (nc) -> AnyAlphabetContraint nc), us )

        //54 withComponentConstraint ts t
        (fun us ts t -> None, us)

        //55 withComponentConstraints
        (fun us ts t  -> None, us)

        //56 globalIntType
        (fun _ -> [], Integer {Integer.cons = []; uperRange=Full; baseType = None; Location =emptyLocation; id=ReferenceToType []})

        //57 getSequenceOfTypeChild
        (fun us newTypeKind -> 
            match newTypeKind with
            | SequenceOf  sq   -> 
                let retType = us.anonymousTypes |> Seq.find(fun at -> at.id = sq.childTypeRef)
                let (ReferenceToType referenceToType) = sq.childTypeRef
                (referenceToType, retType) 
            | _                             -> raise(BugErrorException(sprintf "Expecting SequenceOf, found %A" newTypeKind)))

        //58 getChoiceTypeChild
        (fun us newTypeKind chName ->
            match newTypeKind with
            | Choice  ch   -> 
                match ch.children |> List.tryFind (fun c -> c.Name = chName.Value) with
                | Some ch       -> 
                    let (ReferenceToType referenceToType) = ch.refToType
                    let retType = us.anonymousTypes |> Seq.find(fun at -> at.id = (ReferenceToType referenceToType))
                    (referenceToType, retType) 
                | None          -> raise(SemanticError(chName.Location, (sprintf "CHOICE type has no alternative with name '%s'" chName.Value)))
            | _                 -> raise(BugErrorException(sprintf "Expecting Choice, found %A" newTypeKind)) )
        

        //59 getSequenceTypeChild
        (fun us newTypeKind chName ->
            match newTypeKind with
            | Sequence  sq   -> 
                match sq.children |> List.tryFind (fun c -> c.Name = chName.Value) with
                | Some ch   -> 
                    let (ReferenceToType referenceToType) = ch.refToType
                    let retType = us.anonymousTypes |> Seq.find(fun at -> at.id = (ReferenceToType referenceToType))
                    (referenceToType, retType)  
                | None          -> raise(SemanticError(chName.Location, (sprintf "SEQUENCE type has no alternative with name '%s'" chName.Value)))
            | _                 -> raise(BugErrorException(sprintf "Expecting SEQUENCE, found %A" newTypeKind)) )

        //60 getTypeKind
        (fun newT -> newT)



        app {State.anonymousTypes =[]; anonymousValues = []}