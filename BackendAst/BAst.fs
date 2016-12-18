module BAst

open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime
open Constraints
open FsUtils

(*
MYMOD DEFINITIONS ::=
BEGIN
  MySEQ ::= SEQUENCE (SIZE(1..10)) OF INTEGER (1..1000)
  MySEQ2 ::= MySEQ (WITH COMPONENT (0..255))

  A ::= INTEGER
  B ::= A (1..1000)
  C ::= B (1..100)
  

  MySequence ::= SEQUENCE {
    a INTEGER
    b INTEGER (1 .. 100)
    c MySEQ
    d C(1..10) 
  }


  -->
A ::= INTEGER
B ::= 
    INTEGER
    baseType A 
    cons (1..1000)

C ::= 
    INTEGER
    baseType B
    cons (1..100)

MySequence.a ::= INTEGER
MySequence.b ::= INTEGER (1 .. 100)
MySequence.d ::= 
    INTEGER
        baseType  C
        constraints : (1..10) 

MySequence ::= SEQUENCE {
    a       ref  MySequence.a
    b       ref  MySequence.b
    c       ref  MySEQ
    d       ref  MySequence.d
  }

END

* A Type is defined within the scope of Asn1Module  -> moduleName
* A Type is of specific typeKind. Possible kinds are
    | Integer
    | Real
    | IA5String
    | NumericString
    | OctetString 
    | NullType
    | BitString
    | Boolean 
    | Enumerated        of list<NamedItem>
    | SequenceOf        of Asn1Type
    | Sequence          of list<ChildInfo>
    | Choice            of list<ChildInfo>

    NO REFERENCE TYPE (i.e. a reference to a type is not a type)

* A Type may have a name (TypeAssigment Name)       ->  typeName : string option
    - For example the name for MySequence the typeName is MySequence
    - for component b (INTEGER (1 .. 100)) within MySequence is None

* A Type has a unique id consisting of ModuleName, TasName, path e.g
    - For example the name for MySequence the id is MyMODULE.MySequence
    - for component b (INTEGER (1 .. 100)) within MySequence is MyMODULE.MySequence.b
    
* A Type may extend another type  (baseType) e.g.
    - In MySequence the baseType is None
    - In MySEQ2 the base is MySEQ2 and typeKind SequenceOf INTEGER (1 .. 100)

* A composite type (SEQUENCE, CHOICE, SEUQNCE OF) refences other types 
  by their id e.g. in MySequence
   - a component references type with id:MYMOD.MySequence.a
   - b component references type with id:MYMOD.MySequence.b
   - c component references type with id:MYMOD.MySequence.c


==> In the new AST, for every type there is one and only TypeAssignment therefore there is no concept of TypeAssigment just type with name and id

Likewise, the is no value assigments. 
Only values that have
  - a unique id
  - an optional asn1 name
  - an associated type (through a reference to a type)
  - a value kind which can be one of
    |   IntegerValue        of BigInteger
    |   RealValue           of double
    |   StringValue         of string
    |   BooleanValue        of bool
    |   BitStringValue      of string
    |   OctetStringValue    of list<byte>
    |   EnumValue           of string
    |   SeqOfValue          of list<Asn1Value>
    |   SeqValue            of list<string*Asn1Value>
    |   ChValue             of string*Asn1Value
    |   NullValue

    Note no RefValue

ASN.1 CONSTRAINTS
 * A Constraint always refers to a specific type (i.e. it has a ReferenceToType)
 * A constraint may perVisibleConstraint or not.
 * WITH_COMPONENT AND WITH_COMPONENTS constraints do not exist in this model. Their constraints 
   are applied to components (perVisibleConstraint = false)
* There is no TYPEINCLUSION constraint (constraints copied to type)

*)


type Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of ReferenceToValue


type ChildInfo = {
    Name:string;
    refToType:ReferenceToType;
    Optionality:Asn1Optionality option
    Comments: string array
}

type EnumItems =
    | EnumItemsWithValues    of (string*BigInteger*List<string>) list
    | EnumItemsWithoutValues of (string*List<string>) list



type Asn1TypeKind =
    | Integer
    | Real
    | IA5String
    | OctetString 
    | NullType
    | BitString
    | Boolean 
    | Enumerated        of EnumItems
    | SequenceOf        of ReferenceToType
    | Sequence          of list<ChildInfo>
    | Choice            of list<ChildInfo>



type Asn1Constraint = 
    | SingleValueContraint              of ReferenceToValue             
    | RangeContraint                    of ReferenceToValue*ReferenceToValue*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX            of ReferenceToValue*bool         //min, InclusiveMin(=true)
    | RangeContraint_MIN_val            of ReferenceToValue*bool         //max, InclusiveMax(=true)
    | SizeContraint                     of Asn1Constraint               
    | AlphabetContraint                 of Asn1Constraint           
    | UnionConstraint                   of Asn1Constraint*Asn1Constraint*bool //left,righ, virtual constraint
    | IntersectionConstraint            of Asn1Constraint*Asn1Constraint
    | AllExceptConstraint               of Asn1Constraint
    | ExceptConstraint                  of Asn1Constraint*Asn1Constraint
    | RootConstraint                    of Asn1Constraint
    | RootConstraint2                   of Asn1Constraint*Asn1Constraint


type Asn1Type = {
    asn1Name : string option
    id : ReferenceToType
    baseTypeId : ReferenceToType option     // base type
    Kind:Asn1TypeKind;
    Constraints:list<Asn1Constraint>;
    FromWithCompConstraints:list<Asn1Constraint>;
    Location: SrcLoc   //Line no, Char pos
}

type Asn1ValueKind =
    |   IntegerValue        of BigInteger
    |   RealValue           of double
    |   StringValue         of string
    |   BooleanValue        of bool
    |   BitStringValue      of string
    |   OctetStringValue    of list<byte>
    |   EnumValue           of string
    |   SeqOfValue          of list<ReferenceToValue>
    |   SeqValue            of list<string*ReferenceToValue>
    |   ChValue             of string*ReferenceToValue
    |   NullValue


type Asn1Value = {
    asn1Name : string option
    id : ReferenceToValue
    //baseValue : ReferenceToValue option     
    refToType : ReferenceToType
    Kind:Asn1ValueKind
}

type Asn1Module = {
    Name : string
    Imports : list<Ast.ImportedModule>
    Exports : Ast.Exports
    Comments : string array
}

type Asn1File = {
    FileName:string;
    Tokens: IToken array
    Modules : list<Asn1Module>
}

type AstRoot = {
    Files: list<Asn1File>
    Encodings:list<Ast.Asn1Encoding>
    GenerateEqualFunctions:bool
    TypePrefix:string
    AstXmlAbsFileName:string
    IcdUperHtmlFileName:string
    IcdAcnHtmlFileName:string
    CheckWithOss:bool
    mappingFunctionsModule : string option
    valsMap : Map<ReferenceToValue, Asn1Value>
    typesMap : Map<ReferenceToType, Asn1Type>
    TypeAssignments : list<Asn1Type>
    ValueAssignments : list<Asn1Value>
}




//let createValue vk l = {Asn1Value.Kind = vk ;Location = l}

type State = {
    anonymousTypes : Asn1Type list
    anonymousValues : Asn1Value list
}
with 
    member this.add (other:State) =
        {State.anonymousTypes = this.anonymousTypes@other.anonymousTypes; anonymousValues = this.anonymousValues@other.anonymousValues}


let combineStates (states:State list)= 
    states |> List.fold (fun s c -> {s with anonymousTypes = s.anonymousTypes@c.anonymousTypes; anonymousValues = s.anonymousValues@c.anonymousValues}) {State.anonymousTypes =[]; anonymousValues = []}

let addValue (s:State) (v:Asn1Value)=
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

let createAsn1Module (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (newtases: Asn1Type list ) (vases:Asn1Value list ) = 
    {
        Asn1Module.Name = m.Name.Value
        Imports = m.Imports
        Exports = m.Exports
        Comments = m.Comments
    }, s


let createTypeAssignment (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (tas:Ast.TypeAssignment) (newType:Asn1Type) = 
    newType,s

let createValueAssignment (s:State) (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (vas:Ast.ValueAssignment) (t:Asn1Type) (v:Asn1Value) = 
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

let createType (s:State) (ts:GenericFold2.UserDefinedTypeScope) (oldType:Ast.Asn1Type) (newCons:((Asn1Constraint) option ) list, fromWithComps:((Asn1Constraint) option ) list) (baseTypeId : ReferenceToType option) (newKind:Asn1TypeKind)=
    let ret = 
        {
            Asn1Type.asn1Name = 
                match ts with
                | (GenericFold2.MD _)::(GenericFold2.TA tasName)::[]    -> Some tasName
                | _                                                     -> None
            id = ReferenceToType ts
            baseTypeId = baseTypeId
            Kind = newKind
            Constraints = newCons |> List.choose id
            FromWithCompConstraints = fromWithComps|> List.choose id
            Location = oldType.Location
        }
    //printfn "Creating type with id %s" (ret.id.ToString())
    ret, {s with anonymousTypes = s.anonymousTypes@[ret]}

let createValue (us:State) (asn1ValName:(StringLoc*StringLoc) option) (ts:GenericFold2.UserDefinedTypeScope) (vs:GenericFold2.UserDefinedVarScope) (kind:Asn1ValueKind) =
    let ret = 
        {
            Asn1Value.asn1Name = 
                match asn1ValName with
                | Some (md,vs)  -> Some vs.Value
                | None          -> None
            id = ReferenceToValue (ts, vs)
            //baseValue = baseValue
            refToType = ReferenceToType ts
            Kind = kind
        }
    ret, {us with anonymousValues=us.anonymousValues@[ret]}




let createValidationAst (lang:Ast.ProgrammingLanguage) (app:Ast.AstRoot)  =
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
(*
        //7. refTypeFunc s mdName tasName tabularized 
        (fun ustate s t newCons (baseType, exs) mdName tasName tabularized baseTypeIsNew -> 
            let exs = 
                match baseTypeIsNew with
                | true  -> {exs with anonymousTypes = baseType::exs.anonymousTypes}
                | false -> es
            let retT,s1 = createType s t newCons (Some baseType.id)  baseType.Kind
            retT, exs.add s1)
            *)

        //8 integerFunc s 
        (fun ustate  ->  Integer,ustate)

        //9 realFunc s 
        (fun ustate  -> Real, ustate)

        //10 ia5StringFunc s 
        (fun ustate  -> IA5String, ustate)

        //11 numericStringFunc s
        (fun ustate  -> 
        
            //let zero = {Asn1Value.Kind = StringValue("0"); asn1Name=None; id=zeroId; refToType=refToType}
            //let nine = {Asn1Value.Kind = StringValue("9"); asn1Name=None; id=zeroId; refToType=refToType}
            //let space = {Asn1Value.Kind = StringValue(" "); asn1Name=None; id=zeroId; refToType=refToType}
            //let newConstraint = AlphabetContraint(UnionConstraint(RangeContraint(zero.id,nine.id, true, true),SingleValueContraint(space.id), false))
        
            IA5String, ustate)

        //12 octetStringFunc
        (fun ustate -> OctetString, ustate)

        //13 nullTypeFunc
        (fun ustate -> NullType, ustate)

        //14 bitStringFunc
        (fun ustate -> BitString, ustate)

        //15 booleanFunc
        (fun ustate -> Boolean, ustate)

        //16 enumeratedFunc 
        (fun ustate (enmItems : Ast.NamedItem list)-> 
            let newEnmItems = 
                match enmItems |> Seq.exists (fun nm -> nm._value.IsSome) with
                | false ->
                    EnumItemsWithoutValues (enmItems |> List.map(fun x-> x.Name.Value, x.Comments|> Seq.toList) )
                | true  ->
                    let withVals = RemoveNumericStringsAndFixEnums.allocatedValuesToAllEnumItems enmItems app |> List.map(fun ni -> (ni.Name.Value, Ast.GetValueAsInt ni._value.Value app, ni.Comments|> Seq.toList))
                    EnumItemsWithValues withVals

            (Enumerated newEnmItems), ustate)

        //17 enmItemFunc
        (fun ustate ni newVal -> 0, ustate)

        //18 seqOfTypeFunc 
        (fun ustate newInnerType -> 
            (SequenceOf newInnerType.id), ustate)

        //19 seqTypeFunc 
        (fun ustate newChildren -> 
            (Sequence newChildren) , ustate)

        //20 chTypeFunc 
        (fun ustate newChildren -> 
            (Choice newChildren), ustate)

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
            Asn1Optionality.Default newValue.id)

        //26 choiceChildFunc
        createChoiceChildInfo

        //27 refValueFunc 
        (fun _ -> 0) 

        //28 enumValueFunc
        (fun us asn1ValName ts vs v nmItem -> createValue us asn1ValName ts vs (EnumValue nmItem.Value))

        //29 intValFunc
        (fun us asn1ValName ts vs v bi -> createValue us asn1ValName ts vs  (IntegerValue bi.Value))

        //30 realValFunc
        (fun us asn1ValName ts vs v bi -> createValue us asn1ValName ts vs  (RealValue bi.Value))

        //31 ia5StringValFunc 
        (fun us asn1ValName ts vs v str -> createValue us asn1ValName ts vs  (StringValue str.Value))

        //32 numStringValFunc 
        (fun us asn1ValName ts vs v str -> createValue us asn1ValName ts vs  (StringValue str.Value))

        //33 boolValFunc 
        (fun us asn1ValName ts vs v b -> createValue us asn1ValName ts vs  (BooleanValue b.Value))

        //34 octetStringValueFunc
        (fun us asn1ValName ts vs v bytes -> createValue us asn1ValName ts vs  (OctetStringValue (bytes |> List.map(fun b->b.Value))) )

        //35 octetStringValueFunc
        (fun us asn1ValName ts vs v b -> createValue us asn1ValName ts vs  (BitStringValue b.Value) )

        //36 nullValueFunc
        (fun us asn1ValName  ts vs v  -> createValue us asn1ValName ts vs NullValue )

        //37 seqOfValueFunc s t v actType  newVals
        (fun us asn1ValName ts vs v  newVals -> 
            let refToValsList = newVals |> List.map (fun v -> v.id)
            createValue us asn1ValName ts vs (SeqOfValue refToValsList))

        //38 seqValueFunc 
        (fun us asn1ValName ts vs v  newVals -> 
            let refToValsList = newVals |> List.map (fun (nm, (v)) -> (nm.Value, v.id))
            createValue us asn1ValName ts vs (SeqValue refToValsList) )

        //39 chValueFunc s t v actType name newValue
        (fun us asn1ValName ts vs v name newChValue -> 
            createValue us asn1ValName ts vs (ChValue (name.Value, newChValue.id)) )

        //40 singleValueContraintFunc s t checContent actType newValue
        (fun us ts t checContent newValue-> 
            Some (SingleValueContraint newValue.id), us)

        //41 rangeContraintFunc s t checContent actType newValue1 newValue2 b1 b2
        (fun us ts t checContent (newValue1) (newValue2) b1 b2 -> 
            Some (RangeContraint(newValue1.id, newValue2.id, b1, b2)), us)

        //42 rangeContraint_val_MAXFunc s t checContent actType newValue  b
        (fun us ts t checContent (newValue) b -> 
            Some (RangeContraint_val_MAX (newValue.id,b)), us)

        //43 rangeContraint_MIN_valFunc s t checContent actType newValue  b
        (fun us ts t checContent (newValue) b  -> 
            Some (RangeContraint_MIN_val(newValue.id,b)), us )

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
            | Some (nc1), Some (nc2)  -> Some (UnionConstraint (nc1, nc2, virtualCon)), us
            | Some (nc1), None        -> None, us
            | None, Some (nc2)        -> None, us
            | None, None              -> None, us)

        //47 intersectionConstraintFunc s t actType nc1 nc2
        (fun us ts t x1 x2 -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)  -> Some (IntersectionConstraint (nc1,nc2)), us
            | Some (nc1), None        -> Some (nc1), us
            | None, Some (nc2)        -> Some (nc2), us
            | None, None              -> None, us)

        //48 allExceptConstraintFunc s t actType nc
        (fun  us ts t x1 -> 
            match x1 with
            | Some (nc1)   -> Some (AllExceptConstraint nc1), us
            | None            -> raise(SemanticError(t.Location, (sprintf "EXCEPT constraint makes type to allow no values. Consider changing the EXCET part"))) )

        //49 exceptConstraintFunc s t actType nc1 nc2
        (fun us ts t x1 x2 -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)  -> Some (ExceptConstraint(nc1,nc2)), us
            | Some (nc1), None           -> raise(SemanticError(t.Location, (sprintf "EXCEPT constraint makes type to allow no values. Consider changing the EXCET part")))
            | None, Some (nc2)           -> Some (nc2), us
            | None, None                 -> raise(SemanticError(t.Location, (sprintf "EXCEPT constraint makes type to allow no values. Consider changing the EXCET part")))
        )

        //50 rootConstraintFunc s t actType nc
        (fun us ts t x1 -> x1 |> Option.map (fun (nc) -> RootConstraint nc), us )

        //51 rootConstraint2Func s t actType nc1 nc2
        (fun us ts t x1 x2 -> 
            match x1, x2 with
            | Some (nc1), Some (nc2)     -> Some (RootConstraint2 (nc1,nc2)), us
            | Some (nc1), None           -> None, us
            | None, Some (nc2)           -> None, us
            | None, None                 -> None, us)
        
        //52 sizeContraint 
        (fun us ts t x1 -> x1 |> Option.map (fun (nc) -> SizeContraint nc), us )
        
        //53 alphabetContraint
        (fun us ts t x1 -> x1 |> Option.map (fun (nc) -> AlphabetContraint nc), us )

        //54 withComponentConstraint ts t
        (fun us ts t -> None, us)

        //55 withComponentConstraints
        (fun us ts t  -> None, us)

        //56 globalIntType
        (fun _ -> [], Integer)

        //57 getSequenceOfTypeChild
        (fun us newTypeKind -> 
            match newTypeKind with
            | SequenceOf  (ReferenceToType referenceToType)   -> 
                let retType = us.anonymousTypes |> Seq.find(fun at -> at.id = (ReferenceToType referenceToType))
                (referenceToType, retType.Kind) 
            | _                             -> raise(BugErrorException(sprintf "Expecting SequenceOf, found %A" newTypeKind)))

        //58 getChoiceTypeChild
        (fun us newTypeKind chName ->
            match newTypeKind with
            | Choice  children   -> 
                match children |> List.tryFind (fun c -> c.Name = chName.Value) with
                | Some ch       -> 
                    let (ReferenceToType referenceToType) = ch.refToType
                    let retType = us.anonymousTypes |> Seq.find(fun at -> at.id = (ReferenceToType referenceToType))
                    (referenceToType, retType.Kind ) 
                | None          -> raise(SemanticError(chName.Location, (sprintf "CHOICE type has no alternative with name '%s'" chName.Value)))
            | _                 -> raise(BugErrorException(sprintf "Expecting Choice, found %A" newTypeKind)) )
        

        //59 getSequenceTypeChild
        (fun us newTypeKind chName ->
            match newTypeKind with
            | Sequence  children   -> 
                match children |> List.tryFind (fun c -> c.Name = chName.Value) with
                | Some ch   -> 
                    let (ReferenceToType referenceToType) = ch.refToType
                    let retType = us.anonymousTypes |> Seq.find(fun at -> at.id = (ReferenceToType referenceToType))
                    (referenceToType, retType.Kind )  
                | None          -> raise(SemanticError(chName.Location, (sprintf "SEQUENCE type has no alternative with name '%s'" chName.Value)))
            | _                 -> raise(BugErrorException(sprintf "Expecting SEQUENCE, found %A" newTypeKind)) )

        //60 getTypeKind
        (fun newT -> newT.Kind)



        app {State.anonymousTypes =[]; anonymousValues = []}