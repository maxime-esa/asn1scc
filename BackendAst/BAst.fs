module BAst

open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

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

type ReferenceToType = ReferenceToType of GenericFold2.ScopeNode list
type ReferenceToValue = ReferenceToValue of (GenericFold2.ScopeNode list)*(GenericFold2.VarScopNode list)

type Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of ReferenceToValue


type ChildInfo = {
    Name:string;
    refToType:ReferenceToType;
    Optionality:Asn1Optionality option
    AcnInsertedField:bool
    Comments: string array
}

type NamedItem = {
    Name:string
    refToValue:ReferenceToValue option
    Comments: string array
}


type Asn1TypeKind =
    | Integer
    | Real
    | IA5String
    | OctetString 
    | NullType
    | BitString
    | Boolean 
    | Enumerated        of list<NamedItem>
    | SequenceOf        of ReferenceToType
    | Sequence          of list<ChildInfo>
    | Choice            of list<ChildInfo>


type Asn1Constraint = 
    | SingleValueContraint              of ReferenceToValue             
    | RangeContraint                    of ReferenceToValue*ReferenceToValue*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX            of ReferenceToValue*bool         //min, InclusiveMin(=true)
    | RangeContraint_MIN_val            of ReferenceToValue*bool         //max, InclusiveMax(=true)
    | RangeContraint_MIN_MAX             
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
    AcnProperties : list<AcnTypes.AcnProperty>      //does not contain the properties with long fields 
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
    baseValue : ReferenceToValue option     
    refToType : ReferenceToType
    Kind:Asn1ValueKind
}

type Asn1Module = {
    Name : string
    TypeAssignments : list<Asn1Type>
    ValueAssignments : list<Asn1Value>
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
}













//let createValue vk l = {Asn1Value.Kind = vk ;Location = l}

type MyState = {
    anonymousTypes : Asn1Type list
    anonymousValues : Asn1Value list
}


let es = {MyState.anonymousTypes=[];anonymousValues=[]}

let combineStates (states:MyState list)= 
    states |> List.fold (fun s c -> {s with anonymousTypes = s.anonymousTypes@c.anonymousTypes; anonymousValues = s.anonymousValues@c.anonymousValues}) es

let addValue (s:MyState) (v:Asn1Value)=
    {s with anonymousValues=s.anonymousValues@[v]}

let smap = CloneTree.foldMap

let createAstRoot (sr:Ast.AstRoot) (dfiles: Asn1File list)  =
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
    }

let createAsn1File (r:Ast.AstRoot) (f:Ast.Asn1File) (newMods:Asn1Module list)  = 
    {
        Asn1File.FileName = f.FileName;
        Tokens = f.Tokens
        Modules  = newMods 
    }

let createAsn1Module (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (newtases: (Asn1Type*MyState) list ) (vases:(Asn1Value*MyState) list ) = 
    let newTypes = newtases |> List.map fst
    let newVases = vases |> List.map fst
    let anonymousTypes1 = newtases |> List.map snd |> List.collect (fun x -> x.anonymousTypes)
    let anonymousValues1 = newtases |> List.map snd |> List.collect (fun x -> x.anonymousValues)
    let anonymousTypes2 = vases |> List.map snd |> List.collect (fun x -> x.anonymousTypes)
    let anonymousValues2 = vases |> List.map snd |> List.collect (fun x -> x.anonymousValues)

    {
        Asn1Module.Name = m.Name.Value
        TypeAssignments = newTypes@anonymousTypes1@anonymousTypes2 
        ValueAssignments = newVases@anonymousValues1@anonymousValues2
        Imports = m.Imports
        Exports = m.Exports
        Comments = m.Comments
    }


let createTypeAssignment (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (tas:Ast.TypeAssignment) (newType:Asn1Type, es:MyState) = 
    newType, es

let createValueAssignment (r:Ast.AstRoot) (f:Ast.Asn1File) (m:Ast.Asn1Module) (vas:Ast.ValueAssignment) (t:Asn1Type, es:MyState) (v:Asn1Value, es2:MyState) = 
    v, {es with anonymousTypes = es.anonymousTypes@es.anonymousTypes; anonymousValues = es.anonymousValues@es2.anonymousValues}    

     

let createChildInfo s (ch:Ast.ChildInfo) (newType:Asn1Type, es:MyState) (newOptionality:(Asn1Optionality*MyState) option) = 
    let newState = {es with anonymousTypes = newType::es.anonymousTypes}
    let newOptionality, finalSate =
        match newOptionality with
        | None  -> None, newState
        | Some(no,s2) -> Some no, combineStates [s2;newState]
    {
        ChildInfo.Name = ch.Name.Value
        refToType = newType.id
        Optionality = newOptionality
        AcnInsertedField = ch.AcnInsertedField
        Comments = ch.Comments
    }, finalSate

let createChoiceChildInfo s (ch:Ast.ChildInfo) (newType:Asn1Type, es:MyState) = 
    let newState = {es with anonymousTypes = newType::es.anonymousTypes}
    {
        ChildInfo.Name = ch.Name.Value
        refToType = newType.id
        Optionality = None
        AcnInsertedField = ch.AcnInsertedField
        Comments = ch.Comments
    }, newState
    (*
let createReferenceTypeFunc (s:GenericFold2.Scope) (t:Ast.Asn1Type) (newCons:Asn1Constraint list) (baseTypes: Asn1Type list) (mdName:string) (tasName:string) tabularized : Asn1Type list =
    match newCons with
    | []    -> []
    |
        let thisType = 
            {
                Asn1Type.asn1Name = 
                    match s.parents with
                    | []    -> Some s.a.Name
                    | _     -> None

                id = ReferenceToType s.ID
                baseTypeId = baseTypeId
                Kind = newKind
                Constraints = newCons
                AcnProperties = t.AcnProperties
                Location = t.Location

            }
        thisType
        *)

let createType (s:GenericFold2.Scope) (oldType:Ast.Asn1Type) (newCons:(Asn1Constraint*MyState) list) (baseTypeId : ReferenceToType option) (newKind:Asn1TypeKind)=
    {
        Asn1Type.asn1Name = s.asn1TypeName

        id = ReferenceToType s.typeID
        baseTypeId = baseTypeId
        Kind = newKind
        Constraints = newCons |> List.map fst
        AcnProperties = oldType.AcnProperties
    }

let createValue (s:GenericFold2.Scope) (baseValue : ReferenceToValue option) (refToType : ReferenceToType) (kind:Asn1ValueKind) =
    {
        Asn1Value.asn1Name = s.asn1VarName
        id = ReferenceToValue (s.typeID, s.varID)
        baseValue = baseValue
        refToType = refToType 
        Kind = kind
    }

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

        //6. typeFunc s t newCons newKind
        
        //7. refTypeFunc s mdName tasName tabularized 
        (fun s t newCons (baseType, exs) mdName tasName tabularized  -> 
            createType s t newCons (Some baseType.id)  baseType.Kind , exs)

        //8 integerFunc s 
        (fun s t newCons -> createType s t newCons None Integer, es)

        //9 realFunc s 
        (fun s t newCons -> createType s t newCons None  Real, es)

        //10 ia5StringFunc s 
        (fun s t newCons -> createType s t newCons None  IA5String, es)

        //11 numericStringFunc s
        (fun s t newCons -> 
        
            //let zero = {Asn1Value.Kind = StringValue("0".AsLoc); Location = emptyLocation}
            //let nine = {Asn1Value.Kind = StringValue("9".AsLoc); Location = emptyLocation}
            //let space = {Asn1Value.Kind = StringValue(" ".AsLoc); Location = emptyLocation}
            //let newConstraint = AlphabetContraint(UnionConstraint(RangeContraint(zero,nine, true, true),SingleValueContraint(space), false))
        
            createType s t newCons None  IA5String, es)

        //12 octetStringFunc
        (fun s t newCons -> createType s t newCons None  OctetString, es)

        //13 nullTypeFunc
        (fun s t newCons -> createType s t newCons None  NullType, es)

        //14 bitStringFunc
        (fun s t newCons -> createType s t newCons None  BitString, es)

        //15 booleanFunc
        (fun s t newCons -> createType s t newCons None  Boolean, es)

        //16 enumeratedFunc 
        (fun s t newCons  (itms:List<NamedItem*MyState>)-> 
            let newEnmItems = itms |> List.map fst
            let es = itms |> List.map snd |> combineStates
            let newType = createType s t newCons None   (Enumerated newEnmItems) 
            newType,es )

        //17 enmItemFunc
        (fun ni newVal -> 
            let newNamedItem, newValue = 
                match newVal with
                | None  -> {NamedItem.Name = ni.Name.Value; refToValue = None; Comments=ni.Comments}, es
                | Some (vl,ex) ->  
                    {NamedItem.Name = ni.Name.Value; refToValue = Some vl.id; Comments=ni.Comments}, ex
            newNamedItem, newValue )

        //18 seqOfTypeFunc 
        (fun s  t newCons (newInnerType, state) -> 
            let newState = {state with anonymousTypes = newInnerType::state.anonymousTypes}
            createType s t newCons None   (SequenceOf newInnerType.id), newState)

        //19 seqTypeFunc 
        (fun s  t newCons newChildren -> 
            let nc = newChildren  |> List.map fst
            let newState = newChildren  |> List.map snd |> combineStates
            createType s t newCons None   (Sequence nc), newState)

        //20 chTypeFunc 
        (fun s  t newCons newChildren -> 
            let nc = newChildren  |> List.map fst
            let newState = newChildren  |> List.map snd |> combineStates
            createType s t newCons None   (Choice nc), newState)

        //21 sequenceChildFunc 
        createChildInfo

        //22 alwaysAbsentFunc
        (fun s -> Asn1Optionality.AlwaysAbsent, es)

        //23 alwaysPresentFunc
        (fun s -> Asn1Optionality.AlwaysPresent,es)

        //24 optionalFunc
        (fun s -> Asn1Optionality.Optional, es)

        //25 defaultFunc
        (fun s (newValue,st) -> 
        Asn1Optionality.Default newValue.id, {st with anonymousValues = newValue::st.anonymousValues})

        //26 choiceChildFunc
        createChoiceChildInfo

        //27 refValueFunc 
        (fun ts vs v (md, vas) (newActVal, st) -> 
            createValue vs (Some newActVal.id) (ReferenceToType ts.typeID) newActVal.Kind, st) 

        //28 enumValueFunc
        (fun ts vs v nmItem -> 
            createValue vs None (ReferenceToType ts.typeID) (EnumValue nmItem.Value), es)

        //29 intValFunc
        (fun ts vs v bi -> createValue vs None (ReferenceToType ts.typeID) (IntegerValue bi.Value), es)

        //30 realValFunc
        (fun ts vs v bi -> createValue vs None (ReferenceToType ts.typeID) (RealValue bi.Value), es)

        //31 ia5StringValFunc 
        (fun ts vs v str -> createValue vs None (ReferenceToType ts.typeID) (StringValue str.Value), es)

        //32 numStringValFunc 
        (fun ts vs v str -> createValue vs None (ReferenceToType ts.typeID) (StringValue str.Value), es)

        //33 boolValFunc 
        (fun ts vs v b -> createValue vs None (ReferenceToType ts.typeID) (BooleanValue b.Value), es)

        //34 octetStringValueFunc
        (fun ts vs v bytes -> createValue vs None (ReferenceToType ts.typeID) (OctetStringValue (bytes |> List.map(fun b->b.Value))), es)

        //35 octetStringValueFunc
        (fun ts vs v b -> createValue vs None (ReferenceToType ts.typeID) (BitStringValue b.Value), es)

        //36 nullValueFunc
        (fun ts vs v  -> createValue vs None (ReferenceToType ts.typeID) NullValue, es)

        //37 seqOfValueFunc s t v actType  newVals
        (fun ts vs v  newVals -> 
            let nvs = newVals |> List.map fst
            let ss = newVals |> List.map snd
            let refToValsList = nvs |> List.map (fun v -> v.id)
            let exts = {MyState.anonymousValues = nvs; anonymousTypes=[]}::ss |> combineStates
            createValue vs None (ReferenceToType ts.typeID) (SeqOfValue refToValsList), exts)

        //38 seqValueFunc 
        (fun ts vs v  newVals -> 
            let nvs = newVals |> List.map snd |> List.map fst
            let ss = newVals |> List.map snd |> List.map snd
            let refToValsList = newVals |> List.map (fun (nm, (v,_)) -> (nm.Value, v.id))
            let exts = {MyState.anonymousValues = nvs; anonymousTypes=[]}::ss |> combineStates
            createValue vs None (ReferenceToType ts.typeID) (SeqValue refToValsList), exts)

        //39 chValueFunc s t v actType name newValue
        (fun ts vs v name (newChValue,st) -> 
            let nes = addValue st newChValue
            createValue vs None (ReferenceToType ts.typeID) (ChValue (name.Value, newChValue.id)), nes)

        //40 singleValueContraintFunc s t checContent actType newValue
        (fun ts t checContent (newValue,st)-> 
            let nes = addValue st newValue
            SingleValueContraint newValue.id, nes)

        //41 rangeContraintFunc s t checContent actType newValue1 newValue2 b1 b2
        (fun ts t checContent (newValue1,st1) (newValue2,st2) b1 b2 -> 
            let nes1 = addValue st1 newValue1
            let nes2 = addValue st2 newValue2
            let fs = combineStates [nes1; nes2]
            RangeContraint(newValue1.id, newValue2.id, b1, b2), fs)

        //42 rangeContraint_val_MAXFunc s t checContent actType newValue  b
        (fun ts t checContent (newValue,st) b -> 
            let nes = addValue st newValue
            RangeContraint_val_MAX (newValue.id,b), nes)

        //43 rangeContraint_MIN_valFunc s t checContent actType newValue  b
        (fun ts t checContent (newValue,st) b  -> 
            let nes = addValue st newValue
            RangeContraint_MIN_val(newValue.id,b),nes )

        //44 rangeContraint_MIN_MAXFunc  s t checContent actType
        (fun ts t checContent -> RangeContraint_MIN_MAX,es )

        //45 typeInclConstraintFunc s t actType (md,tas)
        (fun ts t (md,tas) -> raise (System.Exception("typeInclConstraintFunc")))

        //46 unionConstraintFunc s t actType nc1 nc2
        (fun ts t (nc1,s1) (nc2,s2) virtualCon -> 
            UnionConstraint (nc1, nc2, virtualCon), combineStates [s1;s2])

        //47 intersectionConstraintFunc s t actType nc1 nc2
        (fun ts t (nc1,s1) (nc2,s2) -> IntersectionConstraint (nc1,nc2), combineStates [s1;s2])

        //48 allExceptConstraintFunc s t actType nc
        (fun  ts t (nc,s1) -> AllExceptConstraint nc, s1)

        //49 exceptConstraintFunc s t actType nc1 nc2
        (fun ts t (nc1,s1) (nc2,s2) -> ExceptConstraint(nc1,nc2), combineStates [s1;s2] )

        //50 rootConstraintFunc s t actType nc
        (fun ts t (nc,s1) -> RootConstraint nc, s1 )

        //51 rootConstraint2Func s t actType nc1 nc2
        (fun ts t (nc1,s1) (nc2,s2) -> RootConstraint2 (nc1,nc2), combineStates [s1;s2] )

        app