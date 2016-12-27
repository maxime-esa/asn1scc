module BAst

open System
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

type Integer = {
    cons                : (bool*IntegerTypeConstraint) list
    uperRange           : uperRange<BigInteger>
}
type Real = {
    cons                : (bool*RealTypeConstraint) list
    uperRange           : uperRange<double>
}

type StringType = {
    cons                : (bool*IA5StringConstraint) list
    sizeUperRange       : uperRange<UInt32>
    charUperRange       : uperRange<char>
}

type EnumItem = {
    name        : string
    Value       : BigInteger
    comments    : string list
}

type Enumerated = {
    items               : EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : (bool*EnumConstraint) list
}

type Boolean = {
    cons                : (bool*BoolConstraint) list
}

type SequenceOf = {
    childTypeRef        : ReferenceToType
    cons                : (bool*SequenceOfConstraint) list
    sizeUperRange       : uperRange<UInt32>
}
 

type OctetString = {
    cons                : (bool*OctetStringConstraint) list
    sizeUperRange       : uperRange<UInt32>
}

type BitString = {
    cons                : (bool*BitStringConstraint) list
    sizeUperRange       : uperRange<UInt32>
}

type Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of Asn1Value


and ChildInfo = {
    Name:string;
    refToType:ReferenceToType;
    Optionality:Asn1Optionality option
    Comments: string array
}


and Sequence = {
    children : ChildInfo list
    cons     : (bool*SequenceConstraint) list
}

and Choice = {
    children : ChildInfo list
    cons     : (bool*ChoiceConstraint) list
}



and Asn1TypeKind =
    | Integer           of Integer
    | Real              of Real
    | IA5String         of StringType
    | OctetString       of OctetString
    | NullType
    | BitString         of BitString
    | Boolean           of Boolean
    | Enumerated        of Enumerated
    | SequenceOf        of SequenceOf
    | Sequence          of Sequence
    | Choice            of Choice


(*
These constraints are interim.
*)
and Asn1Constraint = 
    | SingleValueContraint              of Asn1Value             
    | RangeContraint                    of Asn1Value*Asn1Value*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX            of Asn1Value*bool         //min, InclusiveMin(=true)
    | RangeContraint_MIN_val            of Asn1Value*bool         //max, InclusiveMax(=true)
    | SizeContraint                     of Asn1Constraint               
    | AlphabetContraint                 of Asn1Constraint           
    | UnionConstraint                   of Asn1Constraint*Asn1Constraint*bool //left,righ, virtual constraint
    | IntersectionConstraint            of Asn1Constraint*Asn1Constraint
    | AllExceptConstraint               of Asn1Constraint
    | ExceptConstraint                  of Asn1Constraint*Asn1Constraint
    | RootConstraint                    of Asn1Constraint
    | RootConstraint2                   of Asn1Constraint*Asn1Constraint


and Asn1Type = {
    asn1Name : string option
    id : ReferenceToType
    baseTypeId : ReferenceToType option     // base type
    Kind:Asn1TypeKind;
    //Constraints:list<Asn1Constraint>;
    //FromWithCompConstraints:list<Asn1Constraint>;
    Location: SrcLoc   //Line no, Char pos
}

and Asn1ValueKind =
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


and Asn1Value = {
    asn1Name : (StringLoc*StringLoc) option
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

