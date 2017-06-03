module DAst

open System
open System.Numerics

open FsUtils
open CommonTypes
open Constraints
open uPER2
type ExpOrStatement =
    | Expression 
    | Statement  

type LocalVariable =
    | SequenceOfIndex       of int*int option        //i index, initialValue
    | IntegerLocalVariable  of string*int option     //variable name, initialValue
    | Asn1SIntLocalVariable of string*int option     //variable name, initialValue
    | Asn1UIntLocalVariable of string*int option     //variable name, initialValue
    | FlagLocalVariable     of string*int option     //variable name, initialValue
    | AcnInsertedChild      of string*string         //variable name, type 
with
    member this.VarName =
        match this with
        | SequenceOfIndex (i,_)   -> sprintf "i%d" i
        | IntegerLocalVariable(name,_)    -> name
        | Asn1SIntLocalVariable(name,_)   -> name
        | Asn1UIntLocalVariable(name,_)   -> name
        | FlagLocalVariable(name,_)       -> name
        | AcnInsertedChild(name,_)        -> name
    member this.GetDeclaration (l:Constraints.ProgrammingLanguage) =
        match l, this with
        | C,    SequenceOfIndex (i,None)                  -> sprintf "int i%d;" i
        | C,    SequenceOfIndex (i,Some iv)               -> sprintf "int i%d=%d;" i iv
        | Ada,  SequenceOfIndex (i,None)                  -> sprintf "i%d:Integer;" i
        | Ada,  SequenceOfIndex (i,Some iv)               -> sprintf "i%d:Integer:=%d;" i iv
        | C,    IntegerLocalVariable (name,None)          -> sprintf "int %s;" name
        | C,    IntegerLocalVariable (name,Some iv)       -> sprintf "int %s=%d;" name iv
        | Ada,  IntegerLocalVariable (name,None)          -> sprintf "%s:Integer;" name
        | Ada,  IntegerLocalVariable (name,Some iv)       -> sprintf "%s:Integer:=%d;" name iv
        | C,    Asn1SIntLocalVariable (name,None)         -> sprintf "asn1SccSint %s;" name
        | C,    Asn1SIntLocalVariable (name,Some iv)      -> sprintf "asn1SccSint %s=%d;" name iv
        | Ada,  Asn1SIntLocalVariable (name,None)         -> sprintf "%s:adaasn1rtl.Asn1Int;" name
        | Ada,  Asn1SIntLocalVariable (name,Some iv)      -> sprintf "%s:adaasn1rtl.Asn1Int:=%d;" name iv
        | C,    Asn1UIntLocalVariable (name,None)         -> sprintf "asn1SccUint %s;" name
        | C,    Asn1UIntLocalVariable (name,Some iv)      -> sprintf "asn1SccUint %s=%d;" name iv
        | Ada,  Asn1UIntLocalVariable (name,None)         -> sprintf "%s:adaasn1rtl.Asn1UInt;" name
        | Ada,  Asn1UIntLocalVariable (name,Some iv)      -> sprintf "%s:adaasn1rtl.Asn1UInt:=%d;" name iv
        | C,    FlagLocalVariable (name,None)             -> sprintf "flag %s;" name
        | C,    FlagLocalVariable (name,Some iv)          -> sprintf "flag %s=%d;" name iv
        | Ada,  FlagLocalVariable (name,None)             -> sprintf "%s:adaasn1rtl.BIT;" name
        | Ada,  FlagLocalVariable (name,Some iv)          -> sprintf "%s:adaasn1rtl.BIT:=%d;" name iv
        | C,    AcnInsertedChild(name, vartype)           -> sprintf "%s %s;" vartype name
        | Ada,    AcnInsertedChild(name, vartype)         -> sprintf "%s:%s;" name vartype



         //Emit_local_variable_SQF_Index(nI, bHasInitalValue)::="I<nI>:Integer<if(bHasInitalValue)>:=1<endif>;"

type TypeOrSubsType =
    | TYPE
    | SUBTYPE


type TypeDefinitionCommon = {
    // the name of the type C or Ada type. Defives from ASN.1 Type Assignment name.
    // Eg. for MyInt4 ::= INTEGER(0..15|20|25)
    // name will be MyInt4 
    name                : string            

    // used only in Ada backend. 
    typeOrSubsType      : TypeOrSubsType    

    //In above example, in C the typeDefinitionBody is : asn1SccSint
    //              in Ada                          is : adaasn1rtl.Asn1Int range 0..25
    // for a complext type e.g. sequence 
    // in C   is the struct { ... fields ...}
    // in Ada is the IS RECORD ... fields ... END RECORD
    // Ada does not allow nested type defintions. Therefore when called with NESTED_DEFINITION_SCOPE (i.e. from a SEQUENCE) the name of the type is returned
    //typeDefinitionBody  : string            

    // Used only for Strings and is the size of the string (plus one for the null terminated character)
    // It is usefull only in C due to the fact that the size of the array is not part of the type definition body but follows the the type name
    // i.e. for the ASN.1 type   STRCAPS   ::= IA5String (SIZE(1..100)) (FROM ("A".."Z"))	
    // the C definition is : typedef char STRCAPS[101];
    // If the definition was typedef char[101] STRCAPS; (which is the case for all other languages Ada, C#, Java etc) then we wouldn't need it
    arraySize           : int option      
    
    // the complete definition of the type
    // e.g. C : typedef asn1SccSint MyInt4;
    // and Ada: SUBTYPE MyInt4 IS adaasn1rtl.Asn1Int range 0..25;    
    completeDefinition  : string  


    // Ada does not allow nested type definitions.
    // Therefore The following type MySeq { a INTEGER, innerSeq SEQUENCE {b REAL}}
    // must be declared as if it was defined MySeq_innerSeq SEQUENCE {b REAL} MySeq { a INTEGER, innerSeq MySeq_innerSeq}
    // in this case it will be : MySeq_innerSeq 
    typeDefinitionBodyWithinSeq : string

    //the complete deffinition of inner complex types that must be declared
    //before this type
    completeDefinitionWithinSeq : string option
}

type ErroCode = {
    errCodeValue    : int
    errCodeName     : string
}

type BaseTypesEquivalence<'T> = {
    typeDefinition  : 'T option
    uper            : 'T option
    acn             : 'T option
}
    
        
(*
Generates initialization statement(s) that inititalize the type with the given Asn1GeneticValue.
*)            
type InitFunction = {
    initFuncName            : string option               // the name of the function
    initFunc                : string option               // the body of the function
    initFuncDef             : string option               // function definition in header file
    initFuncBody            : FuncParamType  -> Asn1GenericValue -> string                      // returns the statement(s) that initialize this type
}


type IsEqualBody =
    | EqualBodyExpression       of (string -> string -> (string*(LocalVariable list)) option)
    | EqualBodyStatementList    of (string -> string -> (string*(LocalVariable list)) option)

type IsEqualBody2 =
    | EqualBodyExpression2       of (string -> string -> string -> (string*(LocalVariable list)) option)
    | EqualBodyStatementList2    of (string -> string -> string -> (string*(LocalVariable list)) option)

type EqualFunction = {
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               // the body of the equal function
    isEqualFuncDef      : string option
    isEqualBody         : IsEqualBody                 // a function that  returns an expression or a statement list
    isEqualBody2        : IsEqualBody2
}

type AlphaFunc   = {
    funcName            : string
    funcBody            : string
}

type IsValidFunction = {
    errCodes            : ErroCode list
    funcName            : string option               // the name of the function. Valid only for TASes)
    func                : string option               // the body of the function
    funcDef             : string option               // function definition in header file
    funcExp             : (string -> string) option   // return a single boolean expression
    funcBody            : string -> string            //returns a list of validations statements
    funcBody2           : string -> string -> string  //like funBody but with two arguement p and accessOper ( i.e. '->' or '.')
    alphaFuncs          : AlphaFunc list  
    localVariables      : LocalVariable list
}

type UPERFuncBodyResult = {
    funcBody            : string
    errCodes            : ErroCode list
    localVariables      : LocalVariable list
}
type UPerFunction = {
    funcName            : string option               // the name of the function
    func                : string option               // the body of the function
    funcDef             : string option               // function definition in header file
    funcBody            : FuncParamType -> (UPERFuncBodyResult option)            // returns a list of validations statements
}

type AcnFuncBodyResult = {
    funcBody            : string
    errCodes            : ErroCode list
    localVariables      : LocalVariable list
}

type AcnFunction = {
    funcName            : string option               // the name of the function. Valid only for TASes)
    func                : string option               // the body of the function
    funcDef             : string option               // function definition
    funcBody            : FuncParamType -> (AcnFuncBodyResult option)            // returns a list of validations statements
}

type Integer = {
    //bast inherrited properties
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : IntegerTypeConstraint list
    withcons            : IntegerTypeConstraint list
    uperRange           : uperRange<BigInteger>
    baseType            : Integer option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.IntEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<Integer>

    typeDefinition      : TypeDefinitionCommon
    initialValue        : IntegerValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction
    acnEncFunction      : AcnFunction
    acnDecFunction      : AcnFunction
    

}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons
    member this.IsUnsigned = isUnsigned this.uperRange

type Enumerated = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    items               : BAst.EnumItem list
    userDefinedValues   : bool      //if true, the user has associated at least one item with a value
    cons                : EnumConstraint list
    withcons            : EnumConstraint list
    baseType            : Enumerated option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    enumEncodingClass   : CAst.EnumAcnEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<Enumerated>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : EnumValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

type Real = {
    //bast inherrited properties
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : RealTypeConstraint list
    withcons            : RealTypeConstraint list
    uperRange           : uperRange<double>
    baseType            : Real option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.RealEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<Real>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : RealValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons


type Boolean = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : BoolConstraint list
    withcons            : BoolConstraint list
    baseType            : Boolean option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.BolleanAcnEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<Boolean>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : BooleanValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction
    acnEncFunction      : AcnFunction
    acnDecFunction      : AcnFunction
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons


type NullType = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    baseType            : NullType option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.NullAcnEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<NullType>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : NullValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}


type StringType = {
    //bast inherrited properties
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : IA5StringConstraint list
    withcons            : IA5StringConstraint list
    minSize             : int
    maxSize             : int
    charSet             : char array
    baseType            : StringType option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.StringAcnEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<StringType>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : StringValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons


type OctetString = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : OctetStringConstraint list
    withcons            : OctetStringConstraint list
    minSize             : int
    maxSize             : int
    baseType            : OctetString option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.SizeableAcnEncodingClass

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<OctetString>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : OctetStringValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons



type BitString = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    cons                : BitStringConstraint list
    withcons            : BitStringConstraint list
    minSize             : int
    maxSize             : int
    baseType            : BitString option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.SizeableAcnEncodingClass
    //acnArguments        : IntArgument list

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<BitString>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : BitStringValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons


type SequenceOf = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    childType           : Asn1Type
    cons                : SequenceOfConstraint list
    withcons            : SequenceOfConstraint list
    minSize             : int
    maxSize             : int
    baseType            : SequenceOf option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option
    acnEncodingClass    : CAst.SizeableAcnEncodingClass
    //acnArguments        : GenericArgument list

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<SequenceOf>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : SeqOfValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons


and SeqChoiceChildInfoIsValid = {
    isValidStatement  : string -> string -> string
    localVars         : LocalVariable list
    alphaFuncs        : AlphaFunc list
    errCode           : ErroCode list
}


and SeqChildInfo = {
    name                :string
    chType              :Asn1Type
    optionality         :CAst.Asn1Optionality option
    acnInsertetField    :bool
    comments            :string list

    //DAst properties
    c_name              : string
    isEqualBodyStats    : string -> string  -> string -> (string*(LocalVariable list)) option  // 
    isValidBodyStats    : int -> (SeqChoiceChildInfoIsValid option * int)
}


and Sequence = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    children            : SeqChildInfo list
    cons                : SequenceConstraint list
    withcons            : SequenceConstraint list
    baseType            : Sequence option
    Location            : SrcLoc   

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    alignment           : CAst.AcnAligment option

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<Sequence>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : SeqValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    acnEncFunction      : AcnFunction
    acnDecFunction      : AcnFunction
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons




and ChChildInfo = {
    name                :string
    chType              :Asn1Type
    comments            :string list
    presenseIsHandleByExtField :bool
    presentWhenName     :string     // the name of the corresponding enum that indicates that specific child is present
    
    //DAst properties
    c_name              : string
    isEqualBodyStats    : string -> string -> string -> string*(LocalVariable list) // 
    isValidBodyStats    : int -> (SeqChoiceChildInfoIsValid option * int)
}

and Choice = {
    id                  : ReferenceToType
    tasInfo             : BAst.TypeAssignmentInfo option
    uperMaxSizeInBits   : int
    uperMinSizeInBits   : int
    children            : ChChildInfo list
    cons                : ChoiceConstraint list
    withcons            : ChoiceConstraint list
    baseType            : Choice option
    Location            : SrcLoc   
    choiceIDForNone     : string

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    acnEncodingClass    : CAst.ChoiceAcnEncClass
    alignment           : CAst.AcnAligment option

    //DAst properties
    baseTypeEquivalence: BaseTypesEquivalence<Choice>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : ChValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons



and Asn1Type =
    | Integer           of Integer
    | Real              of Real
    | IA5String         of StringType
    | OctetString       of OctetString
    | NullType          of NullType
    | BitString         of BitString
    | Boolean           of Boolean
    | Enumerated        of Enumerated
    | SequenceOf        of SequenceOf
    | Sequence          of Sequence
    | Choice            of Choice
with
    member this.id =
        match this with
        | Integer      t -> t.id
        | Real         t -> t.id
        | IA5String    t -> t.id
        | OctetString  t -> t.id
        | NullType     t -> t.id
        | BitString    t -> t.id
        | Boolean      t -> t.id
        | Enumerated   t -> t.id
        | SequenceOf   t -> t.id
        | Sequence     t -> t.id
        | Choice       t -> t.id
    member this.baseType =
        match this with
        | Integer      t -> t.baseType |> Option.map Integer     
        | Real         t -> t.baseType |> Option.map Real        
        | IA5String    t -> t.baseType |> Option.map IA5String   
        | OctetString  t -> t.baseType |> Option.map OctetString 
        | NullType     t -> t.baseType |> Option.map NullType    
        | BitString    t -> t.baseType |> Option.map BitString   
        | Boolean      t -> t.baseType |> Option.map Boolean     
        | Enumerated   t -> t.baseType |> Option.map Enumerated  
        | SequenceOf   t -> t.baseType |> Option.map SequenceOf  
        | Sequence     t -> t.baseType |> Option.map Sequence    
        | Choice       t -> t.baseType |> Option.map Choice      
    member this.uperMaxSizeInBits =
        match this with
        | Integer      t -> t.uperMaxSizeInBits
        | Real         t -> t.uperMaxSizeInBits
        | IA5String    t -> t.uperMaxSizeInBits
        | OctetString  t -> t.uperMaxSizeInBits
        | NullType     t -> t.uperMaxSizeInBits
        | BitString    t -> t.uperMaxSizeInBits
        | Boolean      t -> t.uperMaxSizeInBits
        | Enumerated   t -> t.uperMaxSizeInBits
        | SequenceOf   t -> t.uperMaxSizeInBits
        | Sequence     t -> t.uperMaxSizeInBits
        | Choice       t -> t.uperMaxSizeInBits
    member this.uperMinSizeInBits =
        match this with
        | Integer      t -> t.uperMinSizeInBits
        | Real         t -> t.uperMinSizeInBits
        | IA5String    t -> t.uperMinSizeInBits
        | OctetString  t -> t.uperMinSizeInBits
        | NullType     t -> t.uperMinSizeInBits
        | BitString    t -> t.uperMinSizeInBits
        | Boolean      t -> t.uperMinSizeInBits
        | Enumerated   t -> t.uperMinSizeInBits
        | SequenceOf   t -> t.uperMinSizeInBits
        | Sequence     t -> t.uperMinSizeInBits
        | Choice       t -> t.uperMinSizeInBits
    member this.acnMinSizeInBits =
        match this with
        | Integer      t -> t.acnMinSizeInBits
        | Real         t -> t.acnMinSizeInBits
        | IA5String    t -> t.acnMinSizeInBits
        | OctetString  t -> t.acnMinSizeInBits
        | NullType     t -> t.acnMinSizeInBits
        | BitString    t -> t.acnMinSizeInBits
        | Boolean      t -> t.acnMinSizeInBits
        | Enumerated   t -> t.acnMinSizeInBits
        | SequenceOf   t -> t.acnMinSizeInBits
        | Sequence     t -> t.acnMinSizeInBits
        | Choice       t -> t.acnMinSizeInBits

    member this.acnMaxSizeInBits =
        match this with
        | Integer      t -> t.acnMaxSizeInBits
        | Real         t -> t.acnMaxSizeInBits
        | IA5String    t -> t.acnMaxSizeInBits
        | OctetString  t -> t.acnMaxSizeInBits
        | NullType     t -> t.acnMaxSizeInBits
        | BitString    t -> t.acnMaxSizeInBits
        | Boolean      t -> t.acnMaxSizeInBits
        | Enumerated   t -> t.acnMaxSizeInBits
        | SequenceOf   t -> t.acnMaxSizeInBits
        | Sequence     t -> t.acnMaxSizeInBits
        | Choice       t -> t.acnMaxSizeInBits
    member this.initialValue =
        match this with
        | Integer      t -> IntegerValue t.initialValue
        | Real         t -> RealValue t.initialValue
        | IA5String    t -> StringValue t.initialValue
        | OctetString  t -> OctetStringValue t.initialValue
        | NullType     t -> NullValue t.initialValue
        | BitString    t -> BitStringValue t.initialValue
        | Boolean      t -> BooleanValue t.initialValue
        | Enumerated   t -> EnumValue t.initialValue
        | SequenceOf   t -> SeqOfValue t.initialValue
        | Sequence     t -> SeqValue t.initialValue
        | Choice       t -> ChValue t.initialValue

    member this.initFunction =
        match this with
        | Integer      t -> t.initFunction
        | Real         t -> t.initFunction
        | IA5String    t -> t.initFunction
        | OctetString  t -> t.initFunction
        | NullType     t -> t.initFunction
        | BitString    t -> t.initFunction
        | Boolean      t -> t.initFunction
        | Enumerated   t -> t.initFunction
        | SequenceOf   t -> t.initFunction
        | Sequence     t -> t.initFunction
        | Choice       t -> t.initFunction

    member this.equalFunction =
        match this with
        | Integer      t -> t.equalFunction
        | Real         t -> t.equalFunction
        | IA5String    t -> t.equalFunction
        | OctetString  t -> t.equalFunction
        | NullType     t -> t.equalFunction
        | BitString    t -> t.equalFunction
        | Boolean      t -> t.equalFunction
        | Enumerated   t -> t.equalFunction
        | SequenceOf   t -> t.equalFunction
        | Sequence     t -> t.equalFunction
        | Choice       t -> t.equalFunction

    member this.isValidFunction =
        match this with
        | Integer      t -> t.isValidFunction
        | Real         t -> t.isValidFunction
        | IA5String    t -> t.isValidFunction
        | OctetString  t -> t.isValidFunction
        | NullType     t -> None
        | BitString    t -> t.isValidFunction
        | Boolean      t -> t.isValidFunction
        | Enumerated   t -> t.isValidFunction
        | SequenceOf   t -> t.isValidFunction
        | Sequence     t -> t.isValidFunction
        | Choice       t -> t.isValidFunction
    member this.getUperFunction (l:CommonTypes.Codec) =
        match l with
        | CommonTypes.Encode   -> this.uperEncFunction
        | CommonTypes.Decode   -> this.uperDecFunction
    member this.uperEncFunction =
         match this with
         | Integer      t -> Some(t.uperEncFunction)
         | Real         t -> Some(t.uperEncFunction)
         | IA5String    t -> Some(t.uperEncFunction)
         | OctetString  t -> Some(t.uperEncFunction)
         | NullType     t -> Some(t.uperEncFunction)
         | BitString    t -> Some(t.uperEncFunction)
         | Boolean      t -> Some(t.uperEncFunction)
         | Enumerated   t -> Some(t.uperEncFunction)
         | SequenceOf   t -> Some(t.uperEncFunction)
         | Sequence     t -> Some(t.uperEncFunction)
         | Choice       t -> Some(t.uperEncFunction)
    member this.uperDecFunction =
         match this with
         | Integer      t -> Some(t.uperDecFunction)
         | Real         t -> Some(t.uperDecFunction)
         | IA5String    t -> Some(t.uperDecFunction)
         | OctetString  t -> Some(t.uperDecFunction)
         | NullType     t -> Some(t.uperDecFunction)
         | BitString    t -> Some(t.uperDecFunction)
         | Boolean      t -> Some(t.uperDecFunction)
         | Enumerated   t -> Some(t.uperDecFunction)
         | SequenceOf   t -> Some(t.uperDecFunction)
         | Sequence     t -> Some(t.uperDecFunction)
         | Choice       t -> Some(t.uperDecFunction)
    member this.acnEncFunction : AcnFunction option =
        match this with
        | Integer      t -> Some (t.acnEncFunction)
        | Real         t -> None
        | IA5String    t -> None
        | OctetString  t -> None
        | NullType     t -> None
        | BitString    t -> None
        | Boolean      t -> Some (t.acnEncFunction)
        | Enumerated   t -> None
        | SequenceOf   t -> None
        | Sequence     t -> Some (t.acnEncFunction)
        | Choice       t -> None
    member this.acnDecFunction : AcnFunction option =
        match this with
        | Integer      t -> Some (t.acnDecFunction)
        | Real         t -> None
        | IA5String    t -> None
        | OctetString  t -> None
        | NullType     t -> None
        | BitString    t -> None
        | Boolean      t -> Some (t.acnDecFunction)
        | Enumerated   t -> None
        | SequenceOf   t -> None
        | Sequence     t -> Some (t.acnDecFunction)
        | Choice       t -> None
    member this.getAcnFunction (l:CommonTypes.Codec) =
        match l with
        | CommonTypes.Encode   -> this.acnEncFunction
        | CommonTypes.Decode   -> this.acnDecFunction

    member this.typeDefinition =
        match this with
        | Integer      t -> t.typeDefinition
        | Real         t -> t.typeDefinition
        | IA5String    t -> t.typeDefinition
        | OctetString  t -> t.typeDefinition
        | NullType     t -> t.typeDefinition
        | BitString    t -> t.typeDefinition
        | Boolean      t -> t.typeDefinition
        | Enumerated   t -> t.typeDefinition
        | SequenceOf   t -> t.typeDefinition
        | Sequence     t -> t.typeDefinition
        | Choice       t -> t.typeDefinition
    member this.tasInfo =
        match this with
        | Integer      t -> t.tasInfo
        | Real         t -> t.tasInfo
        | IA5String    t -> t.tasInfo
        | OctetString  t -> t.tasInfo
        | NullType     t -> t.tasInfo
        | BitString    t -> t.tasInfo
        | Boolean      t -> t.tasInfo
        | Enumerated   t -> t.tasInfo
        | SequenceOf   t -> t.tasInfo
        | Sequence     t -> t.tasInfo
        | Choice       t -> t.tasInfo

    member this.isIA5String =
        match this with
        | IA5String    _ -> true
        | _              -> false

    member this.asn1Name = 
        match this.id with
        | ReferenceToType((GenericFold2.MD _)::(GenericFold2.TA tasName)::[])   -> Some tasName
        | _                                                                     -> None

type State = {
    curSeqOfLevel : int
    currentTypes  : Asn1Type list
    currErrCode   : int

}

type ProgramUnit = {
    name    : string
    specFileName            : string
    bodyFileName            : string
    sortedTypeAssignments   : Asn1Type list
    valueAssignments        : Asn1GenericValue list
    importedProgramUnits    : string list
}



type AstRoot = {
    Files                   : Asn1File list
    args:CommandLineSettings
    valsMap                 : Map<ReferenceToValue, Asn1GenericValue>
    typesMap                : Map<ReferenceToType, Asn1Type>
    TypeAssignments         : Asn1Type list
    ValueAssignments        : Asn1GenericValue list
    programUnits            : ProgramUnit list
    acnConstants            : AcnTypes.AcnConstant list
    acnParameters           : CAst.AcnParameter list
    acnLinks                : CAst.AcnLink list
}

let getValueType (r:AstRoot) (v:Asn1GenericValue) =
    r.typesMap.[v.refToType]

