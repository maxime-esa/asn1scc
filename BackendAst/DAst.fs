module DAst

open System
open System.Numerics
open FsUtils
open CommonTypes
//open Constraints



type ProgrammingLanguage =
    |C
    |Ada

type VarScopNode =
    | VA2 of string      //VALUE ASSIGNMENT
    | DV        //DEFAULT VALUE
    | NI  of string      //NAMED ITEM VALUE (enum)
    | CON of int         // constraint index
    | SQOV of int             //SEQUENCE OF VALUE (value index)
    | SQCHILD   of string   //child value (SEQUENCE, CHOICE)
    | VL of int         //value index
    | IMG of int        //non ASN.1 value. Required when constructing values for types in backends

type ReferenceToValue = 
    | ReferenceToValue of (ScopeNode list)*(VarScopNode list)
    with
        member this.ModName =
            match this with
            | ReferenceToValue (path,_) -> 
                match path with
                | (MD modName)::_    -> modName
                | _                               -> raise(BugErrorException "Did not find module at the begining of the scope path")



type Asn1GenericValue = Asn1Value

type FuncParamType =
  | VALUE       of string
  | POINTER     of string
  | FIXARRAY    of string

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

(*
type BaseTypesEquivalence<'T> = {
    typeDefinition  : 'T option
    uper            : 'T option
    acn             : 'T option
}
*)    
        
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
    baseInfo             : Asn1AcnAst.Integer

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<Integer>

    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.IntegerValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction
    acnEncFunction      : AcnFunction
    acnDecFunction      : AcnFunction
    

}

type Enumerated = {
    baseInfo             : Asn1AcnAst.Enumerated

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<Enumerated>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.EnumValue
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

type Real = {
    baseInfo             : Asn1AcnAst.Real

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<Real>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.RealValue
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


type Boolean = {
    baseInfo             : Asn1AcnAst.Boolean

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<Boolean>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.BooleanValue
    initFunction        : InitFunction
    equalFunction       : EqualFunction
    isValidFunction     : IsValidFunction option      // it is optional because some types do not require an IsValid function (e.g. an unconstraint integer)
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction
    acnEncFunction      : AcnFunction
    acnDecFunction      : AcnFunction
}


type NullType = {
    baseInfo             : Asn1AcnAst.NullType

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<NullType>
    typeDefinition      : TypeDefinitionCommon
    initFunction        : InitFunction
    initialValue        : Asn1AcnAst.NullValue
    equalFunction       : EqualFunction
    uperEncFunction     : UPerFunction
    uperDecFunction     : UPerFunction

    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}


type StringType = {
    baseInfo             : Asn1AcnAst.StringType

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<StringType>
    typeDefinition      : TypeDefinitionCommon
    initialValue        :  Asn1AcnAst.StringValue
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


type OctetString = {
    baseInfo             : Asn1AcnAst.OctetString


    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<OctetString>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.OctetStringValue
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



type BitString = {
    baseInfo             : Asn1AcnAst.BitString

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<BitString>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.BitStringValue
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


type SequenceOf = {
    baseInfo            : Asn1AcnAst.SequenceOf
    childType           : Asn1Type

    //DAst properties
    //baseTypeEquivalence: BaseTypesEquivalence<SequenceOf>
    typeDefinition      : TypeDefinitionCommon
    initialValue        : Asn1AcnAst.SeqOfValue
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
    //valsMap                 : Map<ReferenceToValue, Asn1GenericValue>
    typesMap                : Map<ReferenceToType, Asn1Type>
    TypeAssignments         : Asn1Type list
    ValueAssignments        : Asn1GenericValue list
    programUnits            : ProgramUnit list
    acnConstants            : Map<string, BigInteger>
    acnLinks                : AcnLink list
}


