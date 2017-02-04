module DAst

open System
open System.Numerics

open FsUtils
open Constraints
open uPER2


type ExpOrStatement =
    | Expression 
    | Statement  

type LocalVariable =
    | SequenceOfIndex of int*int option        //i index, initialValue
with
    member this.VarName =
        match this with
        | SequenceOfIndex (i,_)   -> sprintf "i%d" i
    member this.GetDeclaration (l:BAst.ProgrammingLanguage) =
        match l, this with
        | BAst.C,    SequenceOfIndex (i,None)         -> sprintf "int i%d;" i
        | BAst.C,    SequenceOfIndex (i,Some iv)      -> sprintf "int i%d=%d;" i iv
        | BAst.Ada,  SequenceOfIndex (i,None)         -> sprintf "i%d:Integer;" i
        | BAst.Ada,  SequenceOfIndex (i,Some iv)      -> sprintf "i%d:Integer:=%d;" i iv

         //Emit_local_variable_SQF_Index(nI, bHasInitalValue)::="I<nI>:Integer<if(bHasInitalValue)>:=1<endif>;"

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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               // the body of the equal function
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list)) option  // a function that takes twos string and generates the equal expression (i.e. a1==a2 for integers)
    
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
    
    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass

}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons  = this.cons@this.withcons

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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list)) option  // for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list)) option  // for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list)) option  // for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list)) option  // for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionArrayPostfix : string
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list)) option  // for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list))  option// for c it will be the c_src.isEqual_Integer stg macro
    isValidBody         : (string -> string) option   // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyExp      : string -> string -> (string*(LocalVariable list))  option// for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyStats    : string -> string -> (string*(LocalVariable list))  option// for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
}
with 
    member this.Cons     = this.cons
    member this.WithCons = this.withcons
    member this.AllCons = this.cons@this.withcons



and SeqChildInfo = {
    name                :string
    chType              :Asn1Type
    optionality         :CAst.Asn1Optionality option
    acnInsertetField    :bool
    comments            :string list

    //DAst properties
    c_name              : string
    typeDefinitionBody  : string option //only the non acn children have typeDefinitions                       
    isEqualBodyStats    : string -> string -> string -> (string*(LocalVariable list)) option  // 
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
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyStats    : string -> string -> (string*(LocalVariable list)) option  // for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
    encodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    encodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
    decodeFuncName      : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    decodeFuncBody      : string -> string            // an stg macro according the acnEncodingClass
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

    //cast new properties
    acnMaxSizeInBits    : int
    acnMinSizeInBits    : int
    acnEncodingClass    : CAst.ChoiceAcnEncClass
    alignment           : CAst.AcnAligment option

    //DAst properties
    typeDefinitionName  : string option               // has value only for top level asn1 types (i.e. TypeAssignments (TAS))
    typeDefinitionBody  : string                      // for C it will be Asn1SInt or Asn1UInt
    isEqualFuncName     : string option               // the name of the equal function. Valid only for TASes)
    isEqualFunc         : string option               
    isEqualBodyStats    : string -> string -> (string*(LocalVariable list))  option// for c it will be the c_src.isEqual_Integer stg macro
    isValidFuncName     : string option               // it has value only for TASes and only if isValidBody has value
    isValidBody         : (string -> string) option   // 
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

    member this.isEqualBody =
        match this with
        | Integer      t -> Expression, t.isEqualBodyExp
        | Real         t -> Expression, t.isEqualBodyExp
        | IA5String    t -> Expression, t.isEqualBodyExp
        | OctetString  t -> Expression, t.isEqualBodyExp
        | NullType     t -> Expression, t.isEqualBodyExp
        | BitString    t -> Expression, t.isEqualBodyExp 
        | Boolean      t -> Expression, t.isEqualBodyExp
        | Enumerated   t -> Expression, t.isEqualBodyExp
        | SequenceOf   t -> Statement, t.isEqualBodyStats
        | Sequence     t -> Statement, t.isEqualBodyStats
        | Choice       t -> Statement, t.isEqualBodyStats 
    member this.isEqualFunc =
        match this with
        | Integer      t -> t.isEqualFunc
        | Real         t -> t.isEqualFunc
        | IA5String    t -> t.isEqualFunc
        | OctetString  t -> t.isEqualFunc
        | NullType     t -> t.isEqualFunc
        | BitString    t -> t.isEqualFunc
        | Boolean      t -> t.isEqualFunc
        | Enumerated   t -> t.isEqualFunc
        | SequenceOf   t -> t.isEqualFunc
        | Sequence     t -> t.isEqualFunc
        | Choice       t -> t.isEqualFunc

    member this.typeDefinitionName =
        match this with
        | Integer      t -> t.typeDefinitionName
        | Real         t -> t.typeDefinitionName
        | IA5String    t -> t.typeDefinitionName
        | OctetString  t -> t.typeDefinitionName
        | NullType     t -> t.typeDefinitionName
        | BitString    t -> t.typeDefinitionName
        | Boolean      t -> t.typeDefinitionName
        | Enumerated   t -> t.typeDefinitionName
        | SequenceOf   t -> t.typeDefinitionName
        | Sequence     t -> t.typeDefinitionName
        | Choice       t -> t.typeDefinitionName


    member this.typeDefinitionBody =
        match this with
        | Integer      t -> t.typeDefinitionBody
        | Real         t -> t.typeDefinitionBody
        | IA5String    t -> t.typeDefinitionBody
        | OctetString  t -> t.typeDefinitionBody
        | NullType     t -> t.typeDefinitionBody
        | BitString    t -> t.typeDefinitionBody
        | Boolean      t -> t.typeDefinitionBody
        | Enumerated   t -> t.typeDefinitionBody
        | SequenceOf   t -> t.typeDefinitionBody
        | Sequence     t -> t.typeDefinitionBody
        | Choice       t -> t.typeDefinitionBody
    member this.getTypeDefinition (l:BAst.ProgrammingLanguage)=
        match this.typeDefinitionName with
        | None  -> None
        | Some typeDefinitionName   ->
            match l with
            | BAst.C ->  
                let typeDefinitionArrayPostfix = match this.typeDefinitionArrayPostfix with None -> "" | Some x -> x
                Some (sprintf "typedef %s %s%s;" this.typeDefinitionBody typeDefinitionName typeDefinitionArrayPostfix)
            | BAst.Ada   ->
                let typeDefinitionArrayPostfix = match this.typeDefinitionArrayPostfix with None -> "" | Some x -> x
                Some(sprintf "typedef %s %s%s;" this.typeDefinitionBody typeDefinitionName typeDefinitionArrayPostfix)

    member this.typeDefinitionArrayPostfix =
        match this with
        | Integer      t -> None
        | Real         t -> None
        | OctetString  t -> None
        | NullType     t -> None
        | BitString    t -> None
        | Boolean      t -> None
        | Enumerated   t -> None
        | SequenceOf   t -> None
        | Sequence     t -> None
        | Choice       t -> None
        | IA5String    t -> Some(t.typeDefinitionArrayPostfix)
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


    member this.asn1Name = 
        match this.id with
        | ReferenceToType((GenericFold2.MD _)::(GenericFold2.TA tasName)::[])   -> Some tasName
        | _                                                                     -> None


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
    Encodings               : Ast.Asn1Encoding list
    GenerateEqualFunctions  : bool
    TypePrefix              : string
    AstXmlAbsFileName       : string
    IcdUperHtmlFileName     : string
    IcdAcnHtmlFileName      : string
    CheckWithOss            : bool
    mappingFunctionsModule  : string option
    valsMap                 : Map<ReferenceToValue, Asn1GenericValue>
    typesMap                : Map<ReferenceToType, Asn1Type>
    TypeAssignments         : Asn1Type list
    ValueAssignments        : Asn1GenericValue list
    programUnits            : ProgramUnit list
    integerSizeInBytes      : int
    acnConstants            : AcnTypes.AcnConstant list
    acnParameters           : CAst.AcnParameter list
    acnLinks                : CAst.AcnLink list
}
