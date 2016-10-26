module BackendAst

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open c_utils


type PathToRoot = 
    PathToRoot of string list
type AccessPath = 
    | AccessPath of string

(*
Aphabet constraints e.g.
e.g. FROM "A" .. "Z" | "abcd"
*)
type CharComparisonBoolExp =
    | AlphaOr                   of CharComparisonBoolExp*CharComparisonBoolExp
    | AlphaAnd                  of CharComparisonBoolExp*CharComparisonBoolExp
    | AlphaNot                  of CharComparisonBoolExp
    | AlphaEq                   of AccessPath*char      
    | AlphaGreaterThan          of AccessPath*char     
    | AlphaGreaterThanOrEq      of AccessPath*char     
    | AlphaLessThan             of AccessPath*char     
    | AlphaLessThanOrEq         of AccessPath*char     
    | AlphaStringContainsChar   of AccessPath*string           
    


type AlphabetCheckFunc = {
    funcName : string
    con : CharComparisonBoolExp
}


type UnnamedVariableDeclaration =
    {
        privateName : string
        typereference : string*string
        value         : string  //needs to defined
    }
    

type BackendPrimaryNumericExpression =
    | IntegerLiteral            of BigInteger*string        //int value, prefix e.g L, UL etc
    | RealLiteral               of double
    | ReferenceToRangeVas       of (string*string)

(*
A BackendPrimaryExpression is an expression in the target language (C or Ada) 
It is either a constant (literal) or an identifier
*)
type BackendPrimaryExpression =
    | BackendPrimaryNumericExpression          of BackendPrimaryNumericExpression
    | StringLiteral             of string
    | CharLiteral               of char
    | EnumeratedTypeLiteral     of string
    | BooleanLiteral            of bool
    | ReferenceToVas            of (string*string)
    | NullTypeLiteral           

    

type BackendBooleanExpression =
    | OrConstraintExp            of BackendBooleanExpression*BackendBooleanExpression
    | AndConstraintExp           of BackendBooleanExpression*BackendBooleanExpression
    | NotConstraintExp           of BackendBooleanExpression
    | EqExp                      of AccessPath*BackendPrimaryExpression
    | GreaterThanExp             of AccessPath*BackendPrimaryNumericExpression
    | GreaterThanOrEqExp         of AccessPath*BackendPrimaryNumericExpression
    | LessThanExp                of AccessPath*BackendPrimaryNumericExpression
    | LessThanOrEqExp            of AccessPath*BackendPrimaryNumericExpression
    | CallAlphaFunc              of AccessPath*AlphabetCheckFunc
    | FixSizeBitStringEq         of AccessPath*UnnamedVariableDeclaration       
    | VarSizeBitStringEq         of AccessPath*UnnamedVariableDeclaration
    | FixSizeOctStringEq         of AccessPath*UnnamedVariableDeclaration
    | VarSizeOctStringEq         of AccessPath*UnnamedVariableDeclaration


type TypeIsValidFuncBody =
    | SequenceIsValidFuncBody       of SeqeunceComponentCheckBody list
    | SequenceOfIsValidFuncBody     of SeqeunceOfCheck
    | BaseTypeIsValidFuncBody       of BaseTypeIsValidFuncBody
with 
    member this.hasValidateFunc = false

and SeqeunceComponentCheckBody = 
    | CheckComponent            of PathToRoot*TypeIsValidFuncBody
    | CheckOptionalComponent    of PathToRoot*TypeIsValidFuncBody
    | CheckComponentIsPresent   of PathToRoot*AlwaysPresentOrAbsentCheck
    | CheckComponentIsAbsent    of PathToRoot*AlwaysPresentOrAbsentCheck

and AlwaysPresentOrAbsentCheck = {
    childExitsPath : string
    errorCode      : string
}    

and SeqeunceOfCheck = {
    path:PathToRoot
    childCheckBody:TypeIsValidFuncBody
    sIndex : string
    lengthCheckBody : TypeIsValidFuncBody
    nMax : BigInteger
    bFixed : bool
}

and BaseTypeIsValidFuncBody = {
    t:ConstraintType 
    path:PathToRoot
    alphaFuncName : string //= ToC ((path |> Seq.skip 1).StrJoin("_").Replace("#","elem"))
    errCodeName : string option //GetTypeConstraintsErrorCode t.Type.Constraints path r
    consCheck      : BackendBooleanExpression list
}

type TypeAssIsValidFunc = {
    funcName :string
    paramType: string
    sContent : TypeIsValidFuncBody
} with 
    member 
        this.LocalVars : LOCAL_VARIABLE list = 
            []
    member 
        this.AlphaCheckFunctions : AlphabetCheckFunc list = 
            []


