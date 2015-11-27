(*
* Copyright (c) 2008-2012 Semantix and (c) 2012-2015 Neuropublic
*
* This file is part of the ASN1SCC tool.
*
* Licensed under the terms of GNU General Public Licence as published by
* the Free Software Foundation.
*
*  For more informations see License.txt file
*)

module c_validate2

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open c_utils


type TasValidateFunc = {
    moduleName  : string // the module where this function lives. I C, this is dummy
    functionName: string 
    validateType: string //e.g. MyStruct*
    typeContent : ValidatedTypeStatementBlock
}
with
  member this.LocalVariables : List<LocalVariable> =
    []

and LocalVariable = {
    varName:string
    varType:string //e.g. int, char* etc
}

and ValidatedTypeStatementBlock =
    | BaseTypedValidateTypeStatementBlock of BaseTypedValidateTypeStatementBlock
    | RefTypedValidateTypeStatementsBlock of RefTypedValidateTypeStatementsBlock
    | SeqOfTypedValidateTypeStatementsBlock of SeqOfTypedValidateTypeStatementsBlock
    | ChoiceTypedValidateTypeStatementsBlock of ChoiceTypedValidateTypeStatementsBlock
    | SequenceTypedValidateTypeStatementsBlock  of SequenceTypedValidateTypeStatementsBlock
    with
        member x.AccessPath : string =
            match x with
            | BaseTypedValidateTypeStatementBlock        x  -> x.accessPath
            | RefTypedValidateTypeStatementsBlock        x  -> x.accessPath
            | SeqOfTypedValidateTypeStatementsBlock      x  -> x.accessPath
            | ChoiceTypedValidateTypeStatementsBlock     x  -> x.accessPath
            | SequenceTypedValidateTypeStatementsBlock   x  -> x.accessPath

and BaseTypedValidateTypeStatementBlock = {
    accessPath : string                 //e.g. pVal->field1.field2, pVal->array1[i1]
    returnErrorCode : int               //error code to return if validations fail
    validatedContraintExpressions : ValidatedContraintExpression list
}

and RefTypedValidateTypeStatementsBlock = {
    accessPath : string                 //e.g. pVal->field1.field2
    refencedTasFunc     : (string*string) // the function to be called
}

and SeqOfTypedValidateTypeStatementsBlock = {
    accessPath : string                         //e.g. pVal->field1.field2
    index      : LocalVariable
    LengthType : bool                           
    validatedSizeContraintExpressions : ValidatedContraintExpression list
    child : ValidatedTypeStatementBlock
}

and ChoiceTypedValidateTypeStatementsBlock = {
    accessPath : string                         //e.g. pVal->field1.field2
    contraintExpressions : ValidatedContraintExpression list        //usually this is empty
    children : (string*ValidatedTypeStatementBlock) list        //present expression, child block
}

and SequenceTypedValidateTypeStatementsBlock = {
    accessPath : string                         //e.g. pVal->field1.field2
    contraintExpressions : ValidatedContraintExpression list        //usually this is empty
    children : SequenceChildTypedValidateTypeStatementsBlock list
}

and SequenceChildTypedValidateTypeStatementsBlock = 
    | MandatoryChild of ValidatedTypeStatementBlock                 //child block
    | OptionalChild of string*ValidatedTypeStatementBlock           //child exists expression, child block
    | AlwaysPresentChild of string*ValidatedTypeStatementBlock      //child exists expression, child block
    | NeverPresentChild of string                                   //child exists expression


and LengthType =
    | Fixed of BigInteger   // this is the case for fixed size sequence/octet strings etc e.g. SEQUENCE (SIZE(10)) OF SOME-TYPE
    | VarSize               // this is the case for variable size sequence/octet strings etc e.g. SEQUENCE (SIZE(10..20)) OF SOME-TYPE

and Reference =     Reference of string*string


and BooleanBinaryOperator =
    | LogicalOr
    | LogicalAnd

and ValidatedContraintExpression = 
    | PrimEqualExpr                             of string*string                        //checked expression it must evaluate to int, char, enum real, value                 -> exp == v in C or exp = v in Ada
    | StringEqualExpr                           of string*string                        //checked expression, value                 -> strcpm(exp,v) in C or exp = v in Ada
    | RangeExpr                                 of string*(string*bool)*(string*bool)   //checked expr, lower value, upper value    -> lv <= exp && exp <= uv
    | LesserThan                                of string*(string*bool)                 //checked expr, value                       -> exp <= v
    | GreaterThan                               of string*(string*bool)                 //checked expr, value                       -> exp >= v
    | AlwaysTrue                                
    | CharInStringExp                           of string*string                        //checked expression, string with valid char set e.g. IA5String(FROM ("ABCDEF"))  
    | BinaryOpExpr                              of BooleanBinaryOperator*ValidatedContraintExpression*ValidatedContraintExpression     // orperator, exp1, exp2
    | NotExpr                                   of ValidatedContraintExpression





let createValidationAst (lang:Ast.ProgrammingLanguage) (app:AstRoot) =
    GenericFold.foldAstRoot
        //1. roorFunc r files
        (fun r files -> files)

        //2. fileFunc r f modules
        (fun r f modules -> (f.FileNameWithoutExtension, modules) )

        //3. modFunc r f m tases vases
        (fun r f m tasses vases -> (m.CName, tasses))

        //4. tasFunc r f m tas asn1Type
        (fun r f m tas t -> {TasValidateFunc.moduleName = m.CName; functionName = tas.c_name; validateType=tas.c_name; typeContent = t})

        //5. vasFunc r f m vas asn1Type asn1Value
        (fun r f m vas t v -> 0)

        //6. refTypeFunc r f m ref newActType refCons
        (fun s mdName tasName newActType refCons -> RefTypedValidateTypeStatementsBlock {RefTypedValidateTypeStatementsBlock.accessPath=""; refencedTasFunc=(mdName, tasName)})

        //7. baseTypeFunc 
        (fun s t newCons -> BaseTypedValidateTypeStatementBlock {BaseTypedValidateTypeStatementBlock.accessPath=""; returnErrorCode=0; validatedContraintExpressions=newCons})

        //8. enmItemFunc 
        (fun s t newEnmItems newCons -> BaseTypedValidateTypeStatementBlock {BaseTypedValidateTypeStatementBlock.accessPath=""; returnErrorCode=0; validatedContraintExpressions=newCons})

        //9. seqOfTypeFunc 
        (fun  s t  newInnerType newCons -> 
            SeqOfTypedValidateTypeStatementsBlock
                {
                    SeqOfTypedValidateTypeStatementsBlock.accessPath = ""
                    index      = {LocalVariable.varName = ""; varType = ""}
                    LengthType  = false
                    validatedSizeContraintExpressions = newCons
                    child = newInnerType
                }
        )

        //10. seqTypeFunc 
        (fun  s t newChildren newCons   ->
            SequenceTypedValidateTypeStatementsBlock
                {
                    SequenceTypedValidateTypeStatementsBlock.accessPath = ""
                    contraintExpressions = newCons
                    children = newChildren
                }
        )

        //11. chTypeFunc 
        (fun s t newChildren newCons ->
            ChoiceTypedValidateTypeStatementsBlock
                {
                    ChoiceTypedValidateTypeStatementsBlock.accessPath = ""
                    contraintExpressions = newCons
                    children = newChildren
                }        
        )

        //12. sequenceChildFunc 
        (fun  s chInfo newType newDefValue ->
            match chInfo.Optionality with
            | Some AlwaysAbsent     -> NeverPresentChild ""
            | Some AlwaysPresent    -> AlwaysPresentChild("", newType)
            | Some Optional         
            | Some (Default _)      -> OptionalChild ("", newType)
            | None                  -> MandatoryChild newType
        )

        //13. choiceChildFunc 
        (fun s   chInfo newType -> (chInfo.CName_Present lang, newType) )

        //14. refValueFunc  
        (fun s t (md,vs) newActVal -> vs)

        //15. enumValueFunc 
        (fun s t actType enmItem  ni -> enmItem.CEnumName s.r lang)

        //16. intValFunc 
        (fun s t actType bi  -> bi.ToString())

        //17. realValFunc 
        (fun s t actType d  -> d.ToString())

        //18. ia5StringValFunc
        (fun s t actType str  -> "\"" + str + "\"") 
        //19. numStringValFunc 
        (fun s t actType str  -> "\"" + str + "\"")

        //20. boolValFunc 
        (fun s t actType b  -> c_var.PrintBooleanValue b)

        //21. octetStringValueFunc 
        (fun s t actType b -> "octec string value")

        //22. bitStringValueFunc 
        (fun s t actType b -> "bit string value")

        //23. nullValueFunc 
        (fun s t actType  -> "0")

        //24. seqOfValueFunc 
        (fun s t actType  newVals -> "sequence of value")

        //25. seqValueFunc 
        (fun s t actType newValues -> "sequence value")

        //26. chValueFunc
        (fun  s t actType name newValue-> "choice value")

        //27. singleValueContraintFunc 
        (fun s t ck actType newValue -> 
            match t.Kind with
            | NumericString | IA5String -> StringEqualExpr (actType.AccessPath,newValue)
            | _                         -> PrimEqualExpr (actType.AccessPath,newValue))

        //28. rangeContraintFunc 
        (fun s t ck actType newValue1 newValue2 b1 b2 -> RangeExpr(actType.AccessPath, (newValue1, b1), (newValue2, b2)))

        //29. greaterThanContraintFunc
        (fun s t ck actType newValue  b -> GreaterThan(actType.AccessPath, (newValue, b)))

        //30. lessThanContraintFunc
        (fun s t ck actType newValue  b -> LesserThan(actType.AccessPath, (newValue, b)))

        //31. alwaysTtrueContraintFunc
        (fun s t checContent actType -> AlwaysTrue)

        //32. typeInclConstraintFunc
        (fun s t actType (md,tas) -> raise(BugErrorException "This constraint should have been removed"))

        //33. unionConstraintFunc
        (fun s t actType nc1 nc2 -> BinaryOpExpr (LogicalAnd, nc1, nc2))

        //34. intersectionConstraintFunc
        (fun s t actType nc1 nc2 -> BinaryOpExpr (LogicalOr, nc1, nc2))

        //35. notConstraintFunc
        (fun s t actType nc      -> NotExpr nc)

        //36. exceptConstraintFunc
        (fun s t actType nc1 nc2 -> BinaryOpExpr (LogicalAnd, nc1, NotExpr nc2))

        //37. rootConstraintFunc
        (fun s t actType nc -> nc)

        //38. root2ConstraintFunc
        (fun s t actType nc1 nc2 -> BinaryOpExpr (LogicalAnd, nc1, nc2))

        app