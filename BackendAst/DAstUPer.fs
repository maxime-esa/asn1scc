module DAstUPer
open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open Constraints
open DAst

let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + codec.suffix))


let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : UPerFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    let funcName            = getFuncName r l codec o.tasInfo
    let errCodeName         = ToC ("ERR_UPER" + (codec.suffix.ToUpper()) + "_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let IntNoneRequired         = match l with C -> uper_c.IntNoneRequired          | Ada -> (fun p min   errCode codec -> uper_a.IntFullyConstraint p min min 0I errCode codec)
    let IntFullyConstraintPos   = match l with C -> uper_c.IntFullyConstraintPos    | Ada -> uper_a.IntFullyConstraint
    let IntFullyConstraint      = match l with C -> uper_c.IntFullyConstraint       | Ada -> uper_a.IntFullyConstraint
    let IntSemiConstraintPos    = match l with C -> uper_c.IntSemiConstraintPos     | Ada -> uper_a.IntSemiConstraint
    let IntSemiConstraint       = match l with C -> uper_c.IntSemiConstraint        | Ada -> uper_a.IntSemiConstraint
    let IntUnconstraint         = match l with C -> uper_c.IntUnconstraint          | Ada -> uper_a.IntUnconstraint
    let IntRootExt              = match l with C -> uper_c.IntRootExt               | Ada -> uper_a.IntRootExt
    let IntRootExt2             = match l with C -> uper_c.IntRootExt2              | Ada -> uper_a.IntRootExt2
    let EmitTypeAssignment_primitive = match l with C -> uper_c.EmitTypeAssignment_primitive    | Ada -> uper_a.EmitTypeAssignment
    let EmitTypeAssignment_primitive_def = match l with C -> uper_c.EmitTypeAssignment_primitive_def    | Ada -> uper_a.EmitTypeAssignment_def
    let EmitTypeAssignment_def_err_code  = match l with C -> uper_c.EmitTypeAssignment_def_err_code    | Ada -> uper_a.EmitTypeAssignment_def_err_code

    let funcBody (p:String) = 
        let rootCons = o.Cons |> List.choose(fun x -> match x with RangeRootConstraint(a) |RangeRootConstraint2(a,_) -> Some(x) |_ -> None) 
        let IntBod uperRange extCon =
            match uperRange with
            | uPER2.Concrete(min, max) when min=max                    -> IntNoneRequired p min   errCode.errCodeName codec 
            | uPER2.Concrete(min, max) when min>=0I && (not extCon)    -> IntFullyConstraintPos p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode.errCodeName codec
            | uPER2.Concrete(min, max)                                 -> IntFullyConstraint p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode.errCodeName codec
            | uPER2.PosInf(a)  when a>=0I && (not extCon)  -> IntSemiConstraintPos p a  errCode.errCodeName codec
            | uPER2.PosInf(a)               -> IntSemiConstraint p a  errCode.errCodeName codec
            | uPER2.NegInf(max)             -> IntUnconstraint p errCode.errCodeName codec
            | uPER2.Full                    -> IntUnconstraint p errCode.errCodeName codec

        let getValueByConstraint uperRange =
            match uperRange with
            | uPER2.Concrete(a, _)  -> a
            | uPER2.PosInf(a)       -> a
            | uPER2.NegInf(b)       -> b
            | uPER2.Full            -> 0I

        match rootCons with
        | []                            -> IntBod o.uperRange false
        | (RangeRootConstraint a)::rest      -> 
            let uperR    = uPER2.getIntTypeConstraintUperRange [a]  o.Location
            let cc = DAstValidate.foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString()) p a
            IntRootExt p (getValueByConstraint uperR) cc (IntBod uperR true) errCode.errCodeName codec
        | (RangeRootConstraint2(a,_))::rest  -> 
            let uperR    = uPER2.getIntTypeConstraintUperRange [a]  o.Location
            let cc = DAstValidate.foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString()) p a
            IntRootExt2 p (getValueByConstraint uperR) cc (IntBod uperR true) errCode.errCodeName codec 
        | _                             -> raise(BugErrorException "")

    let topLevAcc, p =  
        match l, codec with 
        | C, Ast.Codec.Decode -> "->", "pVal" 
        | _                   -> ".", "val"

    let isValidFuncName = match isValidFunc with None -> None | Some f -> f.funcName
    let  func  = 
            match funcName  with
            | None              -> None
            | Some funcName     -> 
                let content = funcBody p  
                Some(EmitTypeAssignment_primitive funcName isValidFuncName  typeDefinition.name []  content codec)
    let  funcDef  = 
            match funcName with
            | None              -> None
            | Some funcName     -> 
                Some(EmitTypeAssignment_primitive_def funcName  typeDefinition.name [(EmitTypeAssignment_def_err_code errCode.errCodeName) (BigInteger errCode.errCodeValue)] (o.uperMaxSizeInBits = 0) (BigInteger (ceil ((double o.uperMaxSizeInBits)/8.0))) (BigInteger o.uperMaxSizeInBits) codec)


    let ret = 
        {
            UPerFunction.errCodes      = [errCode]      
            funcName                   = funcName
            func                       = func 
            funcDef                    = funcDef
            funcBody                   = funcBody
            funcBody2                  = (fun p acc -> funcBody p)
            localVariables             = []
        }
    ret, {us with currErrCode = us.currErrCode + 1}


