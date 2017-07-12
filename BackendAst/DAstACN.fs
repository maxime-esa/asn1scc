module DAstACN

open System
open System.Numerics
open System.IO

open FsUtils
open CommonTypes
open Asn1AcnAst
open Asn1AcnAstUtilFunctions
open DAst
open DAstUtilFunctions

let getFuncName (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (typeId:ReferenceToType) =
    typeId.tasInfo |> Option.map (fun x -> ToC2(r.args.TypePrefix + x.tasName + "_ACN" + codec.suffix))

let getTypeDefinitionName (tasInfo:TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) =
    match tasInfo with
    | Some _                -> typeDefinition.name
    | None (*inner type*)   -> typeDefinition.typeDefinitionBodyWithinSeq

let callBaseTypeFunc l = match l with C -> uper_c.call_base_type_func | Ada -> uper_a.call_base_type_func


let getAcnDeterminantName (id : ReferenceToType) =
    match id with
    | ReferenceToType path ->
        match path with
        | (MD mdName)::(TA tasName)::(PRM prmName)::[]   -> ToC2 prmName
        | _ ->
            let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
            ToC2(longName.Replace("#","elem"))


let createPrimitiveFunction (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (t:Asn1AcnAst.Asn1Type) (typeDefinition:TypeDefinitionCommon) (isValidFunc: IsValidFunction option)  (funcBody:ErroCode->FuncParamType -> (AcnFuncBodyResult option)) soSparkAnnotations (us:State)  =
    let funcNameAndtasInfo   = getFuncName r l codec t.id
    let errCodeName         = ToC ("ERR_ACN" + (codec.suffix.ToUpper()) + "_" + ((t.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let EmitTypeAssignment_primitive     =  match l with C -> acn_c.EmitTypeAssignment_primitive        | Ada -> acn_c.EmitTypeAssignment_primitive
    let EmitTypeAssignment_primitive_def =  match l with C -> acn_c.EmitTypeAssignment_primitive_def    | Ada -> acn_c.EmitTypeAssignment_primitive_def
    let EmitTypeAssignment_def_err_code  =  match l with C -> acn_c.EmitTypeAssignment_def_err_code     | Ada -> acn_c.EmitTypeAssignment_def_err_code

    let funcBody = (funcBody errCode)
    let p : FuncParamType = t.getParamType l codec
    let topLevAcc = p.getAcces l
    let varName = p.p
    let sStar = p.getStar l
    let isValidFuncName = match isValidFunc with None -> None | Some f -> f.funcName
    let sInitilialExp = ""
    let  func, funcDef  = 
            match funcNameAndtasInfo  with
            | None              -> None, None
            | Some funcName     -> 
                let content = funcBody p  
                match content with 
                | None          -> None, None
                | Some bodyResult  ->
                    let handleAcnParameter (p:Asn1AcnAst.AcnParameter) =
                        let intType  = match l with C -> header_c.Declare_Integer () | Ada -> header_a.Declare_Integer ()
                        let boolType = match l with C -> header_c.Declare_Boolean () | Ada -> header_a.Declare_BOOLEAN ()
                        let emitPrm  = match l with C -> acn_c.EmitAcnParameter      | Ada -> acn_c.EmitAcnParameter
                        match p.asn1Type with
                        | Asn1AcnAst.AcnPrmInteger    loc          -> emitPrm p.c_name intType
                        | Asn1AcnAst.AcnPrmBoolean    loc          -> emitPrm p.c_name boolType
                        | Asn1AcnAst.AcnPrmNullType   loc          -> raise(SemanticError (loc, "Invalid type for parameter"))
                        | Asn1AcnAst.AcnPrmRefType(md,ts)           -> emitPrm p.c_name ts.Value

                    let lvars = bodyResult.localVariables |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                    let prms = t.acnParameters |> List.map handleAcnParameter
                    let func = Some(EmitTypeAssignment_primitive varName sStar funcName isValidFuncName  typeDefinition.name lvars  bodyResult.funcBody soSparkAnnotations sInitilialExp prms codec)
                
                    let errCodes = bodyResult.errCodes
                    let errCodStr = errCodes |> List.map(fun x -> (EmitTypeAssignment_def_err_code x.errCodeName) (BigInteger x.errCodeValue))
                    let funcDef = Some(EmitTypeAssignment_primitive_def varName sStar funcName  typeDefinition.name errCodStr (t.acnMaxSizeInBits = 0) (BigInteger (ceil ((double t.acnMaxSizeInBits)/8.0))) (BigInteger t.acnMaxSizeInBits) prms codec)
                    func, funcDef


    let ret = 
        {
            AcnFunction.funcName       = funcNameAndtasInfo 
            func                       = func 
            funcDef                    = funcDef
            funcBody                   = funcBody
        }
    ret, {us with currErrCode = us.currErrCode + 1}

let private createAcnIntegerFunctionInternal (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) acnEncodingClass (uperfuncBody : FuncParamType -> (UPERFuncBodyResult option)) : (ErroCode -> FuncParamType -> (AcnFuncBodyResult option))  =
    let PositiveInteger_ConstSize_8                  = match l with C -> acn_c.PositiveInteger_ConstSize_8                | Ada -> acn_c.PositiveInteger_ConstSize_8               
    let PositiveInteger_ConstSize_big_endian_16      = match l with C -> acn_c.PositiveInteger_ConstSize_big_endian_16    | Ada -> acn_c.PositiveInteger_ConstSize_big_endian_16   
    let PositiveInteger_ConstSize_little_endian_16   = match l with C -> acn_c.PositiveInteger_ConstSize_little_endian_16 | Ada -> acn_c.PositiveInteger_ConstSize_little_endian_16
    let PositiveInteger_ConstSize_big_endian_32      = match l with C -> acn_c.PositiveInteger_ConstSize_big_endian_32    | Ada -> acn_c.PositiveInteger_ConstSize_big_endian_32   
    let PositiveInteger_ConstSize_little_endian_32   = match l with C -> acn_c.PositiveInteger_ConstSize_little_endian_32 | Ada -> acn_c.PositiveInteger_ConstSize_little_endian_32
    let PositiveInteger_ConstSize_big_endian_64      = match l with C -> acn_c.PositiveInteger_ConstSize_big_endian_64    | Ada -> acn_c.PositiveInteger_ConstSize_big_endian_64   
    let PositiveInteger_ConstSize_little_endian_64   = match l with C -> acn_c.PositiveInteger_ConstSize_little_endian_64 | Ada -> acn_c.PositiveInteger_ConstSize_little_endian_64
    let PositiveInteger_ConstSize                    = match l with C -> acn_c.PositiveInteger_ConstSize                  | Ada -> acn_c.PositiveInteger_ConstSize                 
    let TwosComplement_ConstSize_8                   = match l with C -> acn_c.TwosComplement_ConstSize_8                 | Ada -> acn_c.TwosComplement_ConstSize_8                
    let TwosComplement_ConstSize_big_endian_16       = match l with C -> acn_c.TwosComplement_ConstSize_big_endian_16     | Ada -> acn_c.TwosComplement_ConstSize_big_endian_16    
    let TwosComplement_ConstSize_little_endian_16    = match l with C -> acn_c.TwosComplement_ConstSize_little_endian_16  | Ada -> acn_c.TwosComplement_ConstSize_little_endian_16 
    let TwosComplement_ConstSize_big_endian_32       = match l with C -> acn_c.TwosComplement_ConstSize_big_endian_32     | Ada -> acn_c.TwosComplement_ConstSize_big_endian_32    
    let TwosComplement_ConstSize_little_endian_32    = match l with C -> acn_c.TwosComplement_ConstSize_little_endian_32  | Ada -> acn_c.TwosComplement_ConstSize_little_endian_32 
    let TwosComplement_ConstSize_big_endian_64       = match l with C -> acn_c.TwosComplement_ConstSize_big_endian_64     | Ada -> acn_c.TwosComplement_ConstSize_big_endian_64    
    let TwosComplement_ConstSize_little_endian_64    = match l with C -> acn_c.TwosComplement_ConstSize_little_endian_64  | Ada -> acn_c.TwosComplement_ConstSize_little_endian_64 
    let TwosComplement_ConstSize                     = match l with C -> acn_c.TwosComplement_ConstSize                   | Ada -> acn_c.TwosComplement_ConstSize                  
    let ASCII_ConstSize                              = match l with C -> acn_c.ASCII_ConstSize                            | Ada -> acn_c.ASCII_ConstSize                           
    let ASCII_VarSize_NullTerminated                 = match l with C -> acn_c.ASCII_VarSize_NullTerminated               | Ada -> acn_c.ASCII_VarSize_NullTerminated              
    let ASCII_UINT_ConstSize                         = match l with C -> acn_c.ASCII_UINT_ConstSize                       | Ada -> acn_c.ASCII_UINT_ConstSize                      
    let ASCII_UINT_VarSize_NullTerminated            = match l with C -> acn_c.ASCII_UINT_VarSize_NullTerminated          | Ada -> acn_c.ASCII_UINT_VarSize_NullTerminated         
    let BCD_ConstSize                                = match l with C -> acn_c.BCD_ConstSize                              | Ada -> acn_c.BCD_ConstSize                             
    let BCD_VarSize_NullTerminated                   = match l with C -> acn_c.BCD_VarSize_NullTerminated                 | Ada -> acn_c.BCD_VarSize_NullTerminated                

    //let errCodeName         = ToC ("ERR_ACN" + (codec.suffix.ToUpper()) + "_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    //let errCodeValue        = us.currErrCode
    //let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let funcBody (errCode:ErroCode) (p:FuncParamType)        = 
        let pp = match codec with CommonTypes.Encode -> p.getValue l | CommonTypes.Decode -> p.getPointer l
        let funcBodyContent = 
            match acnEncodingClass with
            |Asn1AcnAst.Integer_uPER                                       ->  uperfuncBody p |> Option.map(fun x -> x.funcBody, x.errCodes)
            |Asn1AcnAst.PositiveInteger_ConstSize_8                        ->  Some(PositiveInteger_ConstSize_8 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize_big_endian_16            ->  Some(PositiveInteger_ConstSize_big_endian_16 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize_little_endian_16         ->  Some(PositiveInteger_ConstSize_little_endian_16 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize_big_endian_32            ->  Some(PositiveInteger_ConstSize_big_endian_32 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize_little_endian_32         ->  Some(PositiveInteger_ConstSize_little_endian_32 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize_big_endian_64            ->  Some(PositiveInteger_ConstSize_big_endian_64 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize_little_endian_64         ->  Some(PositiveInteger_ConstSize_little_endian_64 pp None codec, [])
            |Asn1AcnAst.PositiveInteger_ConstSize bitSize                  ->  Some(PositiveInteger_ConstSize pp (BigInteger bitSize) None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_8                         ->  Some(TwosComplement_ConstSize_8 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_big_endian_16             ->  Some(TwosComplement_ConstSize_big_endian_16 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_little_endian_16          ->  Some(TwosComplement_ConstSize_little_endian_16 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_big_endian_32             ->  Some(TwosComplement_ConstSize_big_endian_32 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_little_endian_32          ->  Some(TwosComplement_ConstSize_little_endian_32 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_big_endian_64             ->  Some(TwosComplement_ConstSize_big_endian_64 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize_little_endian_64          ->  Some(TwosComplement_ConstSize_little_endian_64 pp None codec, [])
            |Asn1AcnAst.TwosComplement_ConstSize bitSize                   ->  Some(TwosComplement_ConstSize pp (BigInteger bitSize) None codec, [])
            |Asn1AcnAst.ASCII_ConstSize size                               ->  Some(ASCII_ConstSize pp ((BigInteger size)/8I) None codec, [])
            |Asn1AcnAst.ASCII_VarSize_NullTerminated nullByte              ->  Some(ASCII_VarSize_NullTerminated pp None codec, [])
            |Asn1AcnAst.ASCII_UINT_ConstSize size                          ->  Some(ASCII_UINT_ConstSize pp ((BigInteger size)/8I) None codec, [])
            |Asn1AcnAst.ASCII_UINT_VarSize_NullTerminated nullByte         ->  Some(ASCII_UINT_VarSize_NullTerminated pp  None codec, [])
            |Asn1AcnAst.BCD_ConstSize size                                 ->  Some(BCD_ConstSize pp ((BigInteger size)/4I) None codec, [])
            |Asn1AcnAst.BCD_VarSize_NullTerminated nullByte                ->  Some(BCD_VarSize_NullTerminated pp None codec, [])
        match funcBodyContent with
        | None -> None
        | Some (funcBodyContent,errCodes) -> Some ({AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = errCode::errCodes; localVariables = []})
    //let funcBody = (funcBody errCode)
    funcBody


let createAcnIntegerFunction (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (typeId : ReferenceToType) (t:Asn1AcnAst.AcnInteger)  (us:State)  =
    let errCodeName         = ToC ("ERR_ACN" + (codec.suffix.ToUpper()) + "_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let uperFuncBody (p:FuncParamType) = 
        let pp = match codec with CommonTypes.Encode -> p.getValue l | CommonTypes.Decode -> p.getPointer l
        let IntUnconstraint = match l with C -> uper_c.IntUnconstraint          | Ada -> uper_a.IntUnconstraint
        let funcBodyContent = IntUnconstraint pp errCode.errCodeName codec
        Some {UPERFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []}    

    let funcBody = createAcnIntegerFunctionInternal r l codec t.acnEncodingClass uperFuncBody
    (funcBody errCode), {us with currErrCode = us.currErrCode + 1}



let createIntegerFunction (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : AcnFunction option) (isValidFunc: IsValidFunction option) (uperFunc: UPerFunction) (us:State)  =
    let funcBody = createAcnIntegerFunctionInternal r l codec o.acnEncodingClass uperFunc.funcBody
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec t typeDefinition isValidFunc  (fun e p -> funcBody e p) soSparkAnnotations us





let nestChildItems (l:ProgrammingLanguage) (codec:CommonTypes.Codec) children = 
    let printChild (content:string) (sNestedContent:string option) = 
        match sNestedContent with
        | None  -> content
        | Some c-> 
            match l with
            | C        -> equal_c.JoinItems content sNestedContent
            | Ada      -> uper_a.JoinItems content sNestedContent
    let rec printChildren children : Option<string> = 
        match children with
        |[]     -> None
        |x::xs  -> 
            match printChildren xs with
            | None                 -> Some (printChild x  None)
            | Some childrenCont    -> Some (printChild x  (Some childrenCont))
    printChildren children



let createAcnBooleanFunction (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec)  (typeId : ReferenceToType) (o:Asn1AcnAst.AcnBoolean)  (us:State)  =
    let errCodeName         = ToC ("ERR_ACN" + (codec.suffix.ToUpper()) + "_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with CommonTypes.Encode -> p.getValue l | CommonTypes.Decode -> p.getPointer l
        let Boolean         = match l with C -> uper_c.Boolean          | Ada -> uper_a.Boolean
        let funcBodyContent = 
            Boolean pp errCode.errCodeName codec
        Some {AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []}    
    (funcBody errCode), {us with currErrCode = us.currErrCode + 1}

let createBooleanFunction (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Boolean) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : AcnFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    // todo use BolleanAcnEncodingClass

    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with CommonTypes.Encode -> p.getValue l | CommonTypes.Decode -> p.getPointer l
        let Boolean         = match l with C -> uper_c.Boolean          | Ada -> uper_a.Boolean
        let funcBodyContent = 
            Boolean pp errCode.errCodeName codec
        {AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []}    
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec t typeDefinition  isValidFunc  (fun e p -> Some (funcBody e p)) soSparkAnnotations us

(*
let getFuncParamTypeFromReferenceToType (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (c:CommonTypes.Codec) (ref:ReferenceToType) =
    let isString =
        match (r.typesMap.[ref]) with
        | Asn1AcnAst.IA5String  _ -> true
        | _                 -> false
    match ref with
    | ReferenceToType path ->
        match path with
        | (MD mdName)::(TA tasName)::(PRM prmName)::[]   -> VALUE prmName
        | (MD mdName)::(TA tasName)::rest   -> 
            let tasId = ReferenceToType ((MD mdName)::(TA tasName)::[])
            let tas = r.typesMap.[tasId]
            let pTas = tas.getParamType  l c
            let rec foo_aux (p:FuncParamType) (rest:GenericFold2.ScopeNode list) idx =
                match rest with
                | []    -> p, idx
                | x::xs  ->
                    let isString = isString && (xs=[])
                    match x with
                    | GenericFold2.SEQ_CHILD chname -> 
                        let newp = p.getSeqChild l chname isString
                        foo_aux newp xs idx
                    | GenericFold2.CH_CHILD chname  -> 
                        let newp = p.getChChild l chname isString
                        foo_aux newp xs idx
                    | GenericFold2.SQF              -> 
                        let i = sprintf "i%d" idx
                        let newp = p.getArrayItem l i isString
                        foo_aux newp xs (idx + 1)
                    | _     ->
                        raise(BugErrorException (sprintf "Invalid reference %s. Broken part is '%s'" (ref.ToString()) (rest |> Seq.StrJoin ".") ))
            foo_aux pTas rest 1 |> fst
        | _     -> raise(BugErrorException (sprintf "Invalid reference %s" (ref.ToString()) ))
            
        
*)        

//return an ASN.1 type
let locateTypeByRefId (r:Asn1AcnAst.AstRoot) (ref:ReferenceToType) =
    0


let locateParameter (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (ref:ReferenceToType) =
    
    0

let handleSingleUpdateDependency (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (vTarget:FuncParamType) d (pSrcRoot : FuncParamType) =
    match d with
    | DepIA5StringSizeDeterminant  decTypeId   -> raise(BugErrorException "Not implemented functionality") 
    | DepOtherSizeDeterminant      decTypeId   -> raise(BugErrorException "Not implemented functionality")
    | DepRefTypeArgument           decTypeId   -> 
        let v = vTarget.getPointer l
        let refTypePath = getAccessFromScopeNodeList decTypeId false l pSrcRoot

        let tasName= 
            match decTypeId.parentTypeId with
            | Some refTypeId    -> 
                refTypeId.tasInfo.Value.tasName
            | _             -> raise(BugErrorException "??")
        let prmName = ToC decTypeId.lastItem
        let updateStatement = sprintf "/*%s -- %s*/" (acn_c.RefTypeArgument1 v tasName prmName (refTypePath.getPointer l)) decTypeId.AsString
        
        //let parameter = 

        updateStatement
    | DepPresenceBool              decTypeId   -> 
        //<v> = (<sSeqPath><sAcc>exist.<sChildName> == 1);
        let v = vTarget.getValue l
        let parDecTypeSeq =
            match decTypeId with
            | ReferenceToType (nodes) -> ReferenceToType (nodes |> List.rev |> List.tail |> List.rev)
        let pDecParSeq = getAccessFromScopeNodeList parDecTypeSeq false l pSrcRoot
        let updateStatement = acn_c.PresenceDependency v (pDecParSeq.p) (pDecParSeq.getAcces l) (ToC decTypeId.lastItem)
        updateStatement
    | DepPresenceInt               decTypeId   -> raise(BugErrorException "Not implemented functionality")
    | DepPresenceStr               decTypeId   -> raise(BugErrorException "Not implemented functionality")
    | DepChoiceDeteterminant       decTypeId   -> raise(BugErrorException "Not implemented functionality")

let getUpdateFunctionUsedInEncoding (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (m:Asn1AcnAst.Asn1Module) (acnChildOrAcnParameterId) (us:State) =
    match deps.acnFields.TryFind acnChildOrAcnParameterId with
    | None  -> 
        //let errMessage = sprintf "No dependency found for ACN child or ACN parameter : %s" acnChildOrAcnParameterId.AsString
        //raise(BugErrorException errMessage)
        None, us
    | Some dps -> 
        match dps with
        | []        -> raise(BugErrorException "unexpected error in createSequenceFunction")
        | d1::[]    -> 
            Some ((fun (vTarget : FuncParamType) (pSrcRoot : FuncParamType)  ->  handleSingleUpdateDependency r deps l m vTarget d1 pSrcRoot)), us
        | _         -> raise(BugErrorException "Not implemented functionality")



let createSequenceFunction (r:Asn1AcnAst.AstRoot) (deps:Asn1AcnAst.AcnInsertedFieldDependencies) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.Sequence) (typeDefinition:TypeDefinitionCommon) (isValidFunc: IsValidFunction option) (children:SeqChildInfo list) (acnPrms:AcnParameter list) (us:State)  =
    (*
        1. all Acn inserted children are declared as local variables in the encoded and decode functions (declaration step)
        2. all Acn inserted children must be initialized appropriatelly in the encoding phase
        3. 
    *)

    // stg macros
    let sequence_presense_optChild              = match l with C -> acn_c.sequence_presense_optChild             | Ada -> acn_c.sequence_presense_optChild          
    let sequence_presense_optChild_pres_bool    = match l with C -> acn_c.sequence_presense_optChild_pres_bool   | Ada -> acn_c.sequence_presense_optChild_pres_bool
    let sequence_presense_optChild_pres_int     = match l with C -> acn_c.sequence_presense_optChild_pres_int    | Ada -> acn_c.sequence_presense_optChild_pres_int 
    let sequence_presense_optChild_pres_str     = match l with C -> acn_c.sequence_presense_optChild_pres_str    | Ada -> acn_c.sequence_presense_optChild_pres_str 
    let sequence_mandatory_child                = match l with C -> acn_c.sequence_mandatory_child               | Ada -> acn_c.sequence_mandatory_child            
    let sequence_optional_child                 = match l with C -> acn_c.sequence_optional_child                | Ada -> acn_c.sequence_optional_child             
    let sequence_optional_always_present        = match l with C -> acn_c.sequence_optional_always_present_child | Ada -> acn_c.sequence_optional_always_present_child
    let sequence_default_child                  = match l with C -> acn_c.sequence_default_child                 | Ada -> acn_c.sequence_default_child              
    //let baseFuncName =  match baseTypeUperFunc  with None -> None | Some baseFunc -> baseFunc.funcName

    let acnChildren = children |>  List.choose(fun x -> match x with AcnChild z -> Some z | Asn1Child _ -> None)
    let asn1Children = children |>  List.choose(fun x -> match x with Asn1Child z -> Some z | AcnChild _ -> None)

    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let acnlocalVariablesCh = acnChildren |>  List.map(fun x -> AcnInsertedChild(x.c_name, x.typeDefinitionBodyWithinSeq))
        
        let acnlocalVariablesPrms = 
            match t.id.tasInfo with
            | Some  _ -> []   //if the encoding type is a top level type (i.e. TAS) then the encodig parameters are transformed into function parameters and not local variables.
            | None    -> acnPrms |>  List.map(fun x -> AcnInsertedChild(x.c_name, x.typeDefinitionBodyWithinSeq))
        let acnlocalVariables = acnlocalVariablesCh @ acnlocalVariablesPrms
        //let acnParams =  r.acnParameters |> List.filter(fun  prm -> prm.ModName ) 

        let printPresenceBit (child:Asn1Child) =
            match child.Optionality with
            | None                       -> None
            | Some Asn1AcnAst.AlwaysAbsent     -> None
            | Some Asn1AcnAst.AlwaysPresent    -> None
            | Some (Asn1AcnAst.Optional opt)   -> 
                match opt.acnPresentWhen with
                | None      -> Some (sequence_presense_optChild p.p (p.getAcces l) child.c_name  errCode.errCodeName codec)
                | Some _    -> None

        let localVariables =
            match asn1Children |> List.choose  printPresenceBit with
            | x::_  when l = C  && codec = CommonTypes.Decode -> (FlagLocalVariable ("presenceBit", None))::acnlocalVariables
            | _        -> acnlocalVariables
                    
        let handleChild (child:SeqChildInfo) =
            //let chFunc = child.chType.getAcnFunction codec
            seq {
                match child with
                | Asn1Child child   -> 
                    let chFunc = child.Type.getAcnFunction codec
                    let childContentResult = 
                        match chFunc with
                        | Some chFunc   -> chFunc.funcBody (p.getSeqChild l child.c_name child.Type.isIA5String)
                        | None          -> None

                    //handle present-when acn property
                    let acnPresenceStatement = 
                        match child.Optionality with
                        | Some (Asn1AcnAst.Optional opt)   -> 
                            match opt.acnPresentWhen with
                            | None    -> None
                            | Some (PresenceWhenBool relPath)    -> 
                                let determinantId = deps.asn12AcnFieldDep.[(DepPresenceBool child.Type.id)]
                                let extField = getAcnDeterminantName determinantId
                                Some(sequence_presense_optChild_pres_bool p.p (p.getAcces l) child.c_name extField codec)
                                (*
                                match lnk.linkType with
                                | Asn1AcnAst.PresenceBool              -> Some(sequence_presense_optChild_pres_bool p.p (p.getAcces l) child.c_name extField codec)
                                | Asn1AcnAst.PresenceInt intVal        -> Some(sequence_presense_optChild_pres_int p.p (p.getAcces l) child.c_name extField intVal codec)
                                | Asn1AcnAst.PresenceStr strval        -> Some(sequence_presense_optChild_pres_str p.p (p.getAcces l) child.c_name extField strval codec)
                                | _                         -> raise(BugErrorException "unexpected error in createSequenceFunction")
                                *)
                        | _                 -> None
                    yield (acnPresenceStatement, [], [])


                    match childContentResult with
                    | None              -> ()
                    | Some childContent ->
                        let childBody = 
                            match child.Optionality with
                            | None                             -> Some (sequence_mandatory_child child.c_name childContent.funcBody codec)
                            | Some Asn1AcnAst.AlwaysAbsent     -> match codec with CommonTypes.Encode -> None                        | CommonTypes.Decode -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent.funcBody codec) 
                            | Some Asn1AcnAst.AlwaysPresent    -> match codec with CommonTypes.Encode -> Some childContent.funcBody  | CommonTypes.Decode -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent.funcBody codec)
                            | Some (Asn1AcnAst.Optional opt)   -> 
                                match opt.defaultValue with
                                | None                   -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent.funcBody codec)
                                | Some v                 -> 
                                    let defInit= child.Type.initFunction.initFuncBody (p.getSeqChild l child.c_name child.Type.isIA5String) (mapValue v).kind
                                    Some (sequence_default_child p.p (p.getAcces l) child.c_name childContent.funcBody defInit codec) 
                        yield (childBody, childContent.localVariables, childContent.errCodes)

                | AcnChild  acnChild    -> 
                    //handle updates
                    //acnChild.c_name
                    let childP = VALUE (getAcnDeterminantName acnChild.id)
                    let pRoot : FuncParamType = t.getParamType l codec  //????
                    match codec with
                    | CommonTypes.Encode ->
                            let updateStatement = 
                                match acnChild.funcUpdateStatement with
                                | Some funcUpdateStatement -> Some (funcUpdateStatement childP pRoot)
                                | None                     -> None
                            yield (updateStatement, [], [])
                    | CommonTypes.Decode -> ()

                    //acn child encode/decode
                    let chFunc = acnChild.funcBody codec
                    let childContentResult = chFunc childP
                    match childContentResult with
                    | None              -> ()
                    | Some childContent ->
                        let childBody = Some (sequence_mandatory_child acnChild.c_name childContent.funcBody codec)
                        yield (childBody, childContent.localVariables, childContent.errCodes)

            } |> Seq.toList

        let presenseBits = asn1Children |> List.choose printPresenceBit
        let childrenStatements0 = children |> List.collect handleChild
        let childrenStatements = childrenStatements0 |> List.choose(fun (s,_,_) -> s)
        let childrenLocalvars = childrenStatements0 |> List.collect(fun (_,s,_) -> s)
        let childrenErrCodes = childrenStatements0 |> List.collect(fun (_,_,s) -> s)
        let seqContent =  (presenseBits@childrenStatements) |> nestChildItems l codec 
        match seqContent with
        | None  -> None
        | Some ret -> Some ({AcnFuncBodyResult.funcBody = ret; errCodes = errCode::childrenErrCodes; localVariables = localVariables@childrenLocalvars})    
        //| Some baseFuncName ->
        //    let funcBodyContent = callBaseTypeFunc l (p.getPointer l) baseFuncName codec
        //    Some ({AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []})
            
    let soSparkAnnotations = 
        match l with
        | C     -> None
        | Ada   -> None
    createPrimitiveFunction r l codec t typeDefinition  isValidFunc  funcBody soSparkAnnotations  us



let createReferenceFunction (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (codec:CommonTypes.Codec) (t:Asn1AcnAst.Asn1Type) (o:Asn1AcnAst.ReferenceType) (typeDefinition:TypeDefinitionCommon) (isValidFunc: IsValidFunction option) (baseType:Asn1Type) (us:State)  =
    baseType.getAcnFunction codec, us


(*
-- 
TEST-CASE DEFINITIONS ::= BEGIN
        
    MyPDU[] {    
         tap[]        
    }
    
    
    TAP3File[]{
         headerType [],  
         sourceData <header.nrCalls> []
    }
    
    HeaderType[]{
        operatorID[],
        nrCalls CallsSize []
    }          
             
    SourceData<INTEGER:nElements2>[]
    {

         calls<nElements>[]
    }
    
    CallsArray<INTEGER:nElements>[size nElements]
    
    Call[]
END  


//αν ένας τύπος έχει base type  έχει παράμετρο 
// περίπτωση 1η inline encoding/decoding

//ENCODING
tap3FileEncode(TAP3File* pVal) {
  
  //encode headerType inline
     encode_operatorID()
	 
	 //update nrCalls
	 // από τον πίνακα AcnLinks βλέπουμε ότι το ACN child  nrCalls 
	 // έχει εξάρτηση τύπου RefTypeArgument ("nElements")
	 // δηλαδή AcnLink = {decType = TAP3File.sourceData;  determinant = TAP3File.header.nrCalls;  linkType  = RefTypeArgument ("nElements")}
	 
	 //1ος τρόπος : με κλήση βοηθητικής συνάρτης
	 pVal->header.nrCalls := Tap3SourceData_getnElementsParam(pVal->sourceData);
	 
	 //2ος τρόπος : με inline κώδικα των βοηθητικών συναρτήσεων
	 // o 2ος τρόπος είναι αυτός που θα προχωρήσουμε.
	 pVal->header.nrCalls = pVal->sourceData.calls.nSize;
	 
	 
	 encode_nrCalls()
  //encode sourceData inline
      //encode calls inline
	     encode_calls();
}

Για κάθε TAS με ACN parameter δημιουργούμε βοηθητικές συναρτήσεις ανά παράμετρο

Π1
integer SourceData_getnElementsParam(SourceData pVal) {
	return CallsArray_getnElements2Param(pVal->calls)
}

Π2
integer CallsArray_getnElements2Param(CallsArray pVal) {
   return pVal->nSize;
}

καθώς και (για την περίπτωση των inline encodings) lamda functions 
getParmFuncBody -> string -> string -> string -> string 	// P , sAcc, param name, expression code with the value

Π_nElements(p  = pVal->sourceData, sAcc ='.') ->  
	Prokeitai gia RefTypeArgument dependency ara tha kalesoume thn Π_nElements2 όπου στο p argument θα κάνουμε append to 'calls'
	Δηλαδή το αποτέλεσμα είναι
	Π_nElements2(p = p+ 'calls', sAcc ='.')

Π_nElements2(p = pVal-sourceData.nCalls, sAcc = '.') -> 
	Prokeitai gia size determinant ara to expression tha einai:
	  <p><sAcc>nSize




//DECODING
// δηλώνουμε την παράμετρο ως τοπικές μεταβλητές
// όλες τις ACN parameters. Για να μην υπάρχει naming conflict
// βάζουμε μπροστά το long path του εκάστοτε τύπου
// αφού αφαιρέσουμε το tas name της ρίζας.
// Δηλαδή δεν έχει νόημα να τις βαφτίζουμε TAP3File_sourceData_nElements αλλά sourceData_nElements
tap3FileDecode(TAP3File* pVal) {
   integer sourceData_nElements;
   integer sourceData_calls_nElements;
   
   // decode header inline
     decode_operatorID();
	 decode_nrCalls();
   // decode sourceData inline
   // εφοσον κάνουμε inline decoding του sourceData (δηλαδή δεν καλούμε την base encoding function)
   // θα πρέπει οι ACN parameters να αρχικοποιηθόύν
   // Θα ψάξουμε στον πίνακα acnLinks να βρούμε μια εγγραφή όπου το id του decoding type (στην προκειμένη περίπτωση του sourceData)
   // να είναι ίσο TAP3File.SourceData, να είναι τύπου RefTypeArgument και να ταυτίζεται το όνομα της παραμέτρου με το value του RefTypeArgument
   // δηλαδή AcnLink = {decType = TAP3File.SourceData;  determinant = TAP3File.header.nrCalls;  linkType  = RefTypeArgument ("nElements")}
      sourceData_nElements := pVal->header.nrCalls;
	 //decode calls
	 // Ομοίως για το inline encoding του CallsArray θα πρέπει πρώτα να αρχικοποιηθούν οι acn parameters
	 // άρα θα πρέπει για κάθε παραμετρο του TAP3File.sourceData.calls να βρούμε εγγραφή 
	 // με decoding type id = TAP3File.sourceData.calls και linkType  = RefTypeArgument (όνομα παραμέτρου)
   // δηλαδή AcnLink = {decType = TAP3File.SourceData.calls;  determinant = TAP3File.sourceData.nElements;  linkType  = RefTypeArgument ("nElements")}
     // στην προκειμένη περίπτωση το determinant έχει id -> MD(MyMODULE)::TA(TAP3File)::SEQ_CHILD(sourceData)::PRM(nElements)
	 
	 sourceData_calls_nElements = sourceData_nElements;
	 //decode calls sequence using CallsArray_nElements as length determinant
	    decode_calls();
 }
 
 Συμπέραμα --> 
   όλοι οι Asn1Types μπορεί να έχουν ACN parameters και όχι μόνο τα Type Assignments.
   




*)