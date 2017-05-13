module DAstACN

open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst

let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (tasInfo:BAst.TypeAssignmentInfo option)  =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_ACN" + codec.suffix))

let getTypeDefinitionName (tasInfo:BAst.TypeAssignmentInfo option) (typeDefinition:TypeDefinitionCommon) =
    match tasInfo with
    | Some _                -> typeDefinition.name
    | None (*inner type*)   -> typeDefinition.typeDefinitionBodyWithinSeq

let callBaseTypeFunc l = match l with C -> uper_c.call_base_type_func | Ada -> uper_a.call_base_type_func

let getAcnDeterminantName (id : ReferenceToType) =
    let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
    ToC2(longName.Replace("#","elem"))


let createPrimitiveFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Asn1Type) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : AcnFunction option) (isValidFunc: IsValidFunction option)  (funcBody:ErroCode->FuncParamType -> (AcnFuncBodyResult option)) soSparkAnnotations (us:State)  =
    let funcName            = getFuncName r l codec o.tasInfo
    let errCodeName         = ToC ("ERR_ACN" + (codec.suffix.ToUpper()) + "_" + ((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
    let errCodeValue        = us.currErrCode
    let errCode             = {ErroCode.errCodeName = errCodeName; errCodeValue = errCodeValue}

    let EmitTypeAssignment_primitive = match l with C -> uper_c.EmitTypeAssignment_primitive    | Ada -> uper_a.EmitTypeAssignment
    let EmitTypeAssignment_primitive_def = match l with C -> uper_c.EmitTypeAssignment_primitive_def    | Ada -> uper_a.EmitTypeAssignment_def
    let EmitTypeAssignment_def_err_code  = match l with C -> uper_c.EmitTypeAssignment_def_err_code    | Ada -> uper_a.EmitTypeAssignment_def_err_code

    let funcBody = (funcBody errCode)
    let p = o.getParamType l codec
    let topLevAcc = p.getAcces l
    let varName = p.p
    let sStar = p.getStar l
    let isValidFuncName = match isValidFunc with None -> None | Some f -> f.funcName
    let sInitilialExp = ""
    let  func, funcDef  = 
            match funcName  with
            | None              -> None, None
            | Some funcName     -> 
                let content = funcBody p  
                match content with 
                | None          -> None, None
                | Some bodyResult  ->
                    let lvars = bodyResult.localVariables |> List.map(fun (lv:LocalVariable) -> lv.GetDeclaration l) |> Seq.distinct
                    let func = Some(EmitTypeAssignment_primitive varName sStar funcName isValidFuncName  typeDefinition.name lvars  bodyResult.funcBody soSparkAnnotations sInitilialExp codec)
                
                    let errCodes = bodyResult.errCodes
                    let errCodStr = errCodes |> List.map(fun x -> (EmitTypeAssignment_def_err_code x.errCodeName) (BigInteger x.errCodeValue))
                    let funcDef = Some(EmitTypeAssignment_primitive_def varName sStar funcName  typeDefinition.name errCodStr (o.uperMaxSizeInBits = 0) (BigInteger (ceil ((double o.uperMaxSizeInBits)/8.0))) (BigInteger o.uperMaxSizeInBits) codec)
                    func, funcDef


    let ret = 
        {
            AcnFunction.funcName      = funcName
            func                       = func 
            funcDef                    = funcDef
            funcBody                   = funcBody
        }
    ret, {us with currErrCode = us.currErrCode + 1}

let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : AcnFunction option) (isValidFunc: IsValidFunction option) (uperFunc: UPerFunction) (us:State)  =

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

    let funcBody (errCode:ErroCode) (p:FuncParamType)        = 
        let pp = match codec with Ast.Encode -> p.getValue l | Ast.Decode -> p.getPointer l
        let funcBodyContent = 
            match o.acnEncodingClass with
            |CAst.Integer_uPER                                       ->  uperFunc.funcBody p |> Option.map(fun x -> x.funcBody)
            |CAst.PositiveInteger_ConstSize_8                        ->  Some(PositiveInteger_ConstSize_8 pp None codec)
            |CAst.PositiveInteger_ConstSize_big_endian_16            ->  Some(PositiveInteger_ConstSize_big_endian_16 pp None codec)
            |CAst.PositiveInteger_ConstSize_little_endian_16         ->  Some(PositiveInteger_ConstSize_little_endian_16 pp None codec)
            |CAst.PositiveInteger_ConstSize_big_endian_32            ->  Some(PositiveInteger_ConstSize_big_endian_32 pp None codec)
            |CAst.PositiveInteger_ConstSize_little_endian_32         ->  Some(PositiveInteger_ConstSize_little_endian_32 pp None codec)
            |CAst.PositiveInteger_ConstSize_big_endian_64            ->  Some(PositiveInteger_ConstSize_big_endian_64 pp None codec)
            |CAst.PositiveInteger_ConstSize_little_endian_64         ->  Some(PositiveInteger_ConstSize_little_endian_64 pp None codec)
            |CAst.PositiveInteger_ConstSize bitSize                  ->  Some(PositiveInteger_ConstSize pp (BigInteger bitSize) None codec)
            |CAst.TwosComplement_ConstSize_8                         ->  Some(TwosComplement_ConstSize_8 pp None codec)
            |CAst.TwosComplement_ConstSize_big_endian_16             ->  Some(TwosComplement_ConstSize_big_endian_16 pp None codec)
            |CAst.TwosComplement_ConstSize_little_endian_16          ->  Some(TwosComplement_ConstSize_little_endian_16 pp None codec)
            |CAst.TwosComplement_ConstSize_big_endian_32             ->  Some(TwosComplement_ConstSize_big_endian_32 pp None codec)
            |CAst.TwosComplement_ConstSize_little_endian_32          ->  Some(TwosComplement_ConstSize_little_endian_32 pp None codec)
            |CAst.TwosComplement_ConstSize_big_endian_64             ->  Some(TwosComplement_ConstSize_big_endian_64 pp None codec)
            |CAst.TwosComplement_ConstSize_little_endian_64          ->  Some(TwosComplement_ConstSize_little_endian_64 pp None codec)
            |CAst.TwosComplement_ConstSize bitSize                   ->  Some(TwosComplement_ConstSize pp (BigInteger bitSize) None codec)
            |CAst.ASCII_ConstSize size                               ->  Some(ASCII_ConstSize pp ((BigInteger size)/8I) None codec)
            |CAst.ASCII_VarSize_NullTerminated nullByte              ->  Some(ASCII_VarSize_NullTerminated pp None codec)
            |CAst.ASCII_UINT_ConstSize size                          ->  Some(ASCII_UINT_ConstSize pp ((BigInteger size)/8I) None codec)
            |CAst.ASCII_UINT_VarSize_NullTerminated nullByte         ->  Some(ASCII_UINT_VarSize_NullTerminated pp  None codec)
            |CAst.BCD_ConstSize size                                 ->  Some(BCD_ConstSize pp ((BigInteger size)/4I) None codec)
            |CAst.BCD_VarSize_NullTerminated nullByte                ->  Some(BCD_VarSize_NullTerminated pp None codec)
        match funcBodyContent with
        | None -> None
        | Some funcBodyContent -> Some ({AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []})
    
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Integer o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> funcBody e p) soSparkAnnotations us





let nestChildItems (l:ProgrammingLanguage) (codec:Ast.Codec) children = 
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



let createBooleanFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : AcnFunction option) (isValidFunc: IsValidFunction option) (us:State)  =
    // todo use BolleanAcnEncodingClass

    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        let pp = match codec with Ast.Encode -> p.getValue l | Ast.Decode -> p.getPointer l
        let Boolean         = match l with C -> uper_c.Boolean          | Ada -> uper_a.Boolean
        let funcBodyContent = 
            Boolean pp errCode.errCodeName codec
        {AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []}    
    let soSparkAnnotations = None
    createPrimitiveFunction r l codec (CAst.Boolean o) typeDefinition baseTypeUperFunc  isValidFunc  (fun e p -> Some (funcBody e p)) soSparkAnnotations us


let createSequenceFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (codec:Ast.Codec) (o:CAst.Sequence) (typeDefinition:TypeDefinitionCommon) (baseTypeUperFunc : AcnFunction option) (isValidFunc: IsValidFunction option) (children:SeqChildInfo list) (us:State)  =
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

    let baseFuncName =  match baseTypeUperFunc  with None -> None | Some baseFunc -> baseFunc.funcName

    let funcBody (errCode:ErroCode) (p:FuncParamType) = 
        match baseFuncName with
        | None ->
            let acnlocalVariables =
                children |> List.filter(fun x -> x.acnInsertetField) |> List.map(fun x -> AcnInsertedChild((getAcnDeterminantName x.chType.id), x.chType.typeDefinition.typeDefinitionBodyWithinSeq))
            let localVariables =
                match children |> Seq.exists(fun x -> x.optionality.IsSome) with
                | true  when l = C  && codec = Ast.Decode -> (FlagLocalVariable ("presenceBit", None))::acnlocalVariables
                | _                                       -> acnlocalVariables
            let printPresenceBit (child:SeqChildInfo) =
                match child.optionality with
                | None                       -> None
                | Some CAst.AlwaysAbsent     -> None
                | Some CAst.AlwaysPresent    -> None
                | Some (CAst.Optional opt)   -> 
                    match opt.ancEncodingClass with
                    | CAst.OptionLikeUper    -> Some (sequence_presense_optChild p.p (p.getAcces l) child.c_name  errCode.errCodeName codec)
                    | CAst.OptionExtField    -> None
                        (*
                            *)
                    
            let handleChild (child:SeqChildInfo) =
                let chFunc = child.chType.getUperFunction codec
                match chFunc with
                | None  -> []
                | Some chFunc ->
                    let childContentResult = 
                        match child.acnInsertetField with
                        | false -> chFunc.funcBody (p.getSeqChild l child.c_name child.chType.isIA5String)
                        | true  -> chFunc.funcBody (VALUE (getAcnDeterminantName child.chType.id))
                    seq {
                        match childContentResult with
                        | None              -> ()
                        | Some childContent ->
                            let acnPresenceStatement = 
                                match child.optionality with
                                | Some (CAst.Optional opt)   -> 
                                    match opt.ancEncodingClass with
                                    | CAst.OptionLikeUper    -> None
                                    | CAst.OptionExtField    -> 
                                        match r.acnLinks |> Seq.tryFind(fun l -> l.decType.id = child.chType.id) with
                                        | None  -> raise(BugErrorException "unexpected error in createSequenceFunction")
                                        | Some lnk  ->
                                            let extField = getAcnDeterminantName lnk.determinant
                                            match lnk.linkType with
                                            | CAst.PresenceBool              -> Some(sequence_presense_optChild_pres_bool p.p (p.getAcces l) child.c_name extField codec)
                                            | CAst.PresenceInt intVal        -> Some(sequence_presense_optChild_pres_int p.p (p.getAcces l) child.c_name extField intVal codec)
                                            | CAst.PresenceStr strval        -> Some(sequence_presense_optChild_pres_str p.p (p.getAcces l) child.c_name extField strval codec)
                                            | _                         -> raise(BugErrorException "unexpected error in createSequenceFunction")
                                | _                 -> None
                            yield (acnPresenceStatement, [], [])

                            let childBody = 
                                match child.optionality with
                                | None                       -> Some (sequence_mandatory_child child.c_name childContent.funcBody codec)
                                | Some CAst.AlwaysAbsent     -> match codec with Ast.Encode -> None                        | Ast.Decode -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent.funcBody codec) 
                                | Some CAst.AlwaysPresent    -> match codec with Ast.Encode -> Some childContent.funcBody  | Ast.Decode -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent.funcBody codec)
                                | Some (CAst.Optional opt)   -> 
                                    match opt.defaultValue with
                                    | None                   -> Some (sequence_optional_child p.p (p.getAcces l) child.c_name childContent.funcBody codec)
                                    | Some v                 -> 
                                        let defInit= child.chType.initFunction.initFuncBody (p.getSeqChild l child.c_name child.chType.isIA5String) v
                                        Some (sequence_default_child p.p (p.getAcces l) child.c_name childContent.funcBody defInit codec) 
                            yield (childBody, childContent.localVariables, childContent.errCodes)
                    } |> Seq.toList
            
            let presenseBits = children |> List.choose printPresenceBit
            let childrenStatements0 = children |> List.collect handleChild
            let childrenStatements = childrenStatements0 |> List.choose(fun (s,_,_) -> s)
            let childrenLocalvars = childrenStatements0 |> List.collect(fun (_,s,_) -> s)
            let childrenErrCodes = childrenStatements0 |> List.collect(fun (_,_,s) -> s)
            let seqContent =  (presenseBits@childrenStatements) |> nestChildItems l codec 
            match seqContent with
            | None  -> None
            | Some ret -> Some ({AcnFuncBodyResult.funcBody = ret; errCodes = errCode::childrenErrCodes; localVariables = localVariables@childrenLocalvars})    
        | Some baseFuncName ->
            let funcBodyContent = callBaseTypeFunc l (p.getPointer l) baseFuncName codec
            Some ({AcnFuncBodyResult.funcBody = funcBodyContent; errCodes = [errCode]; localVariables = []})
            
    let soSparkAnnotations = 
        match l with
        | C     -> None
        | Ada   -> None
    createPrimitiveFunction r l codec (CAst.Sequence o) typeDefinition baseTypeUperFunc  isValidFunc  funcBody soSparkAnnotations  us
