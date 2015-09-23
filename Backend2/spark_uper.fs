module spark_uper
open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils



let rec EmitInternalItem_min_max (t:Asn1Type) (sTasName:string) (path:list<string>)  (m:Asn1Module) (r:AstRoot)  codec =
    let sTasName = GetTasCName (path |> Seq.nth 1) r.TypePrefix
    let p = GetAccessFld path (Same t) r 
    match t.Kind with
    | SequenceOf(_) | OctetString | BitString->
        let index = "I1"
        let sCount = su.bit_oct_sqof_length p
        match t.Kind with
        | SequenceOf(inItem)     -> 
            let intItem = EmitTypeBody inItem sTasName (path@["#"], None) m r codec
            let nMax = uperGetMaxSizeInBitsAsInt inItem.Kind inItem.Constraints inItem.Location r
            let nMin = 0I
            intItem,nMin,nMax
        | OctetString            -> su.InternalItem_oct_str p index codec ,8I,8I 
        | BitString              -> su.InternalItem_bit_str p index codec ,1I,1I 
        | _      -> raise(BugErrorException "")
    | IA5String | NumericString -> 
        let index = "I1"
        let sCount = su.str_length p
        let alphaCons = t.Constraints |> List.filter(fun x -> match x with AlphabetContraint(_) -> true |_ -> false)
        match (Seq.isEmpty alphaCons) with
        | true  -> su.InternalItem_string_no_alpha p index codec, 7I, 7I
        | false -> 
            let alphaSet = GetTypeUperRangeFrom (t.Kind, t.Constraints, r)
            let nCharIndexSize = (GetNumberOfBitsForNonNegativeInteger (BigInteger (alphaSet.Length - 1)))
            let nCharIndexMax = BigInteger alphaSet.Length-1I
            su.InternalItem_string_with_alpha p sTasName index nCharIndexSize nCharIndexMax codec,nCharIndexSize,nCharIndexSize
    | _     ->raise(BugErrorException "")

and  EmitTypeBody (t:Asn1Type) (sTasName:string) (path:list<string>, pName:string option)  (m:Asn1Module) (r:AstRoot)  codec =
    //let sTasName = GetTasCName (path |> Seq.nth 1) r.TypePrefix
    let p = match pName with
            | Some(nm)  -> nm
            | None      -> GetAccessFld path (Same t) r 
    let handleSizeableType uPERRange s1 s2 s3 =
        match uPERRange with
        | Concrete(a,b) when b<65536I && a=b   -> s1 a
        | Concrete(a,b) when b<65536I && a<>b  -> s2 a b
        | Concrete(a,b)                        -> s3 a b
        | NegInf(_)         -> raise (BugErrorException("Negative size"))
        | PosInf(_)         -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Full              -> raise (BugErrorException("All sizeable types must be constraint, otherwise max size is infinite"))
        | Empty             -> raise (BugErrorException("I do not known how this is handled"))      

    let errCode = 
        match (GetTypeConstraintsErrorCode t.Constraints path r) with
        | None  -> "0"
        | Some(errCodeName) ->    errCodeName
    match t.Kind with
    | Integer   -> 
        let IntBod cons =
            match (GetTypeUperRange t.Kind cons r) with
            | Concrete(min, max)      -> su.IntFullyConstraint p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode codec
            | PosInf(a)               -> su.IntSemiConstraint p a  errCode codec
            | NegInf(max)             -> su.IntUnconstraintMax p max errCode codec
            | Full                    -> su.IntUnconstraint p errCode codec
            | Empty                   -> raise(BugErrorException "")
        let rootCons = t.Constraints |> List.choose(fun x -> match x with RootConstraint(a) |RootConstraint2(a,_) -> Some(x) |_ -> None) 
        let getValueByConstraint c = 
            match (GetUperRange c r) with
            | Concrete(a, _) | PosInf(a)  | NegInf(a) -> a
            | Full                    -> 0I
            | Empty                   -> raise(BugErrorException "")

        match rootCons with
        | []                            -> IntBod t.Constraints
        | (RootConstraint a)::rest      -> 
            let cc =  spark_validate.PrintTypeContraint (Same t) path a "" [] m r 
            su.IntRootExt p (getValueByConstraint a) cc (IntBod [a]) errCode codec 
        | (RootConstraint2(a,_))::rest  -> 
            let cc =  spark_validate.PrintTypeContraint (Same t) path a "" [] m r 
            su.IntRootExt2 p (getValueByConstraint a) cc (IntBod [a]) errCode codec 
        | _                             -> raise(BugErrorException "")
    | Boolean -> su.Boolean p errCode codec
    | Real    -> su.Real p errCode codec
    | ReferenceType(modName,tasName, _)    ->
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        match modName.Value = m.Name.Value with
        | true  -> su.ReferenceType1 p tsName (UperEncodeFuncRequiresResult t r ) codec 
        | false -> su.ReferenceType2 p (ToC modName.Value) tsName (UperEncodeFuncRequiresResult t r ) codec
        
    | Sequence(children)    ->
        let asn1Children = children |> List.filter(fun x -> not x.AcnInsertedField)
        let d1 = asn1Children |> List.filter(fun c -> c.Optionality.IsSome) |> List.map(fun c -> (0,c))
        let d2 = asn1Children |> List.map(fun c -> (1,c))
        let decodedParts = d1@d2
        let bRequiresInit = match asn1Children with
                            | []    -> true
                            | x::[] -> x.Optionality.IsSome
                            | _     -> true

        let printChild (k:int, c:ChildInfo) requiredBitsSoFar sNestedContent = 
            let content, bRequiresResultCheck = 
                match k with
                | 0     -> su.Sequence_optChild p (c.CName ProgrammingLanguage.Spark) errCode codec, false
                | _     -> 
                    let bHasDef= match c.Optionality with Some(Default(v)) ->true |_  ->false
                    let sChildContent = EmitTypeBody c.Type sTasName (path@[c.Name.Value], None) m r codec 
                    let bRequiresResultCheck = UperEncodeFuncRequiresResult c.Type r
                    let content = su.Sequence_Child p (c.CName ProgrammingLanguage.Spark) c.Optionality.IsSome sChildContent bHasDef codec
                    content, bRequiresResultCheck
            su.JoinItems sTasName content sNestedContent requiredBitsSoFar bRequiresResultCheck codec

        let  printChildren (lst:list<int*ChildInfo>)= 
            let requiredBitsForChild (k:int, c:ChildInfo) =
                match k with
                | 0     -> 1I
                | _     -> uperGetMaxSizeInBitsAsInt c.Type.Kind c.Type.Constraints c.Type.Location r
                
            let rec printChildrenAux (lst:list<int*ChildInfo>) requiredBitsSoFar= 
                match lst with
                    |[]     -> null
                    |x::xs  -> 
                        let requiredBitsForThis = requiredBitsForChild x
                        let newRequiredBitsSoFar = requiredBitsForThis + requiredBitsSoFar
                        printChild x newRequiredBitsSoFar (printChildrenAux xs newRequiredBitsSoFar)
            match lst with
            | []    -> []
            | _     -> [printChildrenAux lst 0I]
        su.Sequence p (printChildren decodedParts) sTasName bRequiresInit codec 
    | SequenceOf(_) | OctetString | BitString->
        let index = "I1"
        
        let encInternalItem, min, max = EmitInternalItem_min_max t sTasName path m r codec
        let s1 a  = su.oct_sqf_FixedSize p index encInternalItem a sTasName min max 0I codec 
        let s2 a b=  su.oct_sqf_VarSize sTasName p index encInternalItem a b (GetNumberOfBitsForNonNegativeInteger (b-a)) min max 0I codec 
        let s3 a b=  
            let sCount = if a=b then b.ToString() else su.bit_oct_sqof_length p
            su.Fragmentation_sqf sCount encInternalItem max  b (b<>a) sTasName codec
        handleSizeableType (GetTypeUperRange t.Kind t.Constraints r) s1 s2 s3
    | Enumerated(items) -> 
        let nMin = 0I
        let nMax = BigInteger(Seq.length items) - 1I
        let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
        let arrItems = 
            match items |> Seq.forall(fun x -> x._value.IsSome) with
            | true  -> items |> Seq.sortBy(fun x -> (Ast.GetValueAsInt x._value.Value r)) |> Seq.mapi(fun i item -> su.Enumerated_item p (item.CEnumName r Spark) (BigInteger i) codec)
            | false -> items |> Seq.mapi(fun i item -> su.Enumerated_item p (item.CEnumName r Spark) (BigInteger i) codec)
        su.Enumerated p sTasName arrItems nMin nMax nBits errCode codec
    | IA5String | NumericString -> 
        let index = "I1"
        let alphaCons = t.Constraints |> List.filter(fun x -> match x with AlphabetContraint(_) -> true |_ -> false)
        let encInternalItem, min, max = EmitInternalItem_min_max t sTasName path m r codec
        let s1 a  = su.str_FixedSize p sTasName index encInternalItem a min max 0I codec 
        let s2 a b=  su.str_VarSize p sTasName index encInternalItem a b (GetNumberOfBitsForNonNegativeInteger (b-a)) min max 0I codec 
        let s3 a b=  
            let sCount = if a=b then b.ToString() else su.str_length p
            su.Fragmentation_sqf sCount encInternalItem max  b false sTasName codec
        handleSizeableType (GetTypeUperRange t.Kind t.Constraints r) s1 s2 s3
    | NullType                  -> su.Null p codec
    | Choice(children)  -> 
        let nMin = 0I
        let nMax = BigInteger(Seq.length children) - 1I
        let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
        let printChild (i:int) (c:ChildInfo) =
            //let newPath = match codec with Encode -> (path@[c.Name.Value]) | Decode -> ([c.CName+"_tmp"])
            let pName = match codec with Encode -> None | Decode -> Some((c.CName ProgrammingLanguage.Spark) + "_tmp")
            let newPath = path@[c.Name.Value]
            let sChildContent = EmitTypeBody c.Type sTasName (newPath, pName) m r codec 
            su.ChoiceChild sTasName (c.CName ProgrammingLanguage.Spark) sChildContent (BigInteger i) nBits  (c.CName_Present Spark) codec
        let arrChildren = children |> Seq.mapi printChild
        su.Choice sTasName arrChildren nMax nBits codec



let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) codec =
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
        match t.Kind with
        | SequenceOf(_) | OctetString | BitString | IA5String | NumericString-> 
            let newState =
                match (GetTypeUperRange t.Kind t.Constraints r) with
                | Concrete(a,b) when b<65536I && a=b   -> (SEQUENCE_OF_INDEX (1,true))::state
                | Concrete(a,b) when b<65536I && a<>b  -> 
                    let s0 = (SEQUENCE_OF_INDEX (1,true))::state
                    match t.Kind with 
                    | SequenceOf(_) | OctetString | BitString -> if codec = Decode then LENGTH::s0 else s0
                    | IA5String | NumericString               -> LENGTH::s0
                    | _                                       -> raise (BugErrorException(""))
                | Concrete(a,b)     -> 
                    let s0 = NCOUNT::CUR_BLOCK_SIZE::CUR_ITEM::state
                    let s1 = match t.Kind with
                                   | SequenceOf(_) | OctetString | BitString  -> if a<>b && codec = Decode then  LENGTH::s0 else s0
                                   | _                                        -> s0
                    if codec = Decode then (SEQUENCE_OF_INDEX (1,false))::LEN2::s1 else s1
                | _                 -> raise (BugErrorException("Unsupported configuration"))
            match t.Kind with
            |IA5String | NumericString -> CHAR_VAL::newState
            |_                         -> newState
        | Integer   when codec = Decode     ->
            let rootCons = t.Constraints |> Seq.filter(fun x -> match x with RootConstraint(a) |RootConstraint2(a,_) -> true |_ -> false) 
            match (Seq.isEmpty rootCons) with
            | true  -> state
            | false -> EXTENSION_BIT::state
        | Enumerated(_)     -> ENUM_IDX::state
        | Choice(children) when codec = Decode -> 
            let handleChild (c:ChildInfo) =
                let typeDecl,_ = spark_spec.PrintType c.Type [m.Name.Value; tas.Name.Value; c.Name.Value] (Some tas.Type) (TypeAssignment tas,m,r) {spark_spec.State.nErrorCode = 0}
                CHOICE_TMP_FLD(c.CName ProgrammingLanguage.Spark, typeDecl)
            let cldnd = children |> List.map handleChild
            CHOICE_IDX::(cldnd@state)
        | _             -> state

    let lvs = VisitType t [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []
    let emitLocalVariable = function
        | SEQUENCE_OF_INDEX(i, bHasInit) -> sc.Emit_local_variable_SQF_Index (BigInteger i) bHasInit
        | EXTENSION_BIT     -> su.Declare_ExtensionBit()
        | LENGTH            -> su.Declare_Length()
        | ENUM_IDX          -> su.Declare_EnumIndex()
        | CHOICE_IDX        -> su.Declare_ChoiceIndex()
        | CHOICE_TMP_FLD(fldName, fldType)  -> su.ChoiceChild_tmpVar fldName fldType
        | CHAR_VAL          -> su.Declare_CharValue()
        | NCOUNT            -> su.Declare_nCount()
        | CUR_BLOCK_SIZE    -> su.Declare_curBlockSize()
        | CUR_ITEM          -> su.Declare_curItem()
        | LEN2              -> su.Declare_len2()
        | REF_TYPE_PARAM(_) -> raise(BugErrorException(""))

    lvs |> Seq.map emitLocalVariable


let EmitTypeAss (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  codec = 
    let sTasName = tas.GetCName r.TypePrefix
    let sTypeBody = EmitTypeBody tas.Type sTasName ([m.Name.Value; tas.Name.Value], None) m r codec
    let localVars = CollectLocalVars tas.Type tas m r codec
    let kDependedsOnValue = SparkDeps.KDependsOnValue_uper tas.Type r
    let kIndexDependsOnData = SparkDeps.KIndexDependsOnData_uper tas.Type r
    let decodingResultDependsOnData = SparkDeps.DecodingResultDependsOnData_uper tas.Type r
    let annotations = 
        (ss.UPER_annotations sTasName kDependedsOnValue (UperEncodeFuncRequiresResult tas.Type r ) decodingResultDependsOnData kIndexDependsOnData codec).Split('\r','\n') 
        |> Seq.filter(fun s -> s<>"") |> Seq.map(fun s -> "-"+s)
        
    let normalCase () = 
        su.Tas sTasName (UperEncodeFuncRequiresResult tas.Type r ) localVars sTypeBody kDependedsOnValue decodingResultDependsOnData kIndexDependsOnData annotations codec
    match tas.Type.Kind with
    | SequenceOf(_) | OctetString | BitString | IA5String | NumericString   ->
        match (GetTypeUperRange tas.Type.Kind tas.Type.Constraints r) with
        | Concrete(_,b) when b>=65536I -> 
            let encInternalItem, min, max = EmitInternalItem_min_max tas.Type sTasName [m.Name.Value; tas.Name.Value] m r codec
            su.Tas_fragmentation sTasName localVars sTypeBody kDependedsOnValue decodingResultDependsOnData kIndexDependsOnData max encInternalItem b (UperEncodeFuncRequiresResult tas.Type r ) codec
        | _                            -> normalCase ()
    | _                                -> normalCase ()
    



