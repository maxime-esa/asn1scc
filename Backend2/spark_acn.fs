module spark_acn

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils


(*
Main update function.
Handles only one update
returns the update statement and a flag indication if result check is required
*)
let UpdateDeterminant determinantPath (kind:AcnTypes.LongReferenceKind, refs:seq<AcnTypes.LongReferenceResolved>) (sTasName:string) (m:Asn1Module)(r:AstRoot) (acn:AcnTypes.AcnAstResolved)=
    let ref = Seq.head refs
    let otherType = GetTypeByPoint ref.decType r acn
    let otherTypePath = GetPointAccessPath ref.decType r acn
    let determinant = GetTypeByPoint ref.determinant r acn
    let actOtherType = GetActualType otherType r
    let actDeterminant = GetActualType determinant r
    match kind with
    | AcnTypes.SizeDeterminant     -> 
        let sCount = GetCount otherType otherTypePath r
        false, sa.SizeDependency determinantPath sCount
    | AcnTypes.ChoiceDeteterminant ->
        let printItem (ch:ChildInfo) (en:NamedItem) =
            sa.ChoiceDependencyEnum_Item determinantPath (ch.CName_Present Spark) (en.CEnumName r Spark)
        match actOtherType.Kind, actDeterminant.Kind with
        | Choice(children), Enumerated(enms)    ->
            let sortedEnms = 
                enms |> 
                List.sortBy (
                    fun en -> 
                        children |> Seq.findIndex (fun ch -> ch.Name = en.Name)
                )
            let arrsChEnumItems = Seq.map2 printItem children sortedEnms
            false, sa.ChoiceDependencyEnum sTasName arrsChEnumItems
        | _ -> raise(BugErrorException(""))
    | AcnTypes.PresenceBool        ->
        let parentPoint = AcnTypes.Point.TypePoint(ref.decType.AbsPath |> List.rev |> List.tail |> List.rev)
        let parentPath = GetPointAccessPath parentPoint (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let childName = ref.decType.AbsPath |> List.rev |> List.head
        false, sa.PresenceDependency determinantPath parentPath (ToC childName)
    | AcnTypes.PresenceInt(_)  ->
        let parentPoint = AcnTypes.Point.TypePoint(ref.decType.AbsPath |> List.rev |> List.tail |> List.rev)
        let parentPath = GetPointAccessPath parentPoint (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let printItem (rf:AcnTypes.LongReferenceResolved) =
            match rf.Kind with
            | AcnTypes.PresenceInt(intVal)  ->
                let childName = ToC (rf.decType.AbsPath |> List.rev |> List.head)
                sa.ChoiceDependencyIntPres_child determinantPath childName (AcnTypes.EvaluateConstant acn.Constants intVal) (childName + "_PRESENT")
            | _                             -> raise(BugErrorException "")
        let children = refs |> Seq.map printItem
        false, sa.ChoiceDependencyPres sTasName children
    | AcnTypes.PresenceStr(_)  ->
        let parentPoint = AcnTypes.Point.TypePoint(ref.decType.AbsPath |> List.rev |> List.tail |> List.rev)
        let parentPath = GetPointAccessPath parentPoint (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let printItem (rf:AcnTypes.LongReferenceResolved) =
            match rf.Kind with
            | AcnTypes.PresenceStr(sVal)  ->
                let childName = ToC (rf.decType.AbsPath |> List.rev |> List.head)
                sa.ChoiceDependencyStrPres_child determinantPath childName sVal (childName + "_PRESENT")
            | _                             -> raise(BugErrorException "")
        let children = refs |> Seq.map printItem
        false, sa.ChoiceDependencyPres sTasName children
    | AcnTypes.RefTypeArgument(prmName)                          -> 
        let newModule, newTas = match otherType.Kind with
                                | ReferenceType(md,ts, _) -> 
                                    let m1 = r.Modules |> Seq.find(fun x -> x.Name.Value = md.Value)
                                    let t1 = m1.TypeAssignments |> Seq.find(fun x -> x.Name.Value = ts.Value)
                                    m1, t1
                                | _                    -> raise(BugErrorException "")
        match acn.Parameters |> Seq.tryFind(fun p -> p.ModName = newModule.Name.Value && p.TasName = newTas.Name.Value && p.Name = prmName) with
        | None  -> raise(BugErrorException "")
        | Some(actPrm)  ->
            let bHasSuccess = acn_backend_logic.Update_param_function_requires_result prmName newTas newModule r acn
            let sNewTasName = newTas.GetCName r.TypePrefix
            match newModule.Name.Value = m.Name.Value with
            | true ->  bHasSuccess, sa.RefTypeArgument1 determinantPath sNewTasName prmName otherTypePath bHasSuccess
            | false -> bHasSuccess, sa.RefTypeArgument2 determinantPath (ToC newModule.Name.Value) sNewTasName prmName otherTypePath bHasSuccess


(*
Handle Encoding Updates for a Sequence child
*)
let HandleChildUpdate (ch:ChildInfo) (parentPath:list<string>) (sTasName:string) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let chPath = parentPath@[ch.Name.Value]
    let childPoint =  AcnTypes.Point.TypePoint(chPath)
    let childDependencies = acn_backend_logic.GroupReferences childPoint r acn
    let chAccessFld = GetAccessFld2 chPath r
    let GetTmpVar i = ToC ((chPath.Tail.StrJoin "_") + "_" + i.ToString())
    let tmpVar0 = GetTmpVar 0
    let HandleChildReference refIndex (kind:AcnTypes.LongReferenceKind, refs:seq<AcnTypes.LongReferenceResolved>)  =
        //let Write Update Stament in tmp variable childPath_refIndex
        //let bRequiresResultCheck : boolean return from the previous function call
        let tmpVar = GetTmpVar refIndex
        let bRequiresResultCheck, updateStatement = UpdateDeterminant tmpVar (kind,refs) sTasName m r acn
        let bReturnRequiresResultCheck, retStatement = 
            match refIndex>0, bRequiresResultCheck with
            | false, false  -> false, updateStatement
            | false, true   -> true, updateStatement
            | true, false   -> true, updateStatement + "\n\n" + sa.MultiUpdateCheckWithFirstValue tmpVar tmpVar0
            | true, true    -> true, updateStatement + "\n\n" + sa.MultiUpdateCheckWithFirstValue2 tmpVar tmpVar0
        bReturnRequiresResultCheck,retStatement
    let ChildUpdates = childDependencies |> Seq.mapi HandleChildReference |> Seq.toList
    let actChildType = GetActualType ch.Type r
    let finalCheck = 
        let FieldIsWritable =
            match ch.AcnInsertedField with
            | false     -> false
            | true      ->
                match acn.Parameters |> Seq.tryFind(fun x -> x.ModName = m.Name.Value && x.TasName=tas.Name.Value && x.Name = ch.Name.Value) with
                | Some(_)   -> false
                | None      -> true
        match FieldIsWritable with
        | false     -> [(true,  if actChildType.Kind = Integer then  
                                   sa.MultiUpdateCheckWithFirstValueInteger chAccessFld tmpVar0
                                else
                                   sa.MultiUpdateCheckWithFirstValue chAccessFld tmpVar0)]
        | true      -> if actChildType.Kind = Integer then  
                            let chPath = parentPath@[ch.Name.Value]
                            let fldType,_ = spark_spec.PrintType ch.Type chPath (Some tas.Type) (TypeAssignment tas,m,r) {nErrorCode = 0}
                            let CheckRangeStatement =   
                                match (GetTypeUperRange ch.Type.Kind ch.Type.Constraints r) with
                                |Concrete(min, max)        -> [(true, sa.CheckBeforeAssignToIntField_min_max tmpVar0 min max)]
                                |NegInf(max)               -> [(true, sa.CheckBeforeAssignToIntField_max tmpVar0  max)]
                                |PosInf(min)               -> [(true, sa.CheckBeforeAssignToIntField_min tmpVar0 min)]
                                |Full                      -> []
                                |Empty                     -> []

                            CheckRangeStatement@[(false, sa.UpdateAsn1IntegerField chAccessFld tmpVar0 fldType)]
                       else 
                            [(false, sa.UpdateAsn1Field chAccessFld tmpVar0)]
    match ChildUpdates with
    | []    -> []
    | _     -> ChildUpdates@finalCheck

(*
Handle Encoding Updates for parameter or TmpTypes
return 
    (b) the update statement for acn determinants
    (a) whether this statement affects the result (and therefore the following statement must first check for result)
*)
let GetPointUpdateStatements  (point:AcnTypes.Point)   (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved)  =
    let path = point.AbsPath
    let prmAccessPath = ToC (path |> List.rev |> List.head)
//    let point = AcnTypes.Point.ParamPoint(path)
    let paramDependencies = acn_backend_logic.GroupReferences point r acn
    let GetTmpVar i = 
        if i = 0 then       
            prmAccessPath
        else
            ToC ((path.Tail.StrJoin "_") + "_" + i.ToString())

    let tmpVar0 = GetTmpVar 0
    let sTasName = tas.GetCName r.TypePrefix
    let HandleChildReference refIndex (kind:AcnTypes.LongReferenceKind, refs:seq<AcnTypes.LongReferenceResolved>)  =
        //let Write Update Stament in tmp variable childPath_refIndex
        //let bRequiresResultCheck : boolean return from the previous function call
        let tmpVar = GetTmpVar refIndex
        let bRequiresResultCheck, updateStatement = UpdateDeterminant tmpVar (kind,refs) sTasName m r acn
        let bReturnRequiresResultCheck, retStatement = 
            match refIndex>0, bRequiresResultCheck with
            | false, false  -> false, updateStatement
            | false, true   -> true, updateStatement
            | true, false   -> true, updateStatement + "\n\n" + sa.MultiParamUpdateCheckWithFirstValue tmpVar tmpVar0 
            | true, true    -> true, updateStatement + "\n\n" + sa.MultiParamUpdateCheckWithFirstValue2 tmpVar tmpVar0 
        bReturnRequiresResultCheck,retStatement
    let prmUpdates = paramDependencies |> Seq.mapi HandleChildReference |> Seq.toList
    let md,ts,name = path.Head, path.Tail.Head, path.Tail.Tail.Head
    let tp = match point with
             |AcnTypes.Point.TempPoint(_)     ->
                let x = acn.TmpTypes |> Seq.find(fun x -> x.Name = name && x.TasName = ts && x.ModName = md)                
                let asn1Type = AcnAsn1Type2Asn1Type x.Asn1Type
                let actAsn1Type = GetActualType asn1Type r
                if actAsn1Type.Kind = Integer then  
                    match (GetTypeUperRange actAsn1Type.Kind actAsn1Type.Constraints r) with
                    |Concrete(min, max)        -> [(true, sa.CheckBeforeAssignToIntField_min_max tmpVar0 min max)]
                    |NegInf(max)               -> [(true, sa.CheckBeforeAssignToIntField_max tmpVar0  max)]
                    |PosInf(min)               -> [(true, sa.CheckBeforeAssignToIntField_min tmpVar0 min)]
                    |Full                      -> []
                    |Empty                     -> []
                else
                    []

             | _                              -> []
                
    match  prmUpdates with
    | []    -> []
    | _     -> prmUpdates@tp


let GetTempVarType (kind:AcnTypes.LongReferenceKind, refs:seq<AcnTypes.LongReferenceResolved>) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let ref = Seq.head refs
    let otherType = GetTypeByPoint ref.decType r acn
    match kind with
    | AcnTypes.SizeDeterminant     -> Some(ss.Declare_spark_Integer())
    | AcnTypes.PresenceBool        -> Some(ss.Declare_BOOLEAN())
    | AcnTypes.ChoiceDeteterminant | AcnTypes.PresenceStr(_) ->
        let determinantType = GetTypeByPoint ref.determinant r acn
        match determinantType.Kind with
        | ReferenceType(modName, tasName, _)    ->
            match modName = m.Name with
            |true  -> Some (ss.Declare_Reference1 (GetTasCName tasName.Value r.TypePrefix))
            |false  -> Some (ss.Declare_Reference2 (ToC modName.Value) (GetTasCName tasName.Value r.TypePrefix))
        | _                                 -> raise(BugErrorException "")
    | AcnTypes.PresenceInt(_)  -> Some(ss.Declare_spark_Integer())
    | AcnTypes.RefTypeArgument(prmName)                          -> 
        let mdName, tsName = match otherType.Kind with
                                | ReferenceType(md,ts,_) -> md.Value, ts.Value
                                | _                    -> raise(BugErrorException "")
        let prm = acn.Parameters |> Seq.find(fun p -> p.ModName=mdName && p.TasName=tsName && p.Name=prmName)

        match prm .Mode with
        | AcnTypes.ParamMode.DecodeMode     -> 
            Some(spark_spec.PrintParamType prm m r)
        | AcnTypes.ParamMode.EncodeDecodeMode -> None


        

let HandleChildUpdate_tmpVars (ch:ChildInfo) (parentPath:list<string>) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let chPath = parentPath@[ch.Name.Value]
    let childPoint =  AcnTypes.Point.TypePoint(chPath)
    let GetTmpVar i = ToC((chPath.Tail.StrJoin "_") + "_" + i.ToString())
    acn_backend_logic.GroupReferences childPoint r acn |> Seq.mapi (fun i x -> GetTmpVar i, GetTempVarType x m r acn) |> Seq.toList |> List.choose(fun (v,t) -> if t.IsSome then Some(v,t.Value) else None) 


// called for by update function
let HandleParameterOrTmpUpdate_tmpVars   (point:AcnTypes.Point) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved)  =
    let path = point.AbsPath
    let GetTmpVar i = 
        if i = 0 then       
            ToC (path |> List.rev |> List.head)
        else
            ToC ((path.Tail.StrJoin "_") + "_" + i.ToString())
    let groupedRefs = acn_backend_logic.GroupReferences point r acn 
    match groupedRefs with
    | []        -> []
    | x::xs     -> 
        match point with
        | AcnTypes.Point.ParamPoint(_) -> groupedRefs |> Seq.mapi (fun i x -> GetTmpVar i, GetTempVarType x m r acn) |> Seq.toList |> List.tail |> List.choose(fun (v,t) -> if t.IsSome then Some(v,t.Value) else None) 
        | AcnTypes.Point.TempPoint(_)  -> groupedRefs |> Seq.mapi (fun i x -> GetTmpVar i, GetTempVarType x m r acn) |> Seq.toList |> List.choose(fun (v,t) -> if t.IsSome then Some(v,t.Value) else None) 
        | AcnTypes.Point.TypePoint(_)  -> raise(BugErrorException "")



(*
Emits the update procedure
<sTasName>_ACN_Encode_update_<sParamName>() 
*)

let EmitUpdate_param_functions(tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved)  =
    let parms = acn.Parameters |> List.filter(fun p -> p.ModName = m.Name.Value && p.TasName = tas.Name.Value && p.Mode = AcnTypes.DecodeMode)
    //for all types
    let sTasName = GetTasCName tas.Name.Value r.TypePrefix
    let rec printNestedItems (lst:list<bool*string>)= 
        match lst with
            |[]     -> null
            |(bCheck, sCont)::xs  -> 
                sa.PrintAcn_update_param_body sCont (printNestedItems xs) bCheck
    //Special Case for choice children when Reference kind is not present-when but   RefTypeArguments
    let IsSpecialChoiceCase (p:AcnTypes.Point) =
        match tas.Type.Kind with
        | Choice(children)  -> 
            let IsRefSpecial (r:AcnTypes.LongReferenceResolved, c:ChildInfo) =
                match r.Kind with
                |AcnTypes.RefTypeArgument(_)    ->(r.decType.AbsPath |> List.rev |> List.head) = c.Name.Value
                | _                             -> false
            let refs = acn.References |> List.filter(fun r -> r.determinant = p)
            if refs.Length = children.Length then
                List.zip refs children |> List.forall IsRefSpecial
            else
                false
        | _                 -> false
    let printNestedItemsChoice (p:AcnTypes.AcnParameter) (children:list<ChildInfo>)  = 
        let PrntChild (ch:ChildInfo, (bCheck:bool, updStm:string)) =
            sa.PrintAcn_update_param_body_choice_child ch.CName updStm bCheck (ch.CName_Present Spark)
        let prmAccessPath = ToC (p.Name)
        let path = [m.Name.Value; tas.Name.Value; p.Name]
        let point = AcnTypes.Point.ParamPoint(path)
        let refs = acn.References |> List.filter(fun r -> r.determinant = point) |> List.map(fun x -> (x.Kind, seq {yield x}))
        let updates = refs |> List.map(fun g -> UpdateDeterminant prmAccessPath g sTasName m r acn)
        let arrsUpdStmts = List.zip children updates  |> List.map PrntChild
        sa.PrintAcn_update_param_body_choice sTasName arrsUpdStmts
    
    let Update_param_Function (p:AcnTypes.AcnParameter) =
        let bHasResult = acn_backend_logic.Update_param_function_requires_result p.Name tas m r acn
        let prmName = ToC p.Name
        let path = [m.Name.Value; tas.Name.Value; p.Name]
        let point = AcnTypes.Point.ParamPoint(path)
        let prmType = spark_spec.PrintParamType p m r
        let updateStatements = GetPointUpdateStatements point tas m r acn
        let sContent, tmpVars =
            match IsSpecialChoiceCase point with
            | false ->
                let sContent = printNestedItems updateStatements
                let tmpVars = HandleParameterOrTmpUpdate_tmpVars point tas m r acn |> Seq.map(fun (fldName, fldType) -> sa.RefTypeParam_tmpVar fldName fldType)
                sContent, tmpVars
            | true  ->
                match tas.Type.Kind with
                | Choice(children)  -> 
                    let sContent = printNestedItemsChoice p children 
                    sContent, Seq.empty
                | _                 -> raise(BugErrorException "")
        sa.PrintAcn_update_param sTasName bHasResult prmName sContent prmType tmpVars
    parms |> List.map Update_param_Function |> Seq.StrJoin "\n\n"

 
type AcnUpdateStatement =
    | ImpactsEncoding of bool*string
    | ImpactsEncodingDecoding of bool*string

type Statement = 
    | UpdateExistsStatement of ChildInfo         // bit mask
    | AcnUpdateStatement of AcnUpdateStatement// bool*string     // acn update statement + flag indicating whether this statement changes result or not 
    | ChildEncDecStatement      of ChildInfo       // normal encoding / decoding of a child
    override x.ToString() = toString x 



let rec EmitTypeBodyAux (t:Asn1Type) (sTasName:string) (path:list<string>, pName:string option)  (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) codec =
    let handleSizeableType auto fixedSize extFld nullTerm =
        let encClass = Acn.GetSizeableEncodingClass t path r acn emptyLocation 
        let (min, max) = match uPER.GetTypeUperRange t.Kind t.Constraints r with
                            | Concrete(a, b)    -> (a,b)
                            | _                 -> raise(BugErrorException "Expecting size constraint")
        match min=max, encClass with
        | true, Acn.ExternalField(fldPath)     -> extFld min max fldPath 
        | true, _                              -> fixedSize max
        | false, Acn.AutoSize                  -> auto min max
        | false, Acn.FixedSize(nItems)         -> fixedSize nItems
        | false, Acn.ExternalField(fldPath)    -> extFld min max fldPath 
        | false, Acn.NullTerminated            -> nullTerm max

    let aligmVal = 
        match Acn.GetAlignment t r with
        | None                       -> 0I
        | Some(AcnTypes.NextByte)    -> 7I
        | Some(AcnTypes.NextWord)    -> 15I
        | Some(AcnTypes.NextDWord)   -> 31I
    let p = match pName with
            |Some(nm)   -> nm
            | None      -> GetAccessFld path (Same t) r 
    let index = "I1"
    let rec EmitInternalItem_min_max () =
        match t.Kind with
        | SequenceOf(inItem)          -> 
            let intItem = EmitTypeBody inItem sTasName (path@["#"], None) tas m r acn codec
            let intItemMax = Acn.RequiredBitsForAcnEncodingInt inItem (path@["#"]) r acn |> fst
            intItem, 0I, intItemMax
        | BitString                   -> su.InternalItem_bit_str p index codec, 1I, 1I 
        | OctetString                 -> su.InternalItem_oct_str p index codec, 8I, 8I 
        | IA5String | NumericString   -> sa.string_InternalItem p index codec,  7I, 7I
        | _                           -> raise(BugErrorException "")

    let longName = path.Tail |> Seq.map ToC |> Seq.StrJoin "_"
    let errCode = 
        match (GetTypeConstraintsErrorCode t.Constraints path r) with
        | None  -> "0"
        | Some(errCodeName) ->    errCodeName
    match t.Kind with
    | Integer   -> 
        
        let uperMin,uperMax = match uPER.GetTypeUperRange t.Kind t.Constraints r with
                                | Full            -> MinInt(), MaxInt() 
                                | NegInf(max)     -> MinInt(), max
                                | PosInf(min)     -> min, MaxInt()
                                | Concrete(a,b)   -> a,b
                                | Empty           -> 0I,0I
        let encClass= Acn.GetIntEncodingClass t r acn emptyLocation
        let adjVal = 0I//Acn.GetIntAdjustValue t r acn emptyLocation
        match encClass with
        | Acn.Integer_uPER                              -> spark_uper.EmitTypeBody t sTasName (path,pName) m  r codec
        | Acn.PositiveInteger_ConstSize(nSize)          -> sai.PositiveInteger_ConstSize p nSize (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_8               -> sai.PositiveInteger_ConstSize_8 p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_big_endian_16   -> sai.PositiveInteger_ConstSize_big_endian_16 p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_big_endian_32   -> sai.PositiveInteger_ConstSize_big_endian_32 p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_big_endian_64   -> sai.PositiveInteger_ConstSize_big_endian_64 p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_little_endian_16-> sai.PositiveInteger_ConstSize_little_endian_16  p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_little_endian_32-> sai.PositiveInteger_ConstSize_little_endian_32  p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_ConstSize_little_endian_64-> sai.PositiveInteger_ConstSize_little_endian_64  p (adjVal<>0I) adjVal uperMin uperMax codec
        | Acn.PositiveInteger_VarSize_LengthEmbedded    -> sai.PositiveInteger_VarSize_LengthEmbedded p (adjVal<>0I) adjVal uperMin codec
        | Acn.TwosComplement_ConstSize(nSize)           -> sai.TwosComplement_ConstSize p nSize uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_8                -> sai.TwosComplement_ConstSize_8 p uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_big_endian_16    -> sai.TwosComplement_ConstSize_big_endian_16 p uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_big_endian_32    -> sai.TwosComplement_ConstSize_big_endian_32 p uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_big_endian_64    -> sai.TwosComplement_ConstSize_big_endian_64 p uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_little_endian_16 -> sai.TwosComplement_ConstSize_little_endian_16 p uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_little_endian_32 -> sai.TwosComplement_ConstSize_little_endian_32 p uperMin uperMax codec
        | Acn.TwosComplement_ConstSize_little_endian_64 -> sai.TwosComplement_ConstSize_little_endian_64 p uperMin uperMax codec
        | Acn.TwosComplement_VarSize_LengthEmbedded     -> sai.TwosComplement_VarSize_LengthEmbedded p codec
        | Acn.ASCII_ConstSize(nBits)                    -> sai.ASCII_ConstSize p uperMin uperMax (nBits/8I) codec
        | Acn.ASCII_VarSize_LengthEmbedded              -> sai.ASCII_VarSize_LengthEmbedded p codec
        | Acn.ASCII_VarSize_NullTerminated              -> sai.ASCII_VarSize_NullTerminated p uperMin uperMax  codec
        | Acn.BCD_ConstSize(nBits)                      -> sai.BCD_ConstSize p uperMin uperMax (nBits/4I) codec
        | Acn.BCD_VarSize_LengthEmbedded                -> sai.BCD_VarSize_LengthEmbedded p codec
        | Acn.BCD_VarSize_NullTerminated                -> sai.BCD_VarSize_NullTerminated p uperMin uperMax codec
    | Real  ->  
        match Acn.GetRealEncodingClass t r with
        | Acn.Real_uPER                                     -> spark_uper.EmitTypeBody t sTasName (path, pName) m  r codec
        | Acn.Real_IEEE754_32_big_endian                    -> sai.Real_IEEE754_32_big_endian p codec
        | Acn.Real_IEEE754_64_big_endian                    -> sai.Real_IEEE754_64_big_endian p codec
        | Acn.Real_IEEE754_32_little_endian                 -> sai.Real_IEEE754_32_little_endian p codec
        | Acn.Real_IEEE754_64_little_endian                 -> sai.Real_IEEE754_64_little_endian p codec
    | Boolean                                           ->
        match Acn.GetBooleanEncoding t r with
        | AcnTypes.TrueValue(_)   -> sai.Boolean p true longName codec
        | AcnTypes.FalseValue(_) ->  sai.Boolean p false longName codec
    | NullType                                          ->
        let normalEncoding() =
            match Acn.GetNullEncodingValue t r with
            | Some(pattern) -> sai.Null_pattern p longName codec
            | None          -> sai.Null p codec
        match path with
        | []    -> raise(BugErrorException "")
        | x::[] -> raise(BugErrorException "")
        | md::ts::[]    -> normalEncoding()
        | _             ->
            let myName = path |> List.rev |> List.head
            let parPath = path |> List.rev |> List.tail |> List.rev
            let par = Ast.GetTypeByAbsPath parPath r
            let actPar = Ast.GetActualType par r
            match actPar.Kind with
            | Sequence(children)    ->
                let me = children |> Seq.find(fun x -> x.Name.Value = myName)
                match me.AcnInsertedField with
                | false            -> normalEncoding()
                | true             ->
                    match Acn.GetNullEncodingValue t r with
                    | Some(pattern) -> sai.Null_pattern2  longName codec
                    | None          -> sai.Null2 () codec
            | _                     -> normalEncoding()
    | Enumerated(items)                    ->
        match (Acn.isEnumEncodingValues t r) with
        | false ->
            let newType = Acn.GetIntTypeFromEnum t r acn
            let sActualCodecFunc = EmitTypeBody newType sTasName (path, Some "intVal") tas m r acn codec
            let arrItems = items |> Seq.mapi(fun idx it -> sai.Enumerated_item p (it.CEnumName r Spark) (BigInteger idx) codec)
            sai.EnumeratedEncIdx p sTasName arrItems sActualCodecFunc codec
        | true  ->
            let newType = Acn.GetIntTypeFromEnum t r acn
            let sActualCodecFunc = EmitTypeBody newType sTasName (path, Some "intVal") tas m r acn codec
            let arrItems = Acn.GetEnumEncodingValues t r Spark acn |> Seq.map(fun (sname,vl) -> sai.Enumerated_item p sname vl codec)
            sai.EnumeratedEncValues p sTasName arrItems sActualCodecFunc codec
    | IA5String | NumericString -> 
        let intItem, IntItemMin, IntItemMax = EmitInternalItem_min_max ()
        let auto min max       = sa.str_VarSize p sTasName index intItem min max (GetNumberOfBitsForNonNegativeInteger (max-min)) IntItemMin IntItemMax aligmVal codec
        let fixSize size       = sa.str_FixedSize p sTasName index intItem size IntItemMin IntItemMax aligmVal codec
        let extFld  min max (fldPath:AcnTypes.Point)= 
            let extFldPath = GetAccessFld (fldPath.AbsPath.Tail.Tail) (Same t) r 
            sa.str_external_field p sTasName index intItem min max IntItemMin IntItemMax extFldPath aligmVal codec
        let nullTerm max       = raise(BugErrorException "Null terminated is not implemented yet")
        handleSizeableType auto fixSize extFld nullTerm
    | SequenceOf(_) | OctetString | BitString->
        let intItem, IntItemMin, IntItemMax = EmitInternalItem_min_max ()
        let auto min max   = su.oct_sqf_VarSize sTasName p index intItem min max (GetNumberOfBitsForNonNegativeInteger (max-min)) IntItemMin IntItemMax aligmVal codec 
        let fixSize size   = su.oct_sqf_FixedSize p index intItem size sTasName IntItemMin IntItemMax aligmVal codec 
        let nullTerm max       = raise(BugErrorException "Null terminated is not supported for this type")
        let extFld  min max (fldPath:AcnTypes.Point)= 
            let extFldPath = GetAccessFld (fldPath.AbsPath.Tail.Tail) (Same t) r 
            sa.bit_oct_sqf_external_field sTasName p index intItem min max IntItemMin IntItemMax extFldPath aligmVal codec
        handleSizeableType auto fixSize extFld nullTerm
    | Sequence(children)                    -> 
        let GetChildThatIDepent (point:AcnTypes.Point) =
            let deps = acn.References |> List.filter(fun x -> x.determinant=point)
            let ref = deps |> Seq.tryFind(fun x ->  match x.Kind with
                                                    | AcnTypes.RefTypeArgument(prmName) -> 
                                                        let otherType = GetTypeByPoint x.decType r acn
                                                        match otherType.Kind with
                                                        | ReferenceType(md,ts, _) -> 
                                                            let m1 = r.Modules |> Seq.find(fun x -> x.Name.Value = md.Value)
                                                            let t1 = m1.TypeAssignments |> Seq.find(fun x -> x.Name.Value = ts.Value)
                                                            match acn.Parameters |> Seq.tryFind(fun p -> p.Name = prmName && p.TasName = t1.Name.Value && p.ModName = m1.Name.Value ) with
                                                            | None          -> false
                                                            | Some(actPrm)  -> match actPrm.Mode with
                                                                                | AcnTypes.EncodeDecodeMode  -> 
                                                                                    true
                                                                                | AcnTypes.DecodeMode        -> false
                                                        | _                    -> false
                                                    | _                                 -> false)
            match ref with
            | Some(x)   ->
                let chName = x.decType.AbsPath |> List.rev |> List.head
                Some(chName)
            | None      -> None


        let tmpTps = acn.TmpTypes |> List.filter(fun x-> x.ModName = m.Name.Value && x.TasName = tas.Name.Value) 
        // Get Acn update Statements for tmp types
        let d0 = tmpTps |> List.collect(fun x -> 
                                            let path = [m.Name.Value; tas.Name.Value; x.Name]
                                            let point = AcnTypes.Point.TempPoint(path)
                                            let name = point.AbsPath |> List.rev |> List.head
                                            let childIDepend = GetChildThatIDepent point
                                            let tmpTypeUpdates = GetPointUpdateStatements point tas m r acn //|> List.filter(fun (b,s) -> s <> "" )
                                            tmpTypeUpdates |> List.map(fun a -> (name, AcnUpdateStatement(ImpactsEncodingDecoding a)),childIDepend ))
        
        // Get update statements for the exist field of the optional fields
        let d1 = children |> List.filter(fun c -> match c.Optionality with 
                                                    | Some(Optional)|Some(Default(_)) -> true
                                                    | _                               -> false) 
                          |> List.map(fun c -> 
                                            let ChildIDepend =
                                                match Acn.GetPresenseEncodingClass path c acn with
                                                | Some(Acn.LikeUPER)           -> None
                                                | Some(Acn.PresBool(extFld)) | Some(Acn.PresInt(extFld, _)) | Some(Acn.PresStr(extFld, _))  -> 
                                                    let chName = extFld.AbsPath |> List.rev |> List.head
                                                    let IsParam = extFld.AbsPath.Length = 3 &&
                                                                  acn.Parameters |> Seq.exists(fun p -> p.ModName = m.Name.Value && p.TasName = tas.Name.Value && p.Name = chName)
                                                    match IsParam with
                                                    | true   -> None
                                                    | false  -> Some(chName)
                                                | None      -> None
                                            (c.Name.Value,(UpdateExistsStatement c)), ChildIDepend)
        // Get AcnUpdateStatements for children (for those having references to them), and child encode - decode statements
        let d2 = children |> List.collect(fun c -> 
                                                   let childUpdates = HandleChildUpdate c path sTasName tas m r acn
                                                   match childUpdates with
                                                   |[]  -> [((c.Name.Value, ChildEncDecStatement(c)), None)]
                                                   | _  -> (childUpdates |> List.map(fun a -> ((c.Name.Value, AcnUpdateStatement(ImpactsEncoding a)), None))) @ [((c.Name.Value, ChildEncDecStatement (c)), None)])

        let sortDecodedParts (items:list<(string*Statement)*option<string>>):list<Statement> =
            let independent = items |> List.choose(fun (x,ch) -> if ch.IsNone then Some(x) else None)
            let dependent = items |> List.choose(fun (x,ch) -> if ch.IsSome then Some( (x,[ch.Value])) else None)
            let cmprer (a1:string) (a2,x) = a1=a2
            let PrintCyclicItems  (items:list<(string*Statement)*list<string>>) =
                let printItemAux = function
                    | UpdateExistsStatement(child)  -> sprintf "UpdateExistsStatement<%s>" child.Name.Value
                    | AcnUpdateStatement(upStm)     -> 
                        match upStm with
                        | ImpactsEncoding(bl,nm)           -> sprintf "acn_update<%b,%s>" bl nm
                        | ImpactsEncodingDecoding(bl,nm)   -> sprintf "acn_update<%b,%s>" bl nm
                    | ChildEncDecStatement(child)   -> sprintf "child<%s>" child.Name.Value

                let PrintCyclicItem ((name:string, itemAux: Statement), lst:list<string>) =
                    sprintf "Item: %s of type %s depends on [%s]" name (printItemAux itemAux) (lst |> Seq.StrJoin ", ")
                items |> Seq.map PrintCyclicItem |> Seq.StrJoin "\n"
            let res = DoTopologicalSort2 independent dependent cmprer (fun x -> BugErrorException (sprintf "cyclic dependencies:\n%s" (PrintCyclicItems x) ))
            res |> List.map snd
        let decodedParts0 = d0@d1@d2
        let statements, firstDecodedItem = 
            match codec with
            | Encode -> (decodedParts0 |> List.map fst |> List.map snd), None
            | Decode -> 
                // filter only those statements that make sense in the decoding
                let onlyDecodingStatements = decodedParts0 |> List.filter (fun ((_,stm),_) -> match stm with AcnUpdateStatement(ImpactsEncoding(_)) -> false |_ -> true)
                let firstDecodedItem = match onlyDecodingStatements with
                                       | []                    -> None
                                       | ((itemName,_),_)::_   -> Some itemName
                sortDecodedParts onlyDecodingStatements, firstDecodedItem
        let ChildIsParameter (ch:ChildInfo) =
            acn.Parameters |> Seq.exists(fun x -> x.ModName = m.Name.Value && x.TasName=tas.Name.Value && x.Name = ch.Name.Value) 

        let bRequiresInit = match children |> List.filter(fun x -> not (ChildIsParameter x)) with
                            | []    -> false
                            | x::[] -> x.Optionality.IsSome
                            | _     -> true
        let DoesItemAffectsResult childItem =
            match childItem with
            | UpdateExistsStatement(c)      ->  match Acn.GetPresenseEncodingClass path c acn with
                                                | Some(Acn.LikeUPER)           -> match codec with Encode -> false | Decode -> true
                                                | Some(Acn.PresBool(extFld))    -> false
                                                | Some(Acn.PresInt(extFld, nVal)) ->false
                                                | Some(Acn.PresStr(extFld, sVal)) ->false
                                                | None      -> raise(BugErrorException "")
            | AcnUpdateStatement(upStm)   ->  
                let bRet = 
                    match upStm with
                    | ImpactsEncoding(bl,nm)           -> bl
                    | ImpactsEncodingDecoding(bl,nm)   -> bl

                match codec with
                | Decode    -> false
                | Encode    -> bRet
            | ChildEncDecStatement(c)      ->   match codec with
                                                | Decode -> true
                                                | Encode -> AcnEncodeFuncRequiresResult c.Type r acn

        let printChildItem childItem requiredBitsSoFar bRequiresAssert sNestedContent = 
            let content = 
                match childItem with
                | UpdateExistsStatement(c)     -> 
                    match Acn.GetPresenseEncodingClass path c acn with
                    | Some(Acn.LikeUPER)           -> sa.Sequence_optChild p c.CName errCode codec
                    | Some(Acn.PresBool(extFld))    -> 
                        let extFldPath = GetAccessFld (extFld.AbsPath.Tail.Tail) (Same t) r 
                        sa.Sequence_optChild_pres_bool p c.CName extFldPath codec
                    | Some(Acn.PresInt(extFld, nVal)) ->
                        let extFldPath = GetAccessFld (extFld.AbsPath.Tail.Tail) (Same t) r 
                        sa.Sequence_optChild_pres_int p c.CName extFldPath nVal codec
                    | Some(Acn.PresStr(extFld, sVal)) ->
                        let extFldPath = GetAccessFld (extFld.AbsPath.Tail.Tail) (Same t) r 
                        sa.Sequence_optChild_pres_str p c.CName extFldPath sVal codec
                    | None      -> raise(BugErrorException "")
                | AcnUpdateStatement(upStm)     ->
                    match codec with
                    | Decode    -> null
                    | Encode    -> match upStm with ImpactsEncoding(_,stm) | ImpactsEncodingDecoding(_,stm) -> stm
                | ChildEncDecStatement(c)     -> 
                    let bHasDef= match c.Optionality with Some(Default(v)) ->true |_  ->false
                    let sChildContent = EmitTypeBody c.Type sTasName (path@[c.Name.Value], None) tas m r acn codec 
                    sa.Sequence_Child p c.CName c.Optionality.IsSome sChildContent bHasDef codec
            let bResult = DoesItemAffectsResult childItem
            sa.JoinItems sTasName content sNestedContent requiredBitsSoFar bRequiresAssert bResult codec
        let  printChildren lst= 
            let requiredBitsForChild  = function
                | UpdateExistsStatement(c) -> match (Acn.ChildHasPresenseDeterminant path c acn) with
                                              | true   -> 0I
                                              | false  -> 1I
                | AcnUpdateStatement(_)   -> 0I
                | ChildEncDecStatement(c)        -> Acn.RequiredBitsForAcnEncodingInt c.Type (path@[c.Name.Value]) r acn |> fst
                
            let rec printChildrenAux lst requiredBitsSoFar= 
                match lst with
                    |[]     -> null
                    |x::xs  -> 
                        let requiredBitsForThis = requiredBitsForChild x
                        let newRequiredBitsSoFar = requiredBitsForThis + requiredBitsSoFar
                        printChildItem x newRequiredBitsSoFar (requiredBitsForThis>0I) (printChildrenAux xs newRequiredBitsSoFar)
            printChildrenAux lst 0I

        let DecOutPrmsInit = 
            acn.Parameters 
            |> List.filter(fun x -> x.ModName = m.Name.Value && x.TasName = tas.Name.Value && x.Mode = AcnTypes.EncodeDecodeMode)
            |> List.filter(fun x -> match firstDecodedItem with
                                    | None            -> true
                                    | Some(firstItem) -> x.Name <> firstItem) //exclude the parameter which is the first decoded item, 
                                                                              //otherwise we get a flow error 10 from spark
            |> Seq.map(fun p -> 
                            let sName = ToC p.Name
                            let sInit = spark_init.PrintInitValueByType (AcnAsn1Type2Asn1Type p.Asn1Type) tas.Name.Value m r
                            sa.PrmUpdate sName sInit)
        
        // In decoding, result must be initialized to 
        // result := spark_asn1_rtl.ASN1_RESULT'(Success => TRUE, ErrorCode => 0);
        // if the first statement that affects result is an optional child
        let bResultRequiresInit = 
            match statements |> List.filter DoesItemAffectsResult with
            | []    -> true
            | x::xs -> match x with
                       | UpdateExistsStatement(c)       -> false
                       | AcnUpdateStatement(_)          -> false
                       | ChildEncDecStatement(c)        -> c.Optionality.IsSome

        sa.Sequence p [(printChildren statements)] sTasName bRequiresInit DecOutPrmsInit bResultRequiresInit codec 

    | Choice(children)                      -> 
        let Choice_like_uPER() = 
            let nMin = 0I
            let nMax = BigInteger(Seq.length children) - 1I
            let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
            let printChild (i:int) (c:ChildInfo) =
                let pName = match codec with Encode -> None | Decode -> Some(c.CName+"_tmp")
                let newPath = path@[c.Name.Value]
                let sChildContent = EmitTypeBody c.Type sTasName (newPath, pName) tas m r acn codec 
                sa.ChoiceChild sTasName c.CName sChildContent (BigInteger i) nBits (c.CName_Present Spark) codec
            let arrChildren = children |> Seq.mapi printChild
            sa.Choice sTasName arrChildren nMax nBits codec
        let Choice_presWhen() =
            let printChild (i:int) (c:ChildInfo) =
                let pName = match codec with Encode -> None | Decode -> Some(c.CName+"_tmp")
                let newPath = path@[c.Name.Value]
                let sChildContent = EmitTypeBody c.Type sTasName (newPath, pName) tas m r acn codec 
                let printCondition = function
                    | Acn.PresBool(extFld)  -> 
                        let extFldPath = GetAccessFld (extFld.AbsPath.Tail.Tail) (Same t) r 
                        sa.ChoiceChild_preWhen_bool_condition extFldPath
                    | Acn.PresInt(extFld, nVal) ->
                        let extFldPath = GetAccessFld (extFld.AbsPath.Tail.Tail) (Same t) r 
                        sa.ChoiceChild_preWhen_int_condition extFldPath nVal
                    | Acn.PresStr(extFld, sVal) ->
                        let extFldPath = GetAccessFld (extFld.AbsPath.Tail.Tail) (Same t) r 
                        sa.ChoiceChild_preWhen_str_condition extFldPath sVal
                    | _                         -> raise(BugErrorException "")
                let conds = Acn.GetPresenseConditions path c acn |> Seq.map printCondition
                sa.ChoiceChild_preWhen sTasName c.CName sChildContent conds (i=0)  (c.CName_Present Spark) codec
            let arrChildren = children |> Seq.mapi printChild
            sa.Choice_preWhen  sTasName arrChildren  codec          
        let Choice_enm (enmDet:AcnTypes.Point) =
            let printChild (c:ChildInfo) =
                let pName = match codec with Encode -> None | Decode -> Some(c.CName+"_tmp")
                let newPath = path@[c.Name.Value]
                let sChildContent = EmitTypeBody c.Type sTasName (newPath, pName) tas m r acn codec 
                let determinantType = GetActualType (GetTypeByPoint enmDet r acn) r
                let enumValue = match determinantType.Kind with
                                |Enumerated(enms) -> enms |> List.find(fun en -> en.Name = c.Name)
                                |_ -> raise(BugErrorException(""))

                sa.ChoiceChild_Enum sTasName c.CName (ToC  (r.TypePrefix +  enumValue.uniqueName)) sChildContent (c.CName_Present Spark) codec                
            let extFldPath = GetAccessFld (enmDet.AbsPath.Tail.Tail) (Same t) r 
            sa.Choice_Enum sTasName (children |> Seq.map printChild) extFldPath codec
        match Acn.GetChoiceEncodingClass path children acn with
        | Some(Acn.EnumDeterminant(extFld))  -> Choice_enm extFld
        | Some(Acn.PresentWhenOnChildren)   -> Choice_presWhen()
        | None                              -> Choice_like_uPER()
    | ReferenceType(modName,tasName, _)    ->
        let dummy = 1
        let dum0 = acn.References |> List.filter(fun x -> x.decType.AbsPath = path )
        let args = acn.References |> 
                    List.filter(fun x -> x.decType.AbsPath = path ) |>
                    List.choose(fun x ->match x.Kind with 
                                        | AcnTypes.RefTypeArgument(prmName)  -> 
                                            let prm = acn.Parameters |> Seq.find(fun p -> p.ModName=modName.Value && p.TasName=tasName.Value && p.Name=prmName)
                                            match prm.Mode, codec with
                                            | AcnTypes.DecodeMode, Encode   -> None
                                            | AcnTypes.EncodeDecodeMode, Decode   -> 
                                                let determinantPath = GetPointAccessPath x.determinant r acn |> ToC
                                                Some (determinantPath, null)
                                            | _                             -> 
                                                let determinantPath = GetPointAccessPath x.determinant r acn
                                                let prmType = spark_spec.PrintParamType prm m r
                                                let localPrmName = ToC (prm.TasName + "_" + prm.Name) 
                                                //let actArg = prmType+"("+determinantPath+")"
                                                let actArg = determinantPath |> ToC
                                                Some (localPrmName, actArg)
                                        | _                                  -> None)
        let localPrms = args |> List.map fst                                         
        let actArgs = args |> List.map snd 
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        match modName.Value = m.Name.Value with
        | true  -> sa.ReferenceType1 p tsName (AcnEncodeFuncRequiresResult t r acn) actArgs localPrms codec
        | false -> sa.ReferenceType2 p (ToC modName.Value) tsName (AcnEncodeFuncRequiresResult t r acn)  actArgs localPrms codec


and EmitTypeBody (t:Asn1Type) (sTasName:string) (path:list<string>, pName:string option)  (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) codec =
    let sBody = EmitTypeBodyAux t sTasName (path, pName) tas m r acn codec
    let hasAligment, aligmVal = 
        match Acn.GetAlignment t r with
        | None                       -> false, 0I
        | Some(AcnTypes.NextByte)    -> true, 8I
        | Some(AcnTypes.NextWord)    -> true, 16I
        | Some(AcnTypes.NextDWord)   -> true, 32I
    sa.PrintTypeNoUpdate sBody hasAligment aligmVal  codec

let CollectBoolPatterns (m:Asn1Module) (r:AstRoot)  =
    let OnType (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<string>) = 
        let GenerateText (pattern:string) =
            let longName = path.Tail |> Seq.map ToC |> Seq.StrJoin "_"
            let arru = pattern.ToCharArray()|> Seq.map(fun c -> if c='1' then 1uy else 0uy)
            sai.Boolean_declare_pattern_array longName arru
        match t.Kind with
        | Boolean       -> 
            match Acn.GetBooleanEncoding t r with
            | AcnTypes.TrueValue(pattern)    
            | AcnTypes.FalseValue(pattern) -> (GenerateText pattern.Value)::state
        | NullType      ->
            match Acn.GetNullEncodingValue t r with
            | Some(pattern) ->(GenerateText pattern)::state
            | None          -> state
        | _             -> state

    VisitModule m r {DefaultVisitors with visitType=OnType} []


let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) codec =
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
        match t.Kind with
        | SequenceOf(_) | OctetString | BitString | IA5String | NumericString-> 
            let encClass = Acn.GetSizeableEncodingClass t path r acn emptyLocation 
            let newState =
                let s0 = (SEQUENCE_OF_INDEX (1,true))::state
                match (GetTypeUperRange t.Kind t.Constraints r) with
                | Concrete(a,b) when  a=b   -> 
                    match t.Kind, codec, encClass with
                    | IA5String, Encode, Acn.ExternalField(_)       -> LENGTH::s0
                    | NumericString, Encode, Acn.ExternalField(_)   -> LENGTH::s0
                    | _                                         -> s0
                | Concrete(a,b)   -> 
                    match t.Kind with 
                    | SequenceOf(_) | OctetString | BitString -> match codec, encClass with
                                                                 | Decode, Acn.FixedSize(_)     -> LENGTH::s0
                                                                 | Decode, Acn.AutoSize(_)      -> LENGTH::s0
                                                                 | _                            -> s0
                    | IA5String | NumericString               -> match codec, encClass with
                                                                 | Decode, Acn.ExternalField(_)     -> s0
                                                                 | _                                -> LENGTH::s0
                    | _                                       -> raise (BugErrorException(""))
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
        | ReferenceType(mdName, tsName, _) ->
            let prms = acn.Parameters |> 
                       Seq.filter(fun p -> p.ModName = mdName.Value && p.TasName = tsName.Value) |>
                       Seq.choose(fun p -> 
                                           let prmType = spark_spec.PrintParamType p m r                                          
                                           match p.Mode, codec with
                                           | AcnTypes.DecodeMode, Encode    -> None
                                           | AcnTypes.EncodeDecodeMode, Decode   -> None
                                           | _                              -> Some (REF_TYPE_PARAM ((ToC (p.TasName + "_" + p.Name)), prmType))
                                  ) |> Seq.toList


            (prms@state)
        | Choice(children) when codec = Decode -> 
            let handleChild (c:ChildInfo) =
                let typeDecl,_ = spark_spec.PrintType c.Type [m.Name.Value; tas.Name.Value; c.Name.Value] (Some tas.Type) (TypeAssignment tas,m,r) {spark_spec.State.nErrorCode = 0}
                CHOICE_TMP_FLD(c.CName, typeDecl)
            let cldnd = children |> List.map handleChild
            match Acn.GetChoiceEncodingClass path children acn with
            | Some(Acn.EnumDeterminant(extFld))  -> (cldnd@state)
            | Some(Acn.PresentWhenOnChildren)   -> (cldnd@state)
            | None                              -> CHOICE_IDX::(cldnd@state)
        | Sequence(children) ->
            let handleTempType (tmp:AcnTypes.AcnTempType) =
                match codec with
                | Encode ->
                    let path = [m.Name.Value; tas.Name.Value; tmp.Name]
                    let point = AcnTypes.Point.TempPoint(path)
                    let allTypes = HandleParameterOrTmpUpdate_tmpVars point tas m r acn
                    allTypes |> List.map(fun (varName, fldType) -> REF_TYPE_PARAM(varName, fldType))
                | Decode ->
                    let varName = ToC tmp.Name
                    let fldType = spark_spec.DeclateAcnAsn1Type tmp.Asn1Type m r
                    [REF_TYPE_PARAM(varName, fldType)]
            let handleAcnInsertedChild (c:ChildInfo) =
                let chPath = path@[c.Name.Value]
                let varName = c.CName
                let fldType,_ = spark_spec.PrintType c.Type chPath (Some t) (TypeAssignment tas,m,r) {nErrorCode = 0}
                REF_TYPE_PARAM(varName, fldType)
            let handleUptdateChildTmpVars (c:ChildInfo) =
                let childVars = HandleChildUpdate_tmpVars c [m.Name.Value; tas.Name.Value] m r acn
                childVars |> List.map(fun (fldName, fldType) -> REF_TYPE_PARAM(ToC fldName, fldType))            
            let childrenUpdateVars = match codec with
                                     | Encode   -> children |> List.collect handleUptdateChildTmpVars
                                     | Decode   -> []
            let tmpTps = acn.TmpTypes |> List.filter(fun x-> x.ModName = m.Name.Value && x.TasName = tas.Name.Value) 
            let tmpTypes = tmpTps |> List.collect handleTempType
            let tmpNames = tmpTps |> List.map(fun x -> x.Name)
            let prmNames = acn.Parameters |> List.filter(fun x-> x.ModName = m.Name.Value && x.TasName = tas.Name.Value) |> List.map(fun x -> x.Name)
            let excludedNames = Set.ofList (tmpNames@prmNames)
            let acnInsertedFields = children |> List.filter(fun x-> not(excludedNames |> Set.contains x.Name.Value) ) |> List.filter(fun c -> c.AcnInsertedField) |> List.filter(fun c -> (Ast.GetActualType c.Type r).Kind <> NullType) |> List.map handleAcnInsertedChild
            state@acnInsertedFields@tmpTypes@childrenUpdateVars
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
        | REF_TYPE_PARAM(fldName, fldType)  ->    sa.RefTypeParam_tmpVar fldName fldType

    lvs |> Seq.distinct |> Seq.map emitLocalVariable





let EmitTypeAss (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved) codec = 
    let path = [m.Name.Value; tas.Name.Value]
    let GetArgNameFromParam(p:AcnTypes.AcnParameter) codec =
        match p.Mode, codec with
        | AcnTypes.DecodeMode, Encode        -> None
        | AcnTypes.DecodeMode, Decode        -> Some (ToC p.Name) 
        | AcnTypes.EncodeDecodeMode, Encode  -> Some (ToC p.Name) 
        | AcnTypes.EncodeDecodeMode, Decode  -> Some (ToC p.Name) 
    let sTasName = tas.GetCName r.TypePrefix
    let sTypeBody = EmitTypeBody tas.Type sTasName (path, None) tas m r acn codec
    let localVars = CollectLocalVars tas.Type tas m r acn codec
    let annotations = 
        let kDependedsOnValue = SparkDeps.KDependsOnValue_acn tas.Type path r acn
        let kIndexDependsOnData = SparkDeps.KIndexDependsOnData_acn tas.Type path r acn
        let decodingResultDependsOnData = SparkDeps.DecodingResultDependsOnData_acn tas.Type path r acn
        let myParams = acn.Parameters |> List.filter(fun p -> p.TasName=tas.Name.Value && p.ModName=m.Name.Value)
        let DecInPrmsNames = myParams |> Seq.choose(fun p -> match p.Mode with AcnTypes.DecodeMode -> Some p.Name | _ -> None)
        let EncDecInOutPrmsNames = myParams |> Seq.choose(fun p -> match p.Mode with AcnTypes.EncodeDecodeMode -> Some (ToC p.Name) | _ -> None)
        let EncDecInOutPrmsNames_noBools = myParams |> Seq.filter(fun p -> SparkDeps.KDependsOnValue_acn (AcnAsn1Type2Asn1Type p.Asn1Type) [p.ModName; p.TasName; p.Name] r  acn (*p.Asn1Type <> AcnTypes.AcnAsn1Type.Boolean*)) |> Seq.choose(fun p -> match p.Mode with AcnTypes.EncodeDecodeMode -> Some (ToC p.Name) | _ -> None)
        (ss.ACN_annotations sTasName kDependedsOnValue (AcnEncodeFuncRequiresResult tas.Type r acn) decodingResultDependsOnData kIndexDependsOnData DecInPrmsNames EncDecInOutPrmsNames EncDecInOutPrmsNames_noBools codec).Split('\r','\n') 
        |> Seq.filter(fun s -> s<>"") |> Seq.map(fun s -> "-"+s)
    let myParams = acn.Parameters |> List.filter(fun p -> p.TasName=tas.Name.Value && p.ModName=m.Name.Value)
    let prms = myParams |> Seq.choose(fun p -> spark_spec.PrintExtracAcnParams p m r codec)
    let prmNames = myParams |> Seq.choose(fun p -> GetArgNameFromParam p codec)
    let bAcnEncodeFuncRequiresResult = AcnEncodeFuncRequiresResult tas.Type r acn
    sa.Tas sTasName bAcnEncodeFuncRequiresResult localVars sTypeBody  annotations prms prmNames codec


