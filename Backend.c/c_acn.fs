module c_acn

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open c_utils


(*
Main update function.
Handles only one update
returns the update statement and a flag indication if result check is required
*)
let UpdateDeterminant determinantPath determinantPathPtr (kind:AcnTypes.LongReferenceKind, refs:seq<AcnTypes.LongReferenceResolved>) (sTasName:string) (m:Asn1Module)(r:AstRoot) (acn:AcnTypes.AcnAstResolved)=
    let ref = Seq.head refs
    let otherType = GetTypeByPoint ref.decType r acn
    let otherTypePath = GetPointAccessPath ref.decType r acn
    let determinant = GetTypeByPoint ref.determinant r acn
    let actOtherType = GetActualType otherType r
    let actDeterminant = GetActualType determinant r
    match kind with
    | AcnTypes.SizeDeterminant     -> 
        let sCount = GetCount otherType otherTypePath r
        false, c_acn.SizeDependency determinantPath sCount
    | AcnTypes.ChoiceDeteterminant ->
        let printItem (ch:ChildInfo) (en:NamedItem) =
            c_acn.ChoiceDependencyEnum_Item determinantPath (ch.CName_Present C) (en.CEnumName r C)
        match actOtherType.Kind, actDeterminant.Kind with
        | Choice(children), Enumerated(enms)    ->
            let sortedEnms = 
                enms |> 
                List.sortBy (
                    fun en -> 
                        children |> Seq.findIndex (fun ch -> ch.Name = en.Name)
                )
            let arrsChEnumItems = Seq.map2 printItem children sortedEnms
            false, c_acn.ChoiceDependencyEnum sTasName arrsChEnumItems
        | _ -> raise(BugErrorException(""))
    | AcnTypes.PresenceBool        ->
        let parentPoint = AcnTypes.Point.TypePoint(ref.decType.AbsPath |> List.rev |> List.tail |> List.rev)
        let parentPath = GetPointAccessPath parentPoint (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let childName = ref.decType.AbsPath |> List.rev |> List.head
        false, c_acn.PresenceDependency determinantPath parentPath (ToC childName)
    | AcnTypes.PresenceInt(_)  ->
        let parentPoint = AcnTypes.Point.TypePoint(ref.decType.AbsPath |> List.rev |> List.tail |> List.rev)
        let parentPath = GetPointAccessPath parentPoint  (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let parentAsnType = GetAsn1TypeByPoint parentPoint (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let printItem (rf:AcnTypes.LongReferenceResolved) (ch:ChildInfo) =
             match rf.Kind with
             | AcnTypes.PresenceInt(intVal)  ->
                  c_acn.ChoiceDependencyIntPres_child determinantPath (ch.CName_Present C) (AcnTypes.EvaluateConstant acn.Constants intVal)
             | _                             -> raise(BugErrorException "")
        match parentAsnType.Kind with
        | Choice(children) ->
            let arrsChEnumItems = Seq.map2 printItem refs children
            false, c_acn.ChoiceDependencyPres sTasName arrsChEnumItems
        | _                             -> raise(BugErrorException "")
    | AcnTypes.PresenceStr(_)  ->
        let parentPoint = AcnTypes.Point.TypePoint(ref.decType.AbsPath |> List.rev |> List.tail |> List.rev)
        let parentPath = GetPointAccessPath parentPoint  (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let parentAsnType = GetAsn1TypeByPoint parentPoint (r:AstRoot) (acn:AcnTypes.AcnAstResolved)
        let printItem (rf:AcnTypes.LongReferenceResolved) (ch:ChildInfo) =
             match rf.Kind with
             | AcnTypes.PresenceStr(sVal)  ->
                  c_acn.ChoiceDependencyStrPres_child determinantPath (ch.CName_Present C) sVal
             | _                             -> raise(BugErrorException "")
        match parentAsnType.Kind with
        | Choice(children) ->
            let arrsChEnumItems = Seq.map2 printItem refs children
            false, c_acn.ChoiceDependencyPres sTasName arrsChEnumItems
        | _                             -> raise(BugErrorException "")
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
            let sNewTasName = newTas.GetCName r.TypePrefix
            let otherTypePath = GetPointAccessPathPtr ref.decType r acn
            true, c_acn.RefTypeArgument1 determinantPathPtr sNewTasName prmName otherTypePath


(*
Handle Encoding Updates for a Sequence child
*)
let HandleChildUpdate (ch:ChildInfo) (parentPath:list<string>) (sTasName:string) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let chPath = parentPath@[ch.Name.Value]
    let childPoint =  AcnTypes.Point.TypePoint(chPath)
    let childDependencies = acn_backend_logic.GroupReferences childPoint r acn
    let chAccessFld = match ch.AcnInsertedField with
                      | false -> GetTypeAccessPath chPath r
                      | true  -> (ch.CName ProgrammingLanguage.C)
    let GetTmpVar i = ToC ((chPath.Tail.StrJoin "_") + "_" + i.ToString())
    let tmpVar0 = GetTmpVar 0
    let HandleChildReference refIndex (kind:AcnTypes.LongReferenceKind, refs:seq<AcnTypes.LongReferenceResolved>)  =
        //let Write Update Stament in tmp variable childPath_refIndex
        //let bRequiresResultCheck : boolean return from the previous function call
        let tmpVar = GetTmpVar refIndex
        let tmpVarPtr = match (Ast.GetActualType ch.Type r).Kind with
                        | IA5String | NumericString -> tmpVar
                        | _                         -> "&" + tmpVar
        let bRequiresResultCheck, updateStatement = UpdateDeterminant tmpVar tmpVarPtr (kind,refs) sTasName m r acn
        let bReturnRequiresResultCheck, retStatement = 
            match refIndex>0, bRequiresResultCheck with
            | false, false  -> false, updateStatement
            | false, true   -> true, updateStatement
            | true, false   -> true, updateStatement + "\n\n" + c_acn.MultiUpdateCheckWithFirstValue tmpVar tmpVar0
            | true, true    -> true, updateStatement + "\n\n" + c_acn.MultiUpdateCheckWithFirstValue2 tmpVar tmpVar0
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
                                   c_acn.MultiUpdateCheckWithFirstValueInteger chAccessFld tmpVar0
                                else
                                   c_acn.MultiUpdateCheckWithFirstValue chAccessFld tmpVar0)]
        | true      -> if actChildType.Kind = Integer then  
                            let chPath = parentPath@[ch.Name.Value]
                            let fldType = c_h.PrintTypeDeclaration ch.Type chPath r
                            let CheckRangeStatement =   
                                match (GetTypeUperRange ch.Type.Kind ch.Type.Constraints r) with
                                |Concrete(min, max)        -> [(true, c_acn.CheckBeforeAssignToIntField_min_max tmpVar0 min max)]
                                |NegInf(max)               -> [(true, c_acn.CheckBeforeAssignToIntField_max tmpVar0  max)]
                                |PosInf(min)               -> [(true, c_acn.CheckBeforeAssignToIntField_min tmpVar0 min)]
                                |Full                      -> []
                                |Empty                     -> []

                            CheckRangeStatement@[(false, c_acn.UpdateAsn1IntegerField chAccessFld tmpVar0 fldType)]
                       else 
                            [(false, c_acn.UpdateAsn1Field chAccessFld tmpVar0)]
    match ChildUpdates with
    | []    -> []
    | _     -> ChildUpdates@finalCheck

(*
Handle Encoding Updates for parameter or TmpTypes
return 
    (b) the update statement for acn determinants
    (a) whether this statement affects the result (and therefore the following statement must first check for result)
*)
let GetPointUpdateStatements  (point:AcnTypes.Point) getPntAccesPath  (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved)  =
    let path = point.AbsPath
    let eqAsn1Type = GetAsn1TypeByPoint point r acn


    let prmAccessPath =  getPntAccesPath () //GetPointAccessPath point r acn
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

        let tmpVarPtr = match (Ast.GetActualType eqAsn1Type r).Kind with
                        | IA5String | NumericString -> tmpVar
                        | _                         -> "&" + tmpVar
        let bRequiresResultCheck, updateStatement = UpdateDeterminant tmpVar tmpVarPtr (kind,refs) sTasName m r acn
        let bReturnRequiresResultCheck, retStatement = 
            match refIndex>0, bRequiresResultCheck with
            | false, false  -> false, updateStatement
            | false, true   -> true, updateStatement
            | true, false   -> true, updateStatement + "\n\n" + c_acn.MultiParamUpdateCheckWithFirstValue tmpVar tmpVar0 
            | true, true    -> true, updateStatement + "\n\n" + c_acn.MultiParamUpdateCheckWithFirstValue2 tmpVar tmpVar0 
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
                    |Concrete(min, max)        -> [(true, c_acn.CheckBeforeAssignToIntField_min_max tmpVar0 min max)]
                    |NegInf(max)               -> [(true, c_acn.CheckBeforeAssignToIntField_max tmpVar0  max)]
                    |PosInf(min)               -> [(true, c_acn.CheckBeforeAssignToIntField_min tmpVar0 min)]
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
    | AcnTypes.SizeDeterminant     -> Some(ch.Declare_Integer())
    | AcnTypes.PresenceBool        -> Some(ch.Declare_Boolean())
    | AcnTypes.ChoiceDeteterminant | AcnTypes.PresenceStr(_) ->
        let determinantType = GetTypeByPoint ref.determinant r acn
        match determinantType.Kind with
        | ReferenceType(modName, tasName, _)    -> Some(GetTasCName tasName.Value r.TypePrefix)
        | _                                 -> raise(BugErrorException "")
    | AcnTypes.PresenceInt(_)  -> Some(ch.Declare_Integer())
    | AcnTypes.RefTypeArgument(prmName)                          -> 
        let mdName, tsName = match otherType.Kind with
                                | ReferenceType(md,ts, _) -> md.Value, ts.Value
                                | _                    -> raise(BugErrorException "")
        let prm = acn.Parameters |> Seq.find(fun p -> p.ModName=mdName && p.TasName=tsName && p.Name=prmName)

        match prm .Mode with
        | AcnTypes.ParamMode.DecodeMode     -> 
            Some(c_h.PrintParamType prm m r)
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
    let sStar = (TypeStar tas.Type r)
    let rec printNestedItems (lst:list<bool*string>)= 
        match lst with
            |[]     -> null
            |(bCheck, sCont)::xs  -> 
                c_acn.PrintAcn_update_param_body sCont (printNestedItems xs) bCheck
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
            c_acn.PrintAcn_update_param_body_choice_child (ch.CName_Present C) updStm bCheck
        let prmAccessPath = GetParameterAccessPath p  r
        let prmAccessPathPtr = GetParameterAccessPathPtr p r
        let path = [m.Name.Value; tas.Name.Value; p.Name]
        let point = AcnTypes.Point.ParamPoint(path)
        let refs = acn.References |> List.filter(fun r -> r.determinant = point) |> List.map(fun x -> (x.Kind, seq {yield x}))
        let updates = refs |> List.map(fun g -> UpdateDeterminant prmAccessPath prmAccessPathPtr g sTasName m r acn)
        let arrsUpdStmts = List.zip children updates  |> List.map PrntChild
        c_acn.PrintAcn_update_param_body_choice arrsUpdStmts
    
    let Update_param_Function (p:AcnTypes.AcnParameter) =
        let bHasResult = acn_backend_logic.Update_param_function_requires_result p.Name tas m r acn
        let prmName = ToC p.Name
        let path = [m.Name.Value; tas.Name.Value; p.Name]
        let point = AcnTypes.Point.ParamPoint(path)
        let prmType = c_h.PrintParamType p m r
        let prmStar = (TypeStar (Ast.AcnAsn1Type2Asn1Type p.Asn1Type) r)
        let updateStatements = GetPointUpdateStatements point (fun () -> "*" + (GetPointAccessPath point r acn)) tas m r acn
        let sContent, tmpVars =
            match IsSpecialChoiceCase point with
            | false ->
                let sContent = printNestedItems updateStatements
                let tmpVars = HandleParameterOrTmpUpdate_tmpVars point tas m r acn |> Seq.map(fun (fldName, fldType) -> c_acn.RefTypeParam_tmpVar fldName fldType)
                sContent, tmpVars
            | true  ->
                match tas.Type.Kind with
                | Choice(children)  -> 
                    let sContent = printNestedItemsChoice p children 
                    sContent, Seq.empty
                | _                 -> raise(BugErrorException "")
        c_acn.PrintAcn_update_param sTasName sStar prmType  prmName prmStar sContent tmpVars
    parms |> List.map Update_param_Function |> Seq.StrJoin "\n\n"

 
type AcnUpdateStatement =
    | ImpactsEncoding of bool*string
    | ImpactsEncodingDecoding of bool*string

type Statement = 
    | UpdateExistsStatement of ChildInfo         // bit mask
    | AcnUpdateStatement of AcnUpdateStatement// bool*string     // acn update statement + flag indicating whether this statement changes result or not 
    | ChildEncDecStatement      of ChildInfo       // normal encoding / decoding of a child
    override x.ToString() = toString x 





let rec EmitTypeBodyAux (t:Asn1Type) (sTasName:string) (path:list<string>, altPath:(string*string) option )  (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) codec =
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

    let pp,ptr = 
            match altPath with
            |Some(alt, altPtr)  -> alt, altPtr
            | None              -> GetTypeAccessPath path r,GetTypeAccessPathPtr path  r 
    let p = match codec with
            | Encode -> pp
            | Decode -> ptr
    let getIndexNameByPath (path:string list) =
        "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
    let index = getIndexNameByPath path
    let rec EmitInternalItem_min_max () =
        match t.Kind with
        | SequenceOf(inItem)          -> 
            let intItem = EmitTypeBody inItem sTasName (path@["#"], None) tas m r acn codec
            let intItemMax = Acn.RequiredBitsForAcnEncodingInt inItem (path@["#"]) r acn |> fst
            intItem, 0I, intItemMax
//        | BitString                   -> su.InternalItem_bit_str p index codec, 1I, 1I 
        | OctetString                 -> c_src.InternalItem_oct_str pp index codec ,8I,8I  //su.InternalItem_oct_str p index codec, 8I, 8I 
        | IA5String | NumericString   -> c_acn.string_InternalItem p index codec,  7I, 7I
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
        | Acn.Integer_uPER                              -> c_uper.EmitTypeBody t sTasName (path, altPath) m  r codec
        | Acn.PositiveInteger_ConstSize(nSize)          -> c_acn.PositiveInteger_ConstSize p nSize codec
        | Acn.PositiveInteger_ConstSize_8               -> c_acn.PositiveInteger_ConstSize_8 p codec
        | Acn.PositiveInteger_ConstSize_big_endian_16   -> c_acn.PositiveInteger_ConstSize_big_endian_16 p codec
        | Acn.PositiveInteger_ConstSize_big_endian_32   -> c_acn.PositiveInteger_ConstSize_big_endian_32 p codec
        | Acn.PositiveInteger_ConstSize_big_endian_64   -> c_acn.PositiveInteger_ConstSize_big_endian_64 p codec
        | Acn.PositiveInteger_ConstSize_little_endian_16-> c_acn.PositiveInteger_ConstSize_little_endian_16  p codec
        | Acn.PositiveInteger_ConstSize_little_endian_32-> c_acn.PositiveInteger_ConstSize_little_endian_32  p codec
        | Acn.PositiveInteger_ConstSize_little_endian_64-> c_acn.PositiveInteger_ConstSize_little_endian_64  p codec
        | Acn.PositiveInteger_VarSize_LengthEmbedded    -> c_acn.PositiveInteger_VarSize_LengthEmbedded p codec
        | Acn.TwosComplement_ConstSize(nSize)           -> c_acn.TwosComplement_ConstSize p nSize codec
        | Acn.TwosComplement_ConstSize_8                -> c_acn.TwosComplement_ConstSize_8 p codec
        | Acn.TwosComplement_ConstSize_big_endian_16    -> c_acn.TwosComplement_ConstSize_big_endian_16 p  codec
        | Acn.TwosComplement_ConstSize_big_endian_32    -> c_acn.TwosComplement_ConstSize_big_endian_32 p  codec
        | Acn.TwosComplement_ConstSize_big_endian_64    -> c_acn.TwosComplement_ConstSize_big_endian_64 p  codec
        | Acn.TwosComplement_ConstSize_little_endian_16 -> c_acn.TwosComplement_ConstSize_little_endian_16 p codec
        | Acn.TwosComplement_ConstSize_little_endian_32 -> c_acn.TwosComplement_ConstSize_little_endian_32 p codec
        | Acn.TwosComplement_ConstSize_little_endian_64 -> c_acn.TwosComplement_ConstSize_little_endian_64 p codec
        | Acn.TwosComplement_VarSize_LengthEmbedded     -> c_acn.TwosComplement_VarSize_LengthEmbedded p codec
        | Acn.ASCII_ConstSize(nBits)                    -> c_acn.ASCII_ConstSize p (nBits/8I) codec
        | Acn.ASCII_VarSize_LengthEmbedded              -> c_acn.ASCII_VarSize_LengthEmbedded p codec
        | Acn.ASCII_VarSize_NullTerminated              -> c_acn.ASCII_VarSize_NullTerminated p codec
        | Acn.BCD_ConstSize(nBits)                      -> c_acn.BCD_ConstSize p (nBits/4I) codec
        | Acn.BCD_VarSize_LengthEmbedded                -> c_acn.BCD_VarSize_LengthEmbedded p codec
        | Acn.BCD_VarSize_NullTerminated                -> c_acn.BCD_VarSize_NullTerminated p codec
    | Real  ->  
        match Acn.GetRealEncodingClass t r with
        | Acn.Real_uPER                                     -> c_uper.EmitTypeBody t sTasName (path, altPath) m  r codec
        | Acn.Real_IEEE754_32_big_endian                    -> c_acn.Real_32_big_endian p codec
        | Acn.Real_IEEE754_64_big_endian                    -> c_acn.Real_64_big_endian p codec
        | Acn.Real_IEEE754_32_little_endian                 -> c_acn.Real_32_little_endian p codec
        | Acn.Real_IEEE754_64_little_endian                 -> c_acn.Real_64_little_endian p codec
    | Boolean                                           ->
        let bEncValIsTrue, arruTrueValueAsByteArray, arruFalseValueAsByteArray, nSize =
            match Acn.GetBooleanEncoding t r with
            | AcnTypes.TrueValue(bitVal)   -> 
                let arrBytes = bitStringValueToByteArray bitVal
                true, arrBytes, (arrBytes |> Array.map (~~~)), bitVal.Value.Length
            | AcnTypes.FalseValue(bitVal)  -> 
                let arrBytes = bitStringValueToByteArray bitVal
                false, (arrBytes |> Array.map (~~~)), arrBytes, bitVal.Value.Length
        c_acn.Boolean pp ptr bEncValIsTrue (BigInteger nSize) arruTrueValueAsByteArray arruFalseValueAsByteArray codec
    | NullType                                          ->
        match Acn.GetNullEncodingValue t r with
        | Some(pattern) -> 
            let arrBytes = bitStringValueToByteArray pattern.AsLoc
            c_acn.Null arrBytes (BigInteger pattern.Length) codec
        | None          -> c_acn.Null_empty_pattern()
    | Enumerated(items)                    ->
        let enP,enPtr = "intVal" , "&intVal"
        match (Acn.isEnumEncodingValues t r) with
        | false ->
            let newType = Acn.GetIntTypeFromEnum t r acn
            let sActualCodecFunc = EmitTypeBody newType sTasName (path, Some (enP,enPtr)) tas m r acn codec
            let arrItems = items |> Seq.mapi(fun idx it -> c_acn.Enumerated_item pp (it.CEnumName r C) (BigInteger idx) codec)
            c_acn.EnumeratedEncIdx p sTasName arrItems sActualCodecFunc codec
        | true  ->
            let newType = Acn.GetIntTypeFromEnum t r acn
            let sActualCodecFunc = EmitTypeBody newType sTasName (path, Some (enP,enPtr)) tas m r acn codec
            let arrItems = Acn.GetEnumEncodingValues t r C acn |> Seq.map(fun (sname,vl) -> c_acn.Enumerated_item pp sname vl codec)
            c_acn.EnumeratedEncValues p sTasName arrItems sActualCodecFunc codec
    | IA5String | NumericString -> 
        let intItem, IntItemMin, IntItemMax = EmitInternalItem_min_max ()
        let auto min max       = c_acn.str_VarSize p index intItem min max codec
        let fixSize size       = c_acn.str_FixedSize p index intItem size codec
        let extFld  min max (fldPath:AcnTypes.Point)= 
            let extFldPath = GetPointAccessPath fldPath  r acn//GetTypeAccessPath (fldPath.AbsPath.Tail.Tail)  r 
            c_acn.str_external_field p index intItem min max extFldPath codec
        let nullTerm max       = raise(BugErrorException "Null terminated is not implemented yet")
        handleSizeableType auto fixSize extFld nullTerm
    | SequenceOf(_) | OctetString ->
        let intItem, IntItemMin, IntItemMax = EmitInternalItem_min_max ()
        let auto min max   = c_src.oct_sqf_VarSize p index intItem min max  (GetCount t pp r) codec  //c_src.oct_sqf_VarSize p index intItem min max (GetNumberOfBitsForNonNegativeInteger (max-min)) IntItemMin IntItemMax aligmVal codec 
        let fixSize size   = c_src.oct_sqf_FixedSize p index intItem size codec  //c_src.oct_sqf_FixedSize p index intItem size sTasName IntItemMin IntItemMax aligmVal codec 
        let nullTerm max       = raise(BugErrorException "Null terminated is not supported for this type")
        let extFld  min max (fldPath:AcnTypes.Point)= 
            let extFldPath = GetPointAccessPath fldPath  r acn //GetTypeAccessPath (fldPath.AbsPath.Tail.Tail)  r 
            c_acn.oct_sqf_external_field pp index intItem min max extFldPath codec
        handleSizeableType auto fixSize extFld nullTerm
    | BitString ->
        let auto min max   = c_src.uper_bitString_VarSize pp min max codec  
        let fixSize size   = c_src.uper_bitString_FixSize pp size codec 
        let nullTerm max       = raise(BugErrorException "Null terminated is not supported for this type")
        let extFld  min max (fldPath:AcnTypes.Point)= 
            let extFldPath = GetPointAccessPath fldPath  r acn 
            c_acn.bit_string_external_field pp min max extFldPath codec
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
                                            let tmpTypeUpdates = GetPointUpdateStatements point (fun () -> GetPointAccessPath point r acn) tas m r acn //|> List.filter(fun (b,s) -> s <> "" )
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
        let bRequiresInit = match (children |> List.filter(fun x -> not x.AcnInsertedField)) with
                            | []    -> false
                            | x::[] -> x.Optionality.IsSome
                            | _     -> true

        let uPERoptionalChildren = children |> List.filter(fun c -> match Acn.GetPresenseEncodingClass path c acn with
                                                                    | Some(Acn.LikeUPER)    -> true
                                                                    | _                     -> false) 

        let sBitMaskName = (TypeLongName path) + "bitMask"
        let printChildItem childItem sNestedContent = 
            let content = 
                match childItem with
                | UpdateExistsStatement(c)     -> 
                    match Acn.GetPresenseEncodingClass path c acn with
                    | Some(Acn.LikeUPER)           -> 
                        let index = uPERoptionalChildren |> Seq.findIndex(fun ch -> ch.Name.Value = c.Name.Value)
                        let nByteIndex = BigInteger (index / 8)
                        let sAndMask=System.String.Format("{0:X2}", 0x80 >>>(index % 8) )
                        c_acn.Sequence_presense_optChild pp (c.CName ProgrammingLanguage.C) errCode sBitMaskName nByteIndex sAndMask codec
                    | Some(Acn.PresBool(extFld))    -> 
                        let extFldPath = GetPointAccessPath extFld  r acn//GetTypeAccessPath (extFld.AbsPath.Tail.Tail)  r 
                        c_acn.Sequence_presense_optChild_pres_bool pp (c.CName ProgrammingLanguage.C) extFldPath codec
                    | Some(Acn.PresInt(extFld, nVal)) ->
                        let extFldPath = GetPointAccessPath extFld  r acn //GetTypeAccessPath (extFld.AbsPath.Tail.Tail)  r 
                        c_acn.Sequence_presense_optChild_pres_int pp (c.CName ProgrammingLanguage.C) extFldPath nVal codec
                    | Some(Acn.PresStr(extFld, sVal)) ->
                        let extFldPath = GetPointAccessPath extFld  r acn //GetTypeAccessPath (extFld.AbsPath.Tail.Tail)  r 
                        c_acn.Sequence_presense_optChild_pres_str pp (c.CName ProgrammingLanguage.C) extFldPath sVal codec
                    | None      -> raise(BugErrorException "")
                | AcnUpdateStatement(upStm)     ->
                    match codec with
                    | Decode    -> null
                    | Encode    -> match upStm with ImpactsEncoding(_,stm) | ImpactsEncodingDecoding(_,stm) -> stm
                | ChildEncDecStatement(c)     -> 
                    let childPath =  path@[c.Name.Value]
                    let chAccPath = 
                        match c.AcnInsertedField with
                        | false     ->  None
                        | true      -> 
                            match (Ast.GetActualType c.Type r).Kind with
                            | IA5String | NumericString -> Some(c.CName ProgrammingLanguage.C, c.CName ProgrammingLanguage.C)
                            | _                         -> 
                                let mdName = path.Head
                                let tsName = path.Tail.Head
                                match acn.Parameters |> Seq.exists(fun x-> x.ModName = mdName && x.TasName = tsName && x.Name = c.Name.Value) with
                                | true  -> 
                                    match codec with
                                    | Encode    -> Some(c.CName ProgrammingLanguage.C, "&" + (c.CName ProgrammingLanguage.C))
                                    | Decode    -> Some("*" + (c.CName ProgrammingLanguage.C), c.CName ProgrammingLanguage.C)
                                | false -> Some(c.CName ProgrammingLanguage.C, "&" + (c.CName ProgrammingLanguage.C))
                    let sChildContent = EmitTypeBody c.Type sTasName (childPath, chAccPath) tas m r acn codec 
                    match c.Optionality with
                    | None      -> c_acn.Sequence_mandatory_child (c.CName ProgrammingLanguage.C) sChildContent codec
                    | Some(Default(vl))  ->
                        let sDefaultValue = c_variables.PrintAsn1Value vl c.Type false (sTasName,0) m r
                        let sChildTypeDeclaration = c_h.PrintTypeDeclaration c.Type childPath r
                        c_acn.Sequence_default_child pp (c.CName ProgrammingLanguage.C) sChildContent sChildTypeDeclaration sDefaultValue codec
                    | _                 ->
                        c_acn.Sequence_optional_child pp (c.CName ProgrammingLanguage.C) sChildContent codec
            c_acn.JoinItems content sNestedContent //requiredBitsSoFar bRequiresAssert  
        let  printChildren lst= 
            let rec printChildrenAux  = function
                    |[]     -> null
                    |x::xs  -> printChildItem x  (printChildrenAux xs )
            printChildrenAux lst
        
        let nUPERoptionalChildren = uPERoptionalChildren |> Seq.length
        c_acn.Sequence (printChildren statements) (nUPERoptionalChildren>0) (BigInteger nUPERoptionalChildren) sBitMaskName codec 
    | Choice(children)                      -> 
        let Choice_like_uPER() = 
            let nMin = 0I
            let nMax = BigInteger(Seq.length children) - 1I
            let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
            let printChild (i:int) (c:ChildInfo) =
                let newPath = path@[c.Name.Value]
                let sChildContent = EmitTypeBody c.Type sTasName (newPath, None) tas m r acn codec 
                c_acn.ChoiceChild pp (c.CName_Present C) (BigInteger i) nMax sChildContent  codec
            let arrChildren = children |> Seq.mapi printChild
            c_acn.Choice p arrChildren nMax errCode codec
        let Choice_presWhen() =
            let printChild (i:int) (c:ChildInfo) =
                let newPath = path@[c.Name.Value]
                let sChildContent = EmitTypeBody c.Type sTasName (newPath, None) tas m r acn codec 
                let printCondition = function
                    | Acn.PresBool(extFld)  -> 
                        let extFldPath = GetPointAccessPath extFld  r acn //GetTypeAccessPath (extFld.AbsPath.Tail.Tail)  r 
                        c_acn.ChoiceChild_preWhen_bool_condition extFldPath
                    | Acn.PresInt(extFld, nVal) ->
                        let extFldPath = GetPointAccessPath extFld  r acn //GetTypeAccessPath (extFld.AbsPath.Tail.Tail)  r 
                        c_acn.ChoiceChild_preWhen_int_condition extFldPath nVal
                    | Acn.PresStr(extFld, sVal) ->
                        let extFldPath = GetPointAccessPath extFld  r acn //GetTypeAccessPath (extFld.AbsPath.Tail.Tail)  r 
                        c_acn.ChoiceChild_preWhen_str_condition extFldPath sVal
                    | _                         -> raise(BugErrorException "")
                let conds = Acn.GetPresenseConditions path c acn |> Seq.map printCondition
                c_acn.ChoiceChild_preWhen pp (c.CName_Present C) sChildContent conds (i=0)  codec
            let arrChildren = children |> Seq.mapi printChild
            c_acn.Choice_preWhen  p arrChildren errCode codec          
        let Choice_enm (enmDet:AcnTypes.Point) =
            let printChild (c:ChildInfo) =
                let newPath = path@[c.Name.Value]
                let sChildContent = EmitTypeBody c.Type sTasName (newPath, None) tas m r acn codec
                let determinantType = GetActualType (GetTypeByPoint enmDet r acn) r
                let enumValue = match determinantType.Kind with
                                | Enumerated(enms) -> enms |> List.find(fun en -> en.Name = c.Name)
                                | _ -> raise(BugErrorException(""))
                c_acn.ChoiceChild_Enum pp enumValue.c_name (c.CName_Present C) sChildContent codec                
            let extFldPath = GetPointAccessPath enmDet  r acn //GetTypeAccessPath (enmDet.AbsPath.Tail.Tail)  r 
            c_acn.Choice_Enum p (children |> Seq.map printChild) extFldPath errCode codec
        match Acn.GetChoiceEncodingClass path children acn with
        | Some(Acn.EnumDeterminant(extFld)) -> Choice_enm extFld
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
                                                let determinantPath = GetPointAccessPathPtr x.determinant  r acn |> ToC
                                                Some (determinantPath, null)
                                            | _                             -> 
                                                let determinantPath = GetPointAccessPath x.determinant  r acn
                                                let prmType = c_h.PrintParamType prm m r
                                                let localPrmName = ToC (prm.TasName + "_" + prm.Name) 
                                                //let actArg = prmType+"("+determinantPath+")"
                                                let actArg = determinantPath //|> ToC
                                                Some (localPrmName, actArg)
                                        | _                                  -> None)
        let localPrms = args |> List.map fst                                         
        let actArgs = args |> List.map snd 
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        c_acn.ReferenceType1 ptr tsName true actArgs localPrms codec


and EmitTypeBody (t:Asn1Type) (sTasName:string) (path:list<string>, altPath:(string*string) option )  (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) codec =
    let sBody = EmitTypeBodyAux t sTasName (path, altPath) tas m r acn codec
    let hasAligment, aligmVal = 
        match Acn.GetAlignment t r with
        | None                       -> false, ""
        | Some(AcnTypes.NextByte)    -> true, "NextByte"
        | Some(AcnTypes.NextWord)    -> true, "NextWord"
        | Some(AcnTypes.NextDWord)   -> true, "NextDWord"
    c_acn.PrintTypeNoUpdate sBody hasAligment aligmVal  codec


let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) codec =
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
        match t.Kind with
        | SequenceOf(_) | OctetString | BitString | IA5String | NumericString-> 
            let encClass = Acn.GetSizeableEncodingClass t path r acn emptyLocation 
            let newState =
                let s0 = (SEQUENCE_OF_INDEX 1)::state
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
            | IA5String | NumericString -> CHAR_VAL::newState
            | BitString                 -> state
            |_                          -> newState
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
                                           let prmType = c_h.PrintParamType p m r                                          
                                           match p.Mode, codec with
                                           | AcnTypes.DecodeMode, Encode    -> None
                                           | AcnTypes.EncodeDecodeMode, Decode   -> None
                                           | _                              -> Some (REF_TYPE_PARAM ((ToC (p.TasName + "_" + p.Name)), prmType))
                                  ) |> Seq.toList


            (prms@state)
        | Choice(children) when codec = Decode -> 
            match Acn.GetChoiceEncodingClass path children acn with
            | Some(Acn.EnumDeterminant(extFld))  -> (state)
            | Some(Acn.PresentWhenOnChildren)   -> (state)
            | None                              -> CHOICE_IDX::(state)
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
                    let fldType = c_h.DeclateAcnAsn1Type tmp.Asn1Type m r
                    [REF_TYPE_PARAM(varName, fldType)]
            let handleAcnInsertedChild (c:ChildInfo) =
                let chPath = path@[c.Name.Value]
                let varName = c.CName ProgrammingLanguage.C
                let fldType = c_h.PrintTypeDeclaration c.Type chPath r 
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


            let sBitMaskName = (TypeLongName path) + "bitMask"
            let uPERoptionalChildren = children |> List.filter(fun c -> match Acn.GetPresenseEncodingClass path c acn with
                                                                        | Some(Acn.LikeUPER)    -> true
                                                                        | _                     -> false) 
            let nOptChildren = uPERoptionalChildren |> Seq.length
            let nSize = BigInteger (System.Math.Ceiling( (float nOptChildren) / 8.0))
            let bitMaskVar = if nOptChildren = 0 then [] else [SEQUENCE_BitMask( sBitMaskName, nSize)]
            state@bitMaskVar@acnInsertedFields@tmpTypes@childrenUpdateVars
        | _             -> state

    let lvs = VisitType t [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []
    let emitLocalVariable = function
        | SEQUENCE_OF_INDEX(i) -> c_src.Emit_local_variable_SQF_Index (BigInteger i) 
        | EXTENSION_BIT     -> ""
        | LENGTH            -> c_src.Declare_Length()
        | ENUM_IDX          -> c_acn.Declare_EnumValue()
        | CHOICE_IDX        -> c_src.Declare_ChoiceIndex()
//        | CHOICE_TMP_FLD(fldName, fldType)  -> su.ChoiceChild_tmpVar fldName fldType
        | CHAR_VAL          -> "" //su.Declare_CharValue()
        | NCOUNT            -> "" //su.Declare_nCount()
        | CUR_BLOCK_SIZE    -> "" //su.Declare_curBlockSize()
        | CUR_ITEM          -> "" //su.Declare_curItem()
        | LEN2              -> "" //su.Declare_len2()
        | REF_TYPE_PARAM(fldName, fldType)  ->    c_acn.RefTypeParam_tmpVar fldName fldType
        | SEQUENCE_BitMask(b,i) -> c_src.Declare_SequenceBitMask b i
    let aa = System.Single.MinValue
    lvs |> Seq.distinct |> Seq.map emitLocalVariable



let EmitTypeAss (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  (acn:AcnTypes.AcnAstResolved) codec = 
    let path = [m.Name.Value; tas.Name.Value]
    let sTasName = tas.GetCName r.TypePrefix
    let sStar = (TypeStar tas.Type r)
    let sTypeBody = EmitTypeBody tas.Type sTasName (path, None) tas m r acn codec
    let localVars = CollectLocalVars tas.Type tas m r acn codec
    let myParams = acn.Parameters |> List.filter(fun p -> p.TasName=tas.Name.Value && p.ModName=m.Name.Value)
    let prms = myParams |> Seq.choose(fun p -> c_h.PrintExtracAcnParams p m r codec)
    c_acn.Tas sTasName sStar localVars sTypeBody  prms codec


