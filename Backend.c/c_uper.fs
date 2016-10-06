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

module c_uper

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open c_utils



let rec EmitInternalItem_min_max (t:Asn1Type) (sTasName:string) (path:list<string>)  (m:Asn1Module) (r:AstRoot)  codec =
    let sTasName = GetTasCName (path |> Seq.nth 1) r.TypePrefix
    let p = match codec with
            | Encode -> GetTypeAccessPath path r
            | Decode -> GetTypeAccessPathPtr path  r 
    let pp = GetTypeAccessPath path r
    let getIndexNameByPath (path:string list) =
        "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
    let index = getIndexNameByPath path
    
    match t.Kind with
    | SequenceOf(_) | OctetString ->
        match t.Kind with
        | SequenceOf(inItem)     -> 
            let intItem = EmitTypeBody inItem sTasName (path@["#"], None) m r codec
            let nMax = uperGetMaxSizeInBitsAsInt inItem.Kind inItem.Constraints inItem.Location r
            let nMin = 0I
            intItem,nMin,nMax
        | OctetString            -> c_src.InternalItem_oct_str pp index codec ,8I,8I 
        | _      -> raise(BugErrorException "")
    | IA5String | NumericString -> 
        let alphaCons = t.Constraints |> List.filter(fun x -> match x with AlphabetContraint(_) -> true |_ -> false)
        match (Seq.isEmpty alphaCons) with
        | true  -> c_src.InternalItem_string_no_alpha pp index codec, 7I, 7I
        | false -> 
            let alphaSet = GetTypeUperRangeFrom (t.Kind, t.Constraints, r)
            let nLastItemIndex = BigInteger (alphaSet.Length - 1)
            let arrAsciiCodes = alphaSet |> Array.map(fun x -> BigInteger (System.Convert.ToInt32 x))
            let nCharIndexSize = (GetNumberOfBitsForNonNegativeInteger (BigInteger (alphaSet.Length - 1)))
            let nCharIndexMax = BigInteger alphaSet.Length-1I
            c_src.InternalItem_string_with_alpha pp index nLastItemIndex arrAsciiCodes (nLastItemIndex+1I) codec,nCharIndexSize,nCharIndexSize
    | _     ->raise(BugErrorException "")

and  EmitTypeBody (t:Asn1Type) (sTasName:string) (path:list<string>, altPath:(string*string) option  )  (m:Asn1Module) (r:AstRoot)  codec =
    let p = match codec with
            | Encode -> 
                match altPath with
                | None -> GetTypeAccessPath path r
                | Some(altPath, altPathPtr) -> altPath
            | Decode -> 
                match altPath with
                | None -> GetTypeAccessPathPtr path  r 
                | Some(altPath, altPathPtr) -> altPathPtr
                
    let pp = 
            match altPath with
            | None -> GetTypeAccessPath path r
            | Some(altPath, altPathPtr) -> altPath
        
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
        let IntBod cons extCon =
            match (GetTypeUperRange t.Kind cons r) with
            | Concrete(min, max) when min=max     -> c_src.IntNoneRequired pp min   errCode codec
            | Concrete(min, max) when min>=0I && (not extCon)   -> c_src.IntFullyConstraintPos p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode codec
            | Concrete(min, max)      -> c_src.IntFullyConstraint p min max (GetNumberOfBitsForNonNegativeInteger (max-min))  errCode codec
            | PosInf(a)  when a>=0I && (not extCon)  -> c_src.IntSemiConstraintPos p a  errCode codec
            | PosInf(a)               -> c_src.IntSemiConstraint p a  errCode codec
            | NegInf(max)             -> c_src.IntUnconstraint p errCode codec
            | Full                    -> c_src.IntUnconstraint p errCode codec
            | Empty                   -> raise(BugErrorException "")
        let rootCons = t.Constraints |> List.choose(fun x -> match x with RootConstraint(a) |RootConstraint2(a,_) -> Some(x) |_ -> None) 
        let getValueByConstraint c = 
            match (GetUperRange c r) with
            | Concrete(a, _) | PosInf(a)  | NegInf(a) -> a
            | Full                    -> 0I
            | Empty                   -> raise(BugErrorException "")

        match rootCons with
        | []                            -> IntBod t.Constraints false
        | (RootConstraint a)::rest      -> 
            let cc =  c_validate.PrintTypeContraint (Same t) path a "" m r 
            c_src.IntRootExt p (getValueByConstraint a) cc (IntBod [a] true) errCode codec 
        | (RootConstraint2(a,_))::rest  -> 
            let cc =  c_validate.PrintTypeContraint (Same t) path a "" m r 
            c_src.IntRootExt2 p (getValueByConstraint a) cc (IntBod [a] true) errCode codec 
        | _                             -> raise(BugErrorException "")
    | Boolean -> c_src.Boolean p errCode codec
    | Real    -> c_src.Real p errCode codec
    | ReferenceType(modName,tasName, _)    ->
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        match modName.Value = m.Name.Value with
        | true  -> c_src.ReferenceType1 (GetTypeAccessPathPtr path  r) tsName codec 
        | false -> c_src.ReferenceType2 (GetTypeAccessPathPtr path  r) (ToC modName.Value) tsName codec
        
    | Sequence(children)    ->
        let asn1Children = children |> List.filter(fun x -> not x.AcnInsertedField)
        let optionalChildren = asn1Children |> List.filter(fun c -> c.Optionality.IsSome)
        let d1 = optionalChildren |> List.map(fun c -> (0,c))
        let nOptionalChildrenLength = BigInteger (optionalChildren.Length)
        let d2 = asn1Children |> List.map(fun c -> (1,c))
        let decodedParts = d1@d2
        let sBitMaskName = (TypeLongName path) + "bitMask"

        let printChild (k:int, c:ChildInfo) sNestedContent = 
            let content = 
                match k with
                | 0     -> c_src.uper_Sequence_optChild p (c.CName ProgrammingLanguage.C) codec
                | _     ->
                    let childPath =  path@[c.Name.Value]
                    let sChildContent = EmitTypeBody c.Type sTasName (childPath, None) m r codec 
                    match c.Optionality with
                    |None                 ->  
                        c_src.uper_Sequence_mandatory_child (c.CName ProgrammingLanguage.C) sChildContent codec
                    |Some(optCase)        ->
                        let index = optionalChildren |> Seq.findIndex(fun ch -> ch.Name.Value = c.Name.Value)
                        let nByteIndex = BigInteger (index / 8)
                        let sAndMask=System.String.Format("{0:X2}", 0x80 >>>(index % 8) )
                        match optCase with
                        |Optional |AlwaysPresent |AlwaysAbsent   ->  
                            c_src.uper_Sequence_optional_child pp (c.CName ProgrammingLanguage.C) sChildContent sBitMaskName nByteIndex sAndMask codec
                        |Default(dv)    ->
                            let sDefaultValue = c_variables.PrintAsn1Value dv c.Type false (sTasName,0) m r
                            let sChildTypeDeclaration = c_h.PrintTypeDeclaration c.Type childPath r
                            c_src.uper_Sequence_default_child pp (c.CName ProgrammingLanguage.C) sChildContent sBitMaskName nByteIndex sAndMask sChildTypeDeclaration sDefaultValue codec
            c_src.JoinItems content sNestedContent 

        let  printChildren (lst:list<int*ChildInfo>)= 
            let rec printChildrenAux = function
                |[]     -> null
                |x::xs  -> printChild x  (printChildrenAux xs )
            printChildrenAux lst 

        c_src.uper_Sequence (printChildren decodedParts) (nOptionalChildrenLength>0I) sBitMaskName nOptionalChildrenLength codec 
    | SequenceOf(_) | OctetString ->
        let getIndexNameByPath (path:string list) =
            "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
        let index = getIndexNameByPath path
        
        let encInternalItem, min, max = EmitInternalItem_min_max t sTasName path m r codec
        let s1 a  = c_src.oct_sqf_FixedSize p index encInternalItem a codec 
        let s2 a b=  c_src.oct_sqf_VarSize p index encInternalItem a b  (GetCount t pp r) codec 
        let s3 a b=  
            let sCount = GetCount t pp r
            let level = BigInteger ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1)
            c_src.Fragmentation_sqf p false level encInternalItem sCount  b  false (a=b) codec
        handleSizeableType (GetTypeUperRange t.Kind t.Constraints r) s1 s2 s3
    | Enumerated(items) -> 
        let nMin = 0I
        let nMax = BigInteger(Seq.length items) - 1I
        
        let arrItems = 
            match items |> Seq.forall(fun x -> x._value.IsSome) with
            | true  -> items |> Seq.sortBy(fun x -> (Ast.GetValueAsInt x._value.Value r))  |> Seq.mapi(fun i item -> c_src.uper_Enumerated_item pp (item.CEnumName r C) (BigInteger i) nMax codec)
            | false -> items |> Seq.mapi(fun i item -> c_src.uper_Enumerated_item pp (item.CEnumName r C) (BigInteger i) nMax codec)
        c_src.uper_Enumerated pp arrItems errCode nMax codec
    | IA5String | NumericString -> 
        let getIndexNameByPath (path:string list) =
            "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
        let index = getIndexNameByPath path
        let alphaCons = t.Constraints |> List.filter(fun x -> match x with AlphabetContraint(_) -> true |_ -> false)
        let encInternalItem, min, max = EmitInternalItem_min_max t sTasName path m r codec
        let s1 a  = c_src.uper_str_FixedSize pp index encInternalItem a  codec 
        let s2 a b=  c_src.uper_str_VarSize pp index encInternalItem a b (GetCount t p r) codec 
        let s3 a b=  
            let sCount = GetCount t p r
            let level = BigInteger ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1)
            c_src.Fragmentation_sqf pp false level encInternalItem sCount  max  true (a=b) codec
        handleSizeableType (GetTypeUperRange t.Kind t.Constraints r) s1 s2 s3
    | NullType                  -> c_src.Null p codec
    | Choice(children)  -> 
        let nMin = 0I
        let nMax = BigInteger(Seq.length children) - 1I
        let nBits = (GetNumberOfBitsForNonNegativeInteger (nMax-nMin))
        let printChild (i:int) (c:ChildInfo) =
            let newPath = path@[c.Name.Value]
            let sChildContent = EmitTypeBody c.Type sTasName (newPath, None) m r codec 
            c_src.uper_Choice_child pp (c.CName_Present C) (BigInteger i) nMax sChildContent  codec
        let arrChildren = children |> Seq.mapi printChild
        c_src.uper_Choice p arrChildren nMax errCode codec
    | BitString->
        let s1 a   = c_src.uper_bitString_FixSize pp a codec 
        let s2 a b = c_src.uper_bitString_VarSize pp a b codec 
        let s3 a b = 
            let sCount = GetCount t pp r
            let level = BigInteger ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1)
            c_src.Fragmentation_sqf pp true level "" sCount b false (a=b) codec 
        handleSizeableType (GetTypeUperRange t.Kind t.Constraints r) s1 s2 s3



let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) codec =
    let AddIfNotPresent  item lst =
        match lst |> Seq.exists ( (=) item) with
        | true  -> lst
        | false -> item::lst
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
        match t.Kind with
        | SequenceOf(_) | OctetString | BitString | IA5String | NumericString-> 
            let index = ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1)
            let s1 = (SEQUENCE_OF_INDEX index)::state
            let s2 =
                match (GetTypeUperRange t.Kind t.Constraints r) with
                | Concrete(a,b) when b<65536I && a=b   -> s1
                | Concrete(a,b) when b<65536I && a<>b  -> 
                    if codec = Decode then LENGTH::s1 else s1
                | Concrete(a,b)     -> s1
//                    let s0 = NCOUNT::CUR_BLOCK_SIZE::CUR_ITEM::s1
//                    let s1 = match t.Kind with
//                                   | SequenceOf(_) | OctetString | BitString  -> if a<>b && codec = Decode then  LENGTH::s0 else s0
//                                   | _                                        -> s0
//                    if codec = Decode then (SEQUENCE_OF_INDEX (1,false))::LEN2::s1 else s1
                | _                 -> raise(BugErrorException "")
            s2
        | Integer   when codec = Decode     ->
            let rootCons = t.Constraints |> Seq.filter(fun x -> match x with RootConstraint(a) |RootConstraint2(a,_) -> true |_ -> false) 
            match (Seq.isEmpty rootCons) with
            | true  -> state
            | false -> EXTENSION_BIT::state
        | Enumerated(_)     -> 
            match codec with
            | Encode    -> state
            | Decode    -> AddIfNotPresent (ENUM_IDX UINT) state
        | Choice(children) when codec = Decode -> AddIfNotPresent CHOICE_IDX state            
        | Sequence(children)    when codec = Decode -> 
            let sBitMaskName = (TypeLongName path) + "bitMask"
            let nOptChildren = children |> Seq.filter(fun x -> not x.AcnInsertedField) |> Seq.filter(fun x -> x.Optionality.IsSome) |> Seq.length
            let nSize = BigInteger (System.Math.Ceiling( (float nOptChildren) / 8.0))
            if nOptChildren = 0 then
                state
            else
                (SEQUENCE_BitMask( sBitMaskName, nSize))::state
        | _             -> state

    let lvs = VisitType t [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []
    let emitLocalVariable = function
        | SEQUENCE_OF_INDEX(i) -> c_src.Emit_local_variable_SQF_Index (BigInteger i) 
        | EXTENSION_BIT     -> "" //su.Declare_ExtensionBit()
        | LENGTH            -> c_src.Declare_Length()
        | ENUM_IDX intType  -> 
            match intType with
            | Ast.UINT  -> c_acn.Declare_EnumValueUInt()
            | Ast.SINT  -> c_acn.Declare_EnumValueSInt()
        | CHOICE_IDX        -> c_src.Declare_ChoiceIndex()
        | SEQUENCE_BitMask(b,i) -> c_src.Declare_SequenceBitMask b i
        | CHAR_VAL          -> "" //su.Declare_CharValue()
        | NCOUNT            -> "" //su.Declare_nCount()
        | CUR_BLOCK_SIZE    -> "" //su.Declare_curBlockSize()
        | CUR_ITEM          -> "" //su.Declare_curItem()
        | LEN2              -> "" //su.Declare_len2()
        | REF_TYPE_PARAM(_) -> raise(BugErrorException(""))

    //let emitLocalVariable xx = ""
    lvs |> List.map emitLocalVariable


let EmitTypeAss (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot)  codec = 
    let sTasName = tas.GetCName r.TypePrefix
    let sStar = (TypeStar tas.Type r)
    let sTypeBody = EmitTypeBody tas.Type sTasName ([m.Name.Value; tas.Name.Value], None) m r codec
    let localVars = CollectLocalVars tas.Type tas m r codec
    c_src.PrintUper sTasName sStar localVars sTypeBody codec
    


