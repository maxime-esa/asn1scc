module c_utils



open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree

open Ast


let TypeItemsCount (t:Asn1Type) (r:AstRoot)=  
    match (GetTypeUperRange t.Kind t.Constraints r) with
    |Concrete(_, max)        -> max
    |_                       -> raise(BugErrorException "SEQUENCE OF or OCTET STRING etc has no constraints")


let rec TypeCArrayItemsCount (t:Asn1Type) (r:AstRoot)=  
    match t.Kind with
    | BitString(_)  -> BigInteger(System.Math.Ceiling(float(TypeItemsCount t r)/8.0))
    | IA5String | NumericString     -> (TypeItemsCount t r) + 1I
    | SequenceOf(_) | OctetString   -> TypeItemsCount t r
    | ReferenceType(_)  ->
        let basetype = Ast.GetBaseTypeConsIncluded t r
        TypeCArrayItemsCount basetype r
    |_                       -> raise(BugErrorException "TypeCArrayItemsCount called for a non sizeable type")





let TypeArrayPostfix (t:Asn1Type) (r:AstRoot)= 
    match t.Kind with
    | IA5String | NumericString     -> c_lib.PrintArrayPostfix (TypeCArrayItemsCount t r)
    | ReferenceType(refCon, _, _)      -> "" 
    | _                             -> ""

let rec TypeStar (t:Asn1Type) (r:AstRoot)= 
    match t.Kind with
    | IA5String | NumericString -> ""
    | ReferenceType(_)   -> TypeStar (Ast.GetActualType t r) r
    | _                  -> "*"



let TypeLongName (p:list<string>) =
    let keyAsStr = p.Tail
    ToC (keyAsStr.StrJoin("_").Replace("#","elem"))



type LOCAL_VARIABLE =
    | SEQUENCE_OF_INDEX of int
    | LENGTH
    | EXTENSION_BIT
    | ENUM_IDX
    | CHOICE_IDX
    | SEQUENCE_BitMask  of string*BigInteger
    | REF_TYPE_PARAM   of string*string
    | CHAR_VAL
    | NCOUNT
    | CUR_BLOCK_SIZE
    | CUR_ITEM
    | LEN2



(* 
This function must be called for an ASN.1 type only.
Not an ACN inserted type, parameter or tmp type
*)
let rec GetTypeAccessPathPriv (pVal:string) (path:list<string>) (r:AstRoot) =
//    let pVal   = "pVal" // ideally these 3 values should be taken from string template
    let arr    = "arr"
    let u      = "u"
    let t = Ast.GetTypeByAbsPath path r

    match path with
    | []                   -> raise(BugErrorException "InvalidPath")
    | modName::[]          -> raise(BugErrorException "InvalidPath")
    | modName::tasName::[] -> 
        match (Ast.GetActualType t r).Kind with
        | Integer | Real | Boolean | Enumerated(_) | NullType                             -> "*"+pVal
        | IA5String | NumericString                                                       -> pVal
        | Sequence(_)  | Choice(_) | SequenceOf(_) | BitString(_) | OctetString(_)        -> pVal+"->"
        | ReferenceType(_)    -> raise(BugErrorException "")
    | modName::tasName::restPath  ->
        let rec GetDot (t:Asn1Type) =
            match t.Kind with
            | Integer| Real | Boolean| Enumerated(_)| NullType | IA5String | NumericString          -> ""
            | Sequence(_) | Choice(_) | SequenceOf(_) | BitString(_) | OctetString(_)               ->"."
            | ReferenceType(refCon, _, _)   -> GetDot (Ast.GetActualType t r)
        let reversePath = path |> List.rev
        let parPath = reversePath.Tail |> List.rev
        let myFldName = reversePath.Head
        let parResult = GetTypeAccessPathPriv pVal parPath r
        let parent = Ast.GetTypeByAbsPath parPath r
        let result = 
            match (Ast.GetActualType parent r).Kind with
            | SequenceOf(_)      -> 
                let i = path |> Seq.filter ((=) "#") |> Seq.length
                parResult+ arr+"[i" + i.ToString() + "]"
            | Sequence(children) -> 
                match children |> Seq.tryFind(fun ch -> ch.Name.Value = myFldName) with
                | Some ch   -> parResult + (ch.CName ProgrammingLanguage.C)
                | None      -> parResult + (ToC myFldName)
            | Choice(children)   -> 
                match children |> Seq.tryFind(fun ch -> ch.Name.Value = myFldName) with
                | Some ch       -> parResult+u+"." + (ch.CName ProgrammingLanguage.C)
                | None          -> parResult+u+"." + (ToC myFldName)
            |   _       -> raise (BugErrorException(""))
        result + GetDot(t)



let rec GetTypeAccessPathPrivPtr (pVal:string) (path:list<string>) (r:AstRoot) =
    let ret = (GetTypeAccessPathPriv pVal path r).TrimEnd('.')
    if ret.StartsWith("*") then
        ret.Substring(1)
    else
        if ret.EndsWith("->") then
            ret.TrimEnd('-','>')
        else
            let t = Ast.GetTypeByAbsPath path r
            match (Ast.GetActualType t r).Kind with
            | IA5String | NumericString -> ret
            | _                         -> "&"+ret



(* 
This function must be called for an ASN.1 type only.
Not an ACN inserted type, parameter or tmp type
*)

let GetCount (t:Asn1Type) (path:string) (r:AstRoot) =
    let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
    match t.Kind with
    | IA5String | NumericString                                     -> c_src.getStringSize path
    | BitString(_) | OctetString | SequenceOf(_) when min=max       -> min.ToString() 
    | BitString(_) | OctetString | SequenceOf(_)                    -> c_src.getSizeableSize path
    | _                                                             -> raise(BugErrorException "")


let GetConstraintTypeAccessPath (path:list<string>) (t:ConstraintType) (r:AstRoot)  = 
    let pVal = "pVal"
    let accessFld = GetTypeAccessPathPriv pVal path r

    match t with
    | Same(_)       ->  accessFld
    | LengthOf(tp) ->
        match (GetActualType tp r).Kind with
        | IA5String | NumericString -> c_src.getStringSize(accessFld)
        | OctetString | BitString | SequenceOf(_)   -> GetCount tp accessFld  r//c_src.getSizeableSize accessFld
        | _                                         -> raise(BugErrorException "Invalid combination type/constraint")
    | AlphabetOf(tp) ->
        match (GetActualType tp r).Kind with
        | IA5String | NumericString -> c_src.Print_AlphabetCheckFunc_str accessFld
        | _                          -> raise(BugErrorException "Invalid combination type/constraint")


let GetConstraintTypeAccessPathPtr (path:list<string>) (t:ConstraintType) (r:AstRoot)  = 
    let pVal = "pVal"
    let accessFld = GetTypeAccessPathPrivPtr pVal path r

    match t with
    | Same(_)        -> accessFld
    | LengthOf(tp)   -> raise(BugErrorException "")
    | AlphabetOf(tp) -> raise(BugErrorException "")

        
let GetTypeAccessPath (path:list<string>) (r:AstRoot)  = 
    GetTypeAccessPathPriv "pVal" path  r

let GetTypeAccessPathPtr (path:list<string>) (r:AstRoot)  = 
    GetTypeAccessPathPrivPtr "pVal" path  r

let GetParameterAccessPath (prm:AcnTypes.AcnParameter)  (r:AstRoot) =
    let asn1Type = Ast.AcnAsn1Type2Asn1Type prm.Asn1Type
    let star = 
        match prm.Mode with
        | AcnTypes.DecodeMode       -> ""
        | AcnTypes.EncodeDecodeMode -> (TypeStar asn1Type r)
    star + (ToC (prm.Name))

let GetParameterAccessPathPtr (prm:AcnTypes.AcnParameter)  (r:AstRoot) =
    (ToC (prm.Name))




let GetPointAccessPath (p:AcnTypes.Point) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    match p with
    | AcnTypes.TypePoint(absPath)   ->    
        match absPath with
        | mdName::tsName::ch::restPath -> 
            let parPath = absPath |> List.rev |> List.tail |> List.rev
            let chName = absPath |> List.rev |> List.head
            let parType = Ast.GetActualType (Ast.GetTypeByAbsPath parPath r) r
            match parType.Kind with
            | Sequence(children)    ->
                let thisChild = children |> Seq.find(fun x -> x.Name.Value = chName)
                match thisChild.AcnInsertedField with
                | false -> GetTypeAccessPath absPath  r
                | true  -> thisChild.CName ProgrammingLanguage.C
            | _                     -> GetTypeAccessPath absPath  r
        | _                       -> GetTypeAccessPath absPath  r
    | AcnTypes.ParamPoint(absPath)  ->    
        match absPath with
        | m::t::prmName::[]   -> 
            let prm = acn.Parameters |> Seq.find(fun x -> x.ModName = m && x.TasName = t && x.Name = prmName)
            GetParameterAccessPath prm r
        | _                   -> raise(BugErrorException "Invalid path for Parameter")
    | AcnTypes.TempPoint(absPath)   ->    
        match absPath with
        | x ::[]        -> ToC x
        | m::t::x::xs   -> ToC x
        | _             -> raise(BugErrorException "")


let GetAsn1TypeByPoint (p:AcnTypes.Point) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    match p with
    | AcnTypes.TypePoint(pth)    -> Ast.GetTypeByAbsPath pth r
    | AcnTypes.ParamPoint(pth)   -> 
        match pth with
        | m::t::prmName::[]   -> 
            let prm = acn.Parameters |> Seq.find(fun x -> x.ModName = m && x.TasName = t && x.Name = prmName)
            Ast.AcnAsn1Type2Asn1Type prm.Asn1Type
        | _                   -> raise (BugErrorException "Invalid path")
    | AcnTypes.TempPoint(pth)    -> 
        match pth with
        | m::t::tmpName::[]   -> 
            let tmpType = acn.TmpTypes |> Seq.find(fun x -> x.ModName = m && x.TasName = t && x.Name = tmpName)
            Ast.AcnAsn1Type2Asn1Type tmpType.Asn1Type
        | _                   -> raise (BugErrorException "Invalid path")

let GetPointAccessPathPtr (p:AcnTypes.Point) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    match p with
    | AcnTypes.TypePoint(absPath)   ->    
        match absPath with
        | mdName::tsName::ch::restPath -> 
            let parPath = absPath |> List.rev |> List.tail |> List.rev
            let chName = absPath |> List.rev |> List.head
            let parType = Ast.GetActualType (Ast.GetTypeByAbsPath parPath r) r
            match parType.Kind with
            | Sequence(children)    ->
                let thisChild = children |> Seq.find(fun x -> x.Name.Value = chName)
                match thisChild.AcnInsertedField with
                | false -> GetTypeAccessPathPtr absPath  r
                | true  -> match (Ast.GetActualType thisChild.Type r).Kind with
                           | IA5String | NumericString  -> thisChild.CName ProgrammingLanguage.C
                           | _                          -> "&" + (thisChild.CName ProgrammingLanguage.C)
            | _                     -> GetTypeAccessPathPtr absPath  r
        | _                       -> GetTypeAccessPathPtr absPath  r
    | AcnTypes.ParamPoint(absPath)  ->    
        match absPath with
        | m::t::prmName::[]   -> 
            let prm = acn.Parameters |> Seq.find(fun x -> x.ModName = m && x.TasName = t && x.Name = prmName)
            GetParameterAccessPathPtr prm r
        | _                   -> raise(BugErrorException "Invalid path for Parameter")
    | AcnTypes.TempPoint(absPath)   ->  
        match absPath with
        | m::t::tmpName::xs   -> 
            let tmpType = acn.TmpTypes |> Seq.find(fun x -> x.ModName = m && x.TasName = t && x.Name = tmpName)
            let actAsn1Type = Ast.GetActualType (Ast.AcnAsn1Type2Asn1Type tmpType.Asn1Type) r
            match actAsn1Type.Kind with
            | IA5String | NumericString  -> (ToC tmpType.Name)
            | _                          -> "&" + (ToC tmpType.Name)
        | _             -> raise(BugErrorException "")

