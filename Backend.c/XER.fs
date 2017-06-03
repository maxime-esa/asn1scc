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

module c_XER

open System.Numerics
open FsUtils
open CommonTypes
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open c_utils

let quote (s:string) = 
    if s.StartsWith("\"") then s else (("\"" + s) + "\"")

let rec XerTag (t:Asn1Type) (r:AstRoot) =
    let result  = XER_bl.XerTag t r
    quote result

type SequenceEncStatement =
    | StartTag
    | EndTag
    | SeqChild of ChildInfo

let rec EmitTypeBody (t:Asn1Type) (sTag:string) (nLevel:BigInteger) (sTasName:string) (path:list<string>, altPath:(string*string) option  )  (m:Asn1Module) (r:AstRoot)  codec =
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
        

    let errCode = 
        match (GetTypeConstraintsErrorCode t.Constraints path r) with
        | None  -> "0"
        | Some(errCodeName) ->    errCodeName
    let isFixedSize () =
        match (GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b) -> a=b
        | _             -> false
        
    match t.Kind with
    | Integer   -> xer.Integer p sTag nLevel codec
    | Boolean -> xer.BOOLEAN p sTag nLevel codec
    | Real    -> xer.REAL p sTag nLevel codec
    | ReferenceType(modName,tasName, _)    ->
        let ptr = (GetTypeAccessPathPtr path  r)
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        xer.ReferenceType ptr tsName sTag codec
    | IA5String | NumericString -> 
        xer.IA5String p sTag nLevel codec
    | OctetString   ->
        xer.OctetString pp sTag nLevel (GetCount t pp r) (isFixedSize ()) codec
    | NullType                  -> xer.NULL () codec
    | BitString->
        xer.BitString pp sTag nLevel (GetCount t pp r) (isFixedSize ()) codec
    | Enumerated(items) -> 
        let handleItem (i:int) (it:NamedItem) =
            xer.ENUMERATED_item pp sTag nLevel (it.CEnumName r C) it.Name.Value (i=0) codec
        let arrItems = items |> Seq.mapi handleItem
        xer.ENUMERATED pp sTag nLevel arrItems codec
    | SequenceOf(child) ->
        let getIndexNameByPath (path:string list) =
            "i" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
        let index = getIndexNameByPath path
        let sChild = EmitTypeBody child  (XerTag child r) (nLevel + 1I) sTasName (path@["#"], None) m r codec
        xer.SequenceOf p sTag nLevel index (GetCount t pp r) sChild (isFixedSize ()) codec 
    | Choice(children)  -> 
        let HandlChild (i:int) (c:ChildInfo) =
            let sChild = EmitTypeBody c.Type  (quote c.Name.Value) (nLevel + 1I) sTasName (path@[c.Name.Value], None) m r codec
            xer.CHOICE_child pp (c.CName_Present C) sChild (i=0) c.Name.Value codec
        let no_tag_body = xer.CHOICE_no_tag p (children |> Seq.mapi HandlChild) codec
        match sTag with
        | null | "" -> no_tag_body
        | _         -> xer.CHOICE p sTag nLevel no_tag_body codec
    | Sequence(children)    ->
        let asn1Children = children |> List.filter(fun x -> not x.AcnInsertedField)

        let encodedItems = (StartTag::(asn1Children |> List.map (fun c -> SeqChild c)))@[EndTag]

        let printChild encStatement sNestedContent = 
            let content = 
                match encStatement with
                | StartTag     -> xer.SEQUENCE_start sTag nLevel codec
                | EndTag      -> xer.SEQUENCE_end sTag nLevel codec
                | SeqChild(c)  ->
                    let childPath =  path@[c.Name.Value]
                    let sChildContent = EmitTypeBody c.Type (quote c.Name.Value) (nLevel + 1I) sTasName (path@[c.Name.Value], None) m r codec
                    match c.Optionality with
                    |None                 ->  
                        xer.Sequence_mandatory_child (c.CName ProgrammingLanguage.C) sChildContent c.Name.Value codec
                    |Some(_)        ->
                        xer.Sequence_optional_child pp (c.CName ProgrammingLanguage.C) sChildContent c.Name.Value codec
            c_src.JoinItems content sNestedContent 

        let  printChildren (lst:list<SequenceEncStatement>)= 
            let rec printChildrenAux = function
                |[]     -> null
                |x::xs  -> printChild x  (printChildrenAux xs )
            printChildrenAux lst 

        xer.SEQUENCE_xer (printChildren encodedItems)  codec 



let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) codec =
    let AddIfNotPresent  item lst =
        match lst |> Seq.exists ( (=) item) with
        | true  -> lst
        | false -> item::lst
    let rec OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
        match t.Kind with
        | SequenceOf(_)  -> 
            let index = ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1)
            let s1 = (SEQUENCE_OF_INDEX index)::state
            s1
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
    let sTypeBody = EmitTypeBody tas.Type (quote tas.Name.Value) 0I sTasName ([m.Name.Value; tas.Name.Value], None) m r codec
    let localVars = CollectLocalVars tas.Type tas m r codec
    let a1 = xer.PrintTas sTasName sStar localVars sTypeBody codec
    let sTypeBody2 = EmitTypeBody tas.Type "xmlTag" 0I sTasName ([m.Name.Value; tas.Name.Value], None) m r codec
    let a2 = xer.PrintTasWithTag sTasName sStar localVars sTypeBody2 codec
    [a1;a2] |> Seq.StrJoin "\n\n"
    




