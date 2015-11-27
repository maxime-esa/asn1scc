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

module Acn

open System.Numerics
open FsUtils
open AcnTypes
open Ast
open VisitTree


let rec GetAlignment (t:Asn1Type) (asn1:Ast.AstRoot)  =
    match t.AcnProperties |> List.choose(fun x -> match x with Aligment(al) -> Some al | _ -> None ) with
    | hd::hx   -> Some hd
    | []       -> None

let rec GetBooleanEncoding (t:Asn1Type) (asn1:Ast.AstRoot)  =
    match t.AcnProperties |> List.choose(fun x -> match x with BooleanEncoding(a) -> Some a | _ -> None ) with
    | hd::_   -> hd
    | []      -> TrueValue "1".AsLoc


let rec GetNullEncodingValue(t:Asn1Type) (asn1:Ast.AstRoot)   =
    match t.AcnProperties |> List.choose(fun x -> match x with AcnTypes.NullValue(a) -> Some a | _ -> None ) with
    | hd::_   -> Some hd.Value
    | []      -> None

let rec GetEndianess (t:Asn1Type) (asn1:Ast.AstRoot)   =
    match t.AcnProperties |> List.choose(fun x -> match x with Endianness(a) -> Some a | _ -> None ) with
    | hd::_   -> hd
    | []      -> AcnTypes.endianness.BigEndianness


let rec isEnumEncodingValues (t:Asn1Type) (asn1:Ast.AstRoot)   =
    t.AcnProperties |> List.exists(fun x -> match x with EncodeValues -> true | _ -> false ) 

let GetEncodingProperty (a:Asn1Type) (asn1:Ast.AstRoot)   =
    match a.AcnProperties |> List.choose(fun x -> match x with Encoding(a) -> Some a | _ -> None ) with
    | hd::_ -> Some hd
    | []    -> None



type IntEncodingClass =
    |Integer_uPER
    |PositiveInteger_ConstSize_8
    |PositiveInteger_ConstSize_big_endian_16
    |PositiveInteger_ConstSize_little_endian_16
    |PositiveInteger_ConstSize_big_endian_32
    |PositiveInteger_ConstSize_little_endian_32
    |PositiveInteger_ConstSize_big_endian_64
    |PositiveInteger_ConstSize_little_endian_64
    |PositiveInteger_ConstSize of BigInteger
    |PositiveInteger_VarSize_LengthEmbedded
    |TwosComplement_ConstSize_8
    |TwosComplement_ConstSize_big_endian_16
    |TwosComplement_ConstSize_little_endian_16
    |TwosComplement_ConstSize_big_endian_32
    |TwosComplement_ConstSize_little_endian_32
    |TwosComplement_ConstSize_big_endian_64
    |TwosComplement_ConstSize_little_endian_64
    |TwosComplement_ConstSize of BigInteger
    |TwosComplement_VarSize_LengthEmbedded
    |ASCII_ConstSize of BigInteger
    |ASCII_VarSize_LengthEmbedded
    |ASCII_VarSize_NullTerminated of byte
    |BCD_ConstSize of BigInteger
    |BCD_VarSize_LengthEmbedded
    |BCD_VarSize_NullTerminated of byte

type SizeableEncodingClass =
    | FixedSize of BigInteger
    | AutoSize  
    | ExternalField of AcnTypes.Point
    | NullTerminated of byte

type StringEncodingClassKind =
    | Acn_Enc_String_Ascii_FixSize                                                           //
    | Acn_Enc_String_Ascii_Null_Teminated                   of byte                          //null character
    | Acn_Enc_String_Ascii_External_Field_Determinant       of AcnTypes.Point                //external field
    | Acn_Enc_String_Ascii_Internal_Field_Determinant       of BigInteger*BigInteger         //asn1 min value, internal length determinant size in bits
    | Acn_Enc_String_CharIndex_FixSize                      of char[]                        //allowed char set
    | Acn_Enc_String_CharIndex_External_Field_Determinant   of char[]*AcnTypes.Point         //allowed char set, external field
    | Acn_Enc_String_CharIndex_Internal_Field_Determinant   of char[]*BigInteger*BigInteger  //allowed char set, asn1 min value, internal length determinant size in bits
    with 
        member x.IsAsccii =
            match x with
            | Acn_Enc_String_Ascii_FixSize                           -> true
            | Acn_Enc_String_Ascii_Null_Teminated                 _  -> true
            | Acn_Enc_String_Ascii_External_Field_Determinant     _  -> true
            | Acn_Enc_String_Ascii_Internal_Field_Determinant     _  -> true
            | Acn_Enc_String_CharIndex_FixSize                    _  -> false
            | Acn_Enc_String_CharIndex_External_Field_Determinant _  -> false
            | Acn_Enc_String_CharIndex_Internal_Field_Determinant _  -> false
        member x.IsExtField =
            match x with
            | Acn_Enc_String_Ascii_FixSize                           -> false
            | Acn_Enc_String_Ascii_Null_Teminated                 _  -> false
            | Acn_Enc_String_Ascii_External_Field_Determinant     _  -> true
            | Acn_Enc_String_Ascii_Internal_Field_Determinant     _  -> false
            | Acn_Enc_String_CharIndex_FixSize                    _  -> false
            | Acn_Enc_String_CharIndex_External_Field_Determinant _  -> true
            | Acn_Enc_String_CharIndex_Internal_Field_Determinant _  -> false

type StringEncodingClass = {
    kind : StringEncodingClassKind
    maxAsn1SizeValue : BigInteger
    maxSizeInBits    : BigInteger
    minSizeInBits    : BigInteger
    characterSizeInBits : BigInteger
}


type sizePropertyPriv =
    | SP_Fixed          of int
    | SP_NullTerminated of byte

///helper function
let sizeToPriv sizeProperty (acn:AcnTypes.AcnAstResolved)=
    match sizeProperty with
    | AcnTypes.sizeProperty.Fixed(c)            -> SP_Fixed (int (AcnTypes.EvaluateConstant acn.Constants c))
    | AcnTypes.sizeProperty.NullTerminated  b    -> SP_NullTerminated b


let GetSizeProperty  (a:Asn1Type) encProperty (acn:AcnTypes.AcnAstResolved) =
    match a.AcnProperties |> List.choose(fun x -> match x with SizeProperty(a) -> Some a | _ -> None ) with     
    | hd::_ -> (sizeToPriv hd acn)
    | []    -> raise(BugErrorException "mandatory property missing")

let tryGetSizeProperty  (a:Asn1Type) (acn:AcnTypes.AcnAstResolved) =
    match a.AcnProperties |> List.choose(fun x -> match x with SizeProperty(a) -> Some a | _ -> None ) with     
    | hd::_ -> Some (sizeToPriv hd acn)
    | []    -> None


let GetIntEncodingClass (a:Asn1Type) (asn1:Ast.AstRoot) (acn:AcnTypes.AcnAstResolved) errLoc =
    let acnEncodingClass() =
        let endianess = GetEndianess a asn1
        let encProp = (GetEncodingProperty a asn1).Value
        let sizeProp = GetSizeProperty a encProp acn
        match encProp, sizeProp, endianess with
        | PosInt, SP_Fixed(8) , BigEndianness               ->  PositiveInteger_ConstSize_8
        | PosInt, SP_Fixed(16), BigEndianness               ->  PositiveInteger_ConstSize_big_endian_16
        | PosInt, SP_Fixed(16), LittleEndianness            ->  PositiveInteger_ConstSize_little_endian_16
        | PosInt, SP_Fixed(32), BigEndianness               ->  PositiveInteger_ConstSize_big_endian_32
        | PosInt, SP_Fixed(32), LittleEndianness            ->  PositiveInteger_ConstSize_little_endian_32
        | PosInt, SP_Fixed(64), BigEndianness               ->  PositiveInteger_ConstSize_big_endian_64
        | PosInt, SP_Fixed(64), LittleEndianness            ->  PositiveInteger_ConstSize_little_endian_64
        | PosInt, SP_Fixed(fxVal) , BigEndianness           ->  PositiveInteger_ConstSize (BigInteger fxVal)
        | PosInt, SP_NullTerminated _, _                      ->  raise(SemanticError(errLoc, "Acn properties pos-int and null-terminated are mutually exclusive"))
        | TwosComplement, SP_Fixed(8) , BigEndianness       ->  TwosComplement_ConstSize_8
        | TwosComplement, SP_Fixed(16), BigEndianness       ->  TwosComplement_ConstSize_big_endian_16
        | TwosComplement, SP_Fixed(16), LittleEndianness    ->  TwosComplement_ConstSize_little_endian_16
        | TwosComplement, SP_Fixed(32), BigEndianness       ->  TwosComplement_ConstSize_big_endian_32
        | TwosComplement, SP_Fixed(32), LittleEndianness    ->  TwosComplement_ConstSize_little_endian_32
        | TwosComplement, SP_Fixed(64), BigEndianness       ->  TwosComplement_ConstSize_big_endian_64
        | TwosComplement, SP_Fixed(64), LittleEndianness    ->  TwosComplement_ConstSize_little_endian_64
        | TwosComplement, SP_Fixed(fxVal) , BigEndianness   ->  TwosComplement_ConstSize (BigInteger fxVal)
        | TwosComplement, SP_NullTerminated _, _            ->  raise(SemanticError(errLoc, "Acn properties twos-complement and null-terminated are mutually exclusive"))
        | Ascii, SP_Fixed(fxVal) , BigEndianness            ->  ASCII_ConstSize  (BigInteger fxVal)
        | BCD, SP_Fixed(fxVal) , BigEndianness              ->  BCD_ConstSize (BigInteger fxVal)
        | BCD, SP_NullTerminated b, BigEndianness           ->  BCD_VarSize_NullTerminated b
        | Ascii, SP_NullTerminated b, BigEndianness         ->  ASCII_VarSize_NullTerminated b
        | _, SP_NullTerminated _, _                         ->  raise(SemanticError(errLoc, "null-terminated can be applied only for ASCII or BCD encodings"))
        | _, _ , LittleEndianness                           ->  raise(SemanticError(errLoc, "Little endian can be applied only for fixed size encodings and size must be 16 or 32 or 64"))
        | IEEE754_32, _, BigEndianness                      ->  raise(SemanticError(errLoc, "invalid encoding value (choose one of pos-int, twos-complement, ascii, BCD)"))
        | IEEE754_64, _, BigEndianness                      ->  raise(SemanticError(errLoc, "invalid encoding value (choose one of pos-int, twos-complement, ascii, BCD)"))

    // if the mandatory property size is missing => the type will be encoded like uPER        
    match a.AcnProperties |> List.exists(fun x -> match x with SizeProperty(_) -> true | _ -> false ) with     
    | false -> Integer_uPER
    | true  -> acnEncodingClass()

  

let GetSizeableEncodingClass_ (a:Asn1Type) (absPath:AcnTypes.AbsPath) (asn1:Ast.AstRoot) (acn:AcnTypes.AcnAstResolved) errLoc =
    let rec GetSizePropertyAux  (kind:Asn1TypeKind) cons  props =
        match kind with
        | OctetString | BitString(_) | SequenceOf(_)->
            match props |> List.choose(fun x -> match x with SizeProperty(a) -> Some a | _ -> None ) with     
            | hd::_ -> match hd with
                        | AcnTypes.sizeProperty.Fixed(c)            -> FixedSize (AcnTypes.EvaluateConstant acn.Constants c)
                        | AcnTypes.sizeProperty.NullTerminated  b   -> NullTerminated b
            | []    -> 
                match acn.References |> Seq.tryFind(fun x -> x.decType.AbsPath = absPath && x.Kind = AcnTypes.SizeDeterminant) with
                | Some(r)       ->  ExternalField (r.determinant)
                | None          ->  AutoSize
        | _     -> raise(BugErrorException "GetSizeableEncodingClass: Invalid function call")
    GetSizePropertyAux a.Kind a.Constraints a.AcnProperties


let GetStringEncodingClass (a:Asn1Type) (absPath:AcnTypes.AbsPath) (asn1:Ast.AstRoot) (acn:AcnTypes.AcnAstResolved) errLoc =
    let GetStringEncodingClassAux  (kind:Asn1TypeKind) cons  (props:AcnProperty list) =
        match kind with
        | IA5String | NumericString ->
            let asn1Min, asn1Max = uPER.GetSizebaleMinMax a.Kind a.Constraints asn1
            let bAsn1FixedSize = asn1Min = asn1Max
            let bAsciiEncoding =
                match GetEncodingProperty a asn1 with
                | Some Ascii     -> true
                | _              -> false
            
            let sizeClass = 
                match props |> List.choose(fun x -> match x with SizeProperty(a) -> Some a | _ -> None ) with     
                | hd::_ -> 
                    match hd with
                    | AcnTypes.sizeProperty.Fixed(c)            -> FixedSize (AcnTypes.EvaluateConstant acn.Constants c)
                    | AcnTypes.sizeProperty.NullTerminated b    -> NullTerminated b
                | []    -> 
                    match acn.References |> Seq.tryFind(fun x -> x.decType.AbsPath = absPath && x.Kind = AcnTypes.SizeDeterminant) with
                    | Some(r)       ->  ExternalField (r.determinant)
                    | None          ->  AutoSize

            let alphaCons = a.Constraints |> List.filter(fun x -> match x with AlphabetContraint(_) -> true |_ -> false)
            let alphaSet = uPER.GetTypeUperRangeFrom (a.Kind, a.Constraints, asn1)
            let allowedBytes = alphaSet |> Array.map(fun c -> (System.Text.Encoding.ASCII.GetBytes (c.ToString())).[0]) |> Set.ofArray
            let lengthDeterminantSize = GetNumberOfBitsForNonNegativeInteger (asn1Max-asn1Min)
            let charSizeInBits =
                match  bAsciiEncoding with
                | true      -> 8I
                | false     -> GetNumberOfBitsForNonNegativeInteger (BigInteger (alphaSet.Length - 1))
            let kind, minSizeInBits, maxSizeInBits = 
                match  bAsciiEncoding, bAsn1FixedSize, sizeClass  with
                | true, true, AutoSize                                          -> Acn_Enc_String_Ascii_FixSize, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
                | true, true, NullTerminated  b                                 -> 
                    match allowedBytes.Contains b && (not (b=0uy && alphaSet.Length = 128))with
                    | true  -> raise(SemanticError(errLoc, "The termination-pattern defines a character which belongs to the allowed values of the ASN.1 type. Use another value in the termination-pattern or apply different constraints in the ASN.1 type."))
                    | false -> Acn_Enc_String_Ascii_Null_Teminated b, (asn1Max+1I)*charSizeInBits, (asn1Max+1I)*charSizeInBits
                | true, true, FixedSize(nItems)    when nItems = asn1Max        -> Acn_Enc_String_Ascii_FixSize, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
                | true, true, FixedSize(nItems)                                 -> raise(BugErrorException(sprintf "size property value should be set to %A" asn1Max))
                | true, true, ExternalField fld                                 -> Acn_Enc_String_Ascii_External_Field_Determinant fld, asn1Max*charSizeInBits,  asn1Max*charSizeInBits

                | true, false, AutoSize                                         -> Acn_Enc_String_Ascii_Internal_Field_Determinant (asn1Min, lengthDeterminantSize), lengthDeterminantSize + asn1Min*charSizeInBits, lengthDeterminantSize + asn1Max*charSizeInBits
                | true, false, NullTerminated b                                 -> 
                    match allowedBytes.Contains b && (not (b=0uy && alphaSet.Length = 128))with
                    | true  -> raise(SemanticError(errLoc, "The termination-pattern defines a character which belongs to the allowed values of the ASN.1 type. Use another value in the termination-pattern or apply different constraints in the ASN.1 type."))
                    | false -> Acn_Enc_String_Ascii_Null_Teminated b, (asn1Max+1I)*charSizeInBits, (asn1Max+1I)*charSizeInBits
                | true, false, FixedSize(nItems)                                -> raise(BugErrorException(sprintf "The size constraints of the ASN.1  allows variable items (%A .. %A). Therefore, you should either remove the size property (in which case the size determinant will be encoded automatically exactly like uPER), or use a an Integer field as size determinant" asn1Min asn1Max))
                | true, false, ExternalField fld                                -> Acn_Enc_String_Ascii_External_Field_Determinant fld, asn1Max*charSizeInBits,  asn1Max*charSizeInBits

                | false, true, AutoSize                                         -> Acn_Enc_String_CharIndex_FixSize alphaSet, asn1Max*charSizeInBits,  asn1Max*charSizeInBits 
                | false, true, NullTerminated  _                                -> raise(BugErrorException(sprintf "when a string type has the acn property 'size null-terminated' it must also have the acn property 'encoding ASCII'" ))
                | false, true, FixedSize(nItems)    when nItems = asn1Max       -> Acn_Enc_String_CharIndex_FixSize alphaSet, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
                | false, true, FixedSize(nItems)                                -> raise(BugErrorException(sprintf "size property value should be set to %A" asn1Max))
                | false, true, ExternalField fld                                -> Acn_Enc_String_CharIndex_External_Field_Determinant (alphaSet,fld), asn1Max*charSizeInBits,  asn1Max*charSizeInBits

                | false, false, AutoSize                                        -> Acn_Enc_String_CharIndex_Internal_Field_Determinant (alphaSet, asn1Min, lengthDeterminantSize), lengthDeterminantSize + asn1Min*charSizeInBits, lengthDeterminantSize + asn1Max*charSizeInBits
                | false, false, NullTerminated  _                               -> raise(BugErrorException(sprintf "when a string type has the acn property 'size null-terminated' it must also have the acn property 'encoding ASCII'" ))
                | false, false, FixedSize(nItems)                               -> raise(BugErrorException(sprintf "The size constraints of the ASN.1  allows variable items (%A .. %A). Therefore, you should either remove the size property (in which case the size determinant will be encoded automatically exactly like uPER), or use a an Integer field as size determinant" asn1Min asn1Max))
                | false, false, ExternalField fld                               -> Acn_Enc_String_CharIndex_External_Field_Determinant (alphaSet, fld), asn1Min*charSizeInBits, asn1Max*charSizeInBits

            { 
                StringEncodingClass.kind = kind
                maxAsn1SizeValue = asn1Max
                maxSizeInBits    = maxSizeInBits
                minSizeInBits    = minSizeInBits
                characterSizeInBits = charSizeInBits
            }

        | _     -> raise(BugErrorException "GetStringEncodingClass: Invalid function call")
    GetStringEncodingClassAux a.Kind a.Constraints a.AcnProperties

    
type RealEncodingClass =
    | Real_uPER
    | Real_IEEE754_32_big_endian
    | Real_IEEE754_64_big_endian
    | Real_IEEE754_32_little_endian
    | Real_IEEE754_64_little_endian

let GetRealEncodingClass (a:Asn1Type)  (asn1:Ast.AstRoot) =
    match a.AcnProperties |> List.exists(fun x -> match x with Encoding(_) -> true | _ -> false ) with     
    | false     -> Real_uPER
    | true      ->
        let enc = (GetEncodingProperty a asn1).Value
        let endianess = GetEndianess a asn1
        match enc, endianess with
        | IEEE754_32, BigEndianness     -> Real_IEEE754_32_big_endian
        | IEEE754_64, BigEndianness     -> Real_IEEE754_64_big_endian
        | IEEE754_32, LittleEndianness  -> Real_IEEE754_32_little_endian
        | IEEE754_64, LittleEndianness  -> Real_IEEE754_64_little_endian
        | _,_                           -> raise(BugErrorException "")

let ChildHasPresenseDeterminant (parentPath:AcnTypes.AbsPath) (ch:ChildInfo) (acn:AcnTypes.AcnAstResolved) =
    let chPath = parentPath@[ch.Name.Value]
    acn.References |> Seq.exists(fun r-> r.decType.AbsPath = chPath && (match r.Kind with PresenceBool | PresenceInt(_) | PresenceStr(_) -> true |_ -> false)) 


type PresenseEncClass = 
    | LikeUPER
    | PresBool of Point
    | PresInt of Point*BigInteger
    | PresStr of Point*string
    
let GetPresenseEncodingClass (parentPath:AcnTypes.AbsPath) (ch:ChildInfo) (acn:AcnTypes.AcnAstResolved) =
    let chPath = parentPath@[ch.Name.Value]
    match ch.Optionality with
    | None | Some(AlwaysAbsent) | Some(AlwaysPresent)   -> None
    | _     ->
        let KindIsPresence = function
            | PresenceBool             -> true
            | PresenceInt(nVal)        -> true
            | PresenceStr(sVal)        -> true
            | _                        -> false
        match acn.References |> Seq.tryFind(fun r -> r.decType.AbsPath = chPath && (KindIsPresence r.Kind)) with
        | None          -> Some(LikeUPER)
        | Some(r)       -> match r.Kind with
                           | PresenceBool             -> Some (PresBool r.determinant)
                           | PresenceInt(nVal)        -> Some (PresInt (r.determinant, (AcnTypes.EvaluateConstant acn.Constants nVal)))
                           | PresenceStr(sVal)        -> Some (PresStr (r.determinant, sVal))
                           | _                        -> Some (LikeUPER)
type ChoiceEncClass =
    | EnumDeterminant of Point
    | PresentWhenOnChildren
  
let GetChoiceEncodingClass (choicePath:AcnTypes.AbsPath) (children:List<ChildInfo>) (acn:AcnTypes.AcnAstResolved) =
    match acn.References |> Seq.tryFind(fun r -> r.decType.AbsPath = choicePath) with
    | Some(r)  -> Some(EnumDeterminant r.determinant) 
    | None     -> match children |> Seq.forall(fun x -> ChildHasPresenseDeterminant choicePath x acn) with
                  | true  -> Some PresentWhenOnChildren
                  | false -> None
        

let GetPresenseConditions (parentPath:AcnTypes.AbsPath) (ch:ChildInfo) (acn:AcnTypes.AcnAstResolved) =
    let chPath = parentPath@[ch.Name.Value]
    seq {
        for cond in acn.References |> List.filter(fun r -> r.decType.AbsPath = chPath) do
            match cond.Kind with
            | PresenceBool             -> yield (PresBool cond.determinant)
            | PresenceInt(nVal)        -> yield (PresInt (cond.determinant, (AcnTypes.EvaluateConstant acn.Constants nVal)))
            | PresenceStr(sVal)        -> yield (PresStr (cond.determinant, sVal))
            | _                        -> ()
    }

let GetEnumEncodingValues (t:Asn1Type) (r:AstRoot) (lang:ProgrammingLanguage) (acn:AcnTypes.AcnAstResolved) = 
    match t.Kind with
    | Enumerated(items) ->
        match items |> Seq.forall(fun x -> x._value.IsSome) with
        | true  -> items |> List.mapi(fun idx itm -> (itm.CEnumName r lang), GetValueAsInt itm._value.Value r)
        | false -> items |> List.mapi(fun idx itm -> (itm.CEnumName r lang), BigInteger idx)
    | _                 -> raise(BugErrorException "")



let GetIntTypeFromEnum (t:Asn1Type) (asn1:Ast.AstRoot)  (acn:AcnTypes.AcnAstResolved) =
    match t.Kind with
    | Enumerated(items) ->
        let AsAsn1Val n = {Asn1Value.Kind = IntegerValue(IntLoc.ByValue n); Asn1Value.Location = emptyLocation}
        let Con =
            match isEnumEncodingValues t asn1 with
            | false -> 
                let nMax = BigInteger(Seq.length items) - 1I
                Ast.RangeContraint(AsAsn1Val 0I, AsAsn1Val nMax, true, true)
            | true  -> 
                let encVals = GetEnumEncodingValues t asn1 Spark acn |> List.map(fun (_,vl) -> AsAsn1Val vl)|> List.map SingleValueContraint
                match encVals with
                |hd::hs   -> hs|>Seq.fold(fun acc x -> UnionConstraint(acc,x,true) ) hd    
                | []      -> raise(BugErrorException("Empty enum"))
        {t with Kind = Integer; Constraints=[Con]}
    | _                -> raise(BugErrorException "Expecting Enum")
  
let rec RequiredBitsForAcnEncodingInt (t:Asn1Type) (absPath:AcnTypes.AbsPath) (asn1:Ast.AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let alignSize  = 
        match GetAlignment t asn1 with
        | Some(NextByte)    -> 7I
        | Some(NextWord)    -> 15I
        | Some(NextDWord)   -> 31I
        | None              -> 0I

    let calcSize =
        match t.Kind with
        | Integer   -> 
            let encClas = GetIntEncodingClass t asn1 acn emptyLocation
            match encClas with
            |Integer_uPER                                   -> 
                match uPER.uperGetMaxSizeInBits t.Kind t.Constraints asn1 with
                | Bounded(nBits)            -> nBits
                | Infinite                  -> raise(BugErrorException "impossible case in RequiredBitsForAcnEncodingInt")
            |PositiveInteger_ConstSize_8                    -> (8I)
            |PositiveInteger_ConstSize_big_endian_16        -> (16I)
            |PositiveInteger_ConstSize_little_endian_16     -> (16I)
            |PositiveInteger_ConstSize_big_endian_32        -> (32I)
            |PositiveInteger_ConstSize_little_endian_32     -> (32I)
            |PositiveInteger_ConstSize_big_endian_64        -> (64I)
            |PositiveInteger_ConstSize_little_endian_64     -> (64I)
            |PositiveInteger_ConstSize(nSize)               -> (nSize)
            |PositiveInteger_VarSize_LengthEmbedded         -> (72I)
            |TwosComplement_ConstSize_8                     -> (8I)         
            |TwosComplement_ConstSize_big_endian_16         -> (16I)
            |TwosComplement_ConstSize_little_endian_16      -> (16I)
            |TwosComplement_ConstSize_big_endian_32         -> (32I)
            |TwosComplement_ConstSize_little_endian_32      -> (32I)
            |TwosComplement_ConstSize_big_endian_64         -> (64I)
            |TwosComplement_ConstSize_little_endian_64      -> (64I)
            |TwosComplement_ConstSize(nSize)                -> (nSize)
            |TwosComplement_VarSize_LengthEmbedded          -> (72I)
            |ASCII_ConstSize(nSize)                         -> (nSize)
            |ASCII_VarSize_LengthEmbedded                   -> (8I+8I+18I*8I)
            |ASCII_VarSize_NullTerminated   _               -> (8I+8I+18I*8I)
            |BCD_ConstSize(nSize)                           -> (nSize)
            |BCD_VarSize_LengthEmbedded                     -> (8I+18I*4I)
            |BCD_VarSize_NullTerminated    _                -> (19I*4I)
        | Real  ->
            let encProp = GetEncodingProperty t asn1
            match encProp with
            | Some(IEEE754_32)    -> 32I
            | Some(IEEE754_64)    -> 64I
            | None             -> 
                match uPER.uperGetMaxSizeInBits t.Kind t.Constraints asn1 with
                | Bounded(nBits)            -> nBits
                | Infinite                  -> raise(BugErrorException "")
            | _                 -> raise(BugErrorException "")
        | Boolean   ->
            match GetBooleanEncoding t asn1 with
            | TrueValue(s) | FalseValue(s)  -> BigInteger s.Value.Length
        | NullType          ->
            match GetNullEncodingValue t asn1 with
            | Some(s)   -> BigInteger(s.Length)
            | None      -> 0I
        | Enumerated(items) ->
            let newType = GetIntTypeFromEnum t asn1 acn
            RequiredBitsForAcnEncodingInt newType absPath asn1 acn |> fst
        | ReferenceType(modl,tsName,_)   ->  
            let baseType = Ast.GetActualTypeAllConsIncluded t asn1
            RequiredBitsForAcnEncodingInt baseType [modl.Value;tsName.Value] asn1 acn |> fst
        | Sequence(children)        ->
            let OptionalChildenHandledLikeUPER = 
                     children 
                     |> Seq.filter(fun x -> match x.Optionality with Some(Optional) | Some(Default(_)) -> true |_ -> false) 
                     |> Seq.filter(fun x -> not(ChildHasPresenseDeterminant absPath x acn))
                     |> Seq.length
            let optionalBitMaskSize = BigInteger OptionalChildenHandledLikeUPER
            let childrenSize = children |> Seq.fold(fun accSize ch -> 
                                                        let childSize, _ = RequiredBitsForAcnEncodingInt ch.Type (absPath@[ch.Name.Value]) asn1 acn
                                                        accSize + childSize ) 0I
            optionalBitMaskSize + childrenSize
        | Choice(children)  ->
            let hasEnumDeterminant =
                acn.References |> Seq.exists(fun r -> r.decType.AbsPath = absPath && r.Kind = ChoiceDeteterminant)
            let childrenHavePresenceDeterminant =
                     children |> Seq.forall(fun x -> ChildHasPresenseDeterminant absPath x acn)
                
            let indexSize = if hasEnumDeterminant || childrenHavePresenceDeterminant then 0I else GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children)) 
            let maxChildSize = children |> Seq.fold(fun accSize ch -> 
                                                        let childSize,_ = RequiredBitsForAcnEncodingInt ch.Type (absPath@[ch.Name.Value]) asn1 acn
                                                        max accSize childSize ) 0I
            indexSize + maxChildSize
        | OctetString | BitString(_) | SequenceOf(_)->
            let encClass = GetSizeableEncodingClass_ t absPath asn1 acn emptyLocation 
            let innerItemSize = 
                match t.Kind with
                | OctetString                -> 8I
                | BitString(_)               -> 1I
                | SequenceOf(innerType)      -> RequiredBitsForAcnEncodingInt innerType (absPath@["#"]) asn1 acn |> fst
                | _ -> raise(BugErrorException "impossible")

            match encClass with
            | AutoSize          -> 
                match (uPER.GetTypeUperRange t.Kind t.Constraints asn1) with
                | Concrete(a,b)                   -> GetNumberOfBitsForNonNegativeInteger(b-a)+innerItemSize*b
                | _                               -> raise(SemanticError(emptyLocation, "Infinite Size"))
            | FixedSize(nItems) -> innerItemSize*nItems
            | ExternalField(_)  ->  
                match uPER.GetTypeUperRange t.Kind t.Constraints asn1 with
                | Concrete(_,b)     -> innerItemSize*b
                | _                 -> raise(SemanticError(emptyLocation, "Invalid Size"))
            | NullTerminated   _                 ->
                match uPER.GetTypeUperRange t.Kind t.Constraints asn1 with
                | Concrete(_,b)     -> innerItemSize*b+innerItemSize
                | _                 -> raise(SemanticError(emptyLocation, "Invalid Size"))

        | IA5String | NumericString ->
            let encClass = GetStringEncodingClass t absPath asn1 acn emptyLocation 
            encClass.maxSizeInBits

    let nBits = calcSize + alignSize
    nBits, BigInteger(System.Math.Ceiling(double(nBits)/8.0))




let rec RequiredMinBitsForAcnEncodingInt (t:Asn1Type) (absPath:AcnTypes.AbsPath) (asn1:Ast.AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let alignSize  = 0I

    let calcSize =
        match t.Kind with
        | Integer   -> 
            let encClas = GetIntEncodingClass t asn1 acn emptyLocation
            match encClas with
            |Integer_uPER                                   -> 
                match uPER.uperGetMinSizeInBits t.Kind t.Constraints asn1 with
                | Bounded(nBits)            -> nBits
                | Infinite                  -> raise(BugErrorException "")
            |PositiveInteger_ConstSize_8                    -> (8I)
            |PositiveInteger_ConstSize_big_endian_16        -> (16I)
            |PositiveInteger_ConstSize_little_endian_16     -> (16I)
            |PositiveInteger_ConstSize_big_endian_32        -> (32I)
            |PositiveInteger_ConstSize_little_endian_32     -> (32I)
            |PositiveInteger_ConstSize_big_endian_64        -> (64I)
            |PositiveInteger_ConstSize_little_endian_64     -> (64I)
            |PositiveInteger_ConstSize(nSize)               -> (nSize)
            |PositiveInteger_VarSize_LengthEmbedded         -> (72I)
            |TwosComplement_ConstSize_8                     -> (8I)         
            |TwosComplement_ConstSize_big_endian_16         -> (16I)
            |TwosComplement_ConstSize_little_endian_16      -> (16I)
            |TwosComplement_ConstSize_big_endian_32         -> (32I)
            |TwosComplement_ConstSize_little_endian_32      -> (32I)
            |TwosComplement_ConstSize_big_endian_64         -> (64I)
            |TwosComplement_ConstSize_little_endian_64      -> (64I)
            |TwosComplement_ConstSize(nSize)                -> (nSize)
            |TwosComplement_VarSize_LengthEmbedded          -> (72I)
            |ASCII_ConstSize(nSize)                         -> (nSize)
            |ASCII_VarSize_LengthEmbedded                   -> (8I)
            |ASCII_VarSize_NullTerminated   _               -> (8I)
            |BCD_ConstSize(nSize)                           -> (nSize)
            |BCD_VarSize_LengthEmbedded                     -> (8I)
            |BCD_VarSize_NullTerminated      _               -> (4I)
        | Real  ->
            let encProp = GetEncodingProperty t asn1
            match encProp with
            | Some(IEEE754_32)    -> 32I
            | Some(IEEE754_64)    -> 64I
            | None             -> 
                match uPER.uperGetMinSizeInBits t.Kind t.Constraints asn1 with
                | Bounded(nBits)            -> nBits
                | Infinite                  -> raise(BugErrorException "")
            | _                 -> raise(BugErrorException "")
        | Boolean   ->
            match GetBooleanEncoding t asn1 with
            | TrueValue(s) | FalseValue(s)  -> BigInteger s.Value.Length
        | NullType          ->
            match GetNullEncodingValue t asn1 with
            | Some(s)   -> BigInteger(s.Length)
            | None      -> 0I
        | Enumerated(items) ->
            let newType = GetIntTypeFromEnum t asn1 acn
            RequiredMinBitsForAcnEncodingInt newType absPath asn1 acn |> fst
        | ReferenceType(modl,tsName,_)   ->  
            let baseType = Ast.GetActualTypeAllConsIncluded t asn1
            RequiredMinBitsForAcnEncodingInt baseType [modl.Value; tsName.Value] asn1 acn |> fst
        | Sequence(children)        ->
            let OptionalChildenHandledLikeUPER = 
                     children 
                     |> Seq.filter(fun x -> match x.Optionality with Some(Optional) | Some(Default(_)) -> true |_ -> false) 
                     |> Seq.filter(fun x -> not(ChildHasPresenseDeterminant absPath x acn))
                     |> Seq.length
            let optionalBitMaskSize = BigInteger OptionalChildenHandledLikeUPER
            let childrenSize = children |> 
                               Seq.filter(fun x -> x.Optionality.IsNone) |> 
                               Seq.fold(fun accSize ch -> 
                                            let childSize, _ = RequiredMinBitsForAcnEncodingInt ch.Type (absPath@[ch.Name.Value]) asn1 acn
                                            accSize + childSize ) 0I
            optionalBitMaskSize + childrenSize
        | Choice(children)  ->
            let hasEnumDeterminant =
                acn.References |> Seq.exists(fun r -> r.decType.AbsPath = absPath && r.Kind = ChoiceDeteterminant)
            let childrenHavePresenceDeterminant =
                     children |> Seq.forall(fun x -> ChildHasPresenseDeterminant absPath x acn)
                
            let indexSize = if hasEnumDeterminant || childrenHavePresenceDeterminant then 0I else GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children)) 
            let maxChildSize = children |> Seq.fold(fun accSize ch -> 
                                                        let childSize,_ = RequiredMinBitsForAcnEncodingInt ch.Type (absPath@[ch.Name.Value]) asn1 acn
                                                        max accSize childSize ) 0I
            let minChildSize = children |> Seq.fold(fun accSize ch -> 
                                                        let childSize,_ = RequiredMinBitsForAcnEncodingInt ch.Type (absPath@[ch.Name.Value]) asn1 acn
                                                        min accSize childSize ) maxChildSize
            indexSize + minChildSize
        | OctetString | BitString(_) | SequenceOf(_)->
            let encClass = GetSizeableEncodingClass_ t absPath asn1 acn emptyLocation 
            let innerItemSize = 
                match t.Kind with
                | OctetString                -> 8I
                | BitString(_)               -> 1I
                | SequenceOf(innerType)      -> RequiredMinBitsForAcnEncodingInt innerType (absPath@["#"]) asn1 acn |> fst
                | _ -> raise(BugErrorException "impossible")

            match encClass with
            | AutoSize          -> 
                match (uPER.GetTypeUperRange t.Kind t.Constraints asn1) with
                | Concrete(a,b)                   -> GetNumberOfBitsForNonNegativeInteger(b-a)+innerItemSize*a
                | _                               -> raise(SemanticError(emptyLocation, "Infinite Size"))
            | FixedSize(nItems) -> innerItemSize*nItems
            | ExternalField(_)  ->  
                match uPER.GetTypeUperRange t.Kind t.Constraints asn1 with
                | Concrete(a,_)     -> innerItemSize*a
                | _                 -> raise(SemanticError(emptyLocation, "Invalid Size"))
            | NullTerminated  _                  ->
                match uPER.GetTypeUperRange t.Kind t.Constraints asn1 with
                | Concrete(a,_)     -> innerItemSize*a+innerItemSize
                | _                 -> raise(SemanticError(emptyLocation, "Invalid Size"))
        | IA5String | NumericString         ->
            let encClass = GetStringEncodingClass t absPath asn1 acn emptyLocation 
            encClass.minSizeInBits

    let nBits = calcSize + alignSize
    nBits, BigInteger(System.Math.Ceiling(double(nBits)/8.0))
  


module aux =
    let GetTypeByAbsPath (r:AstRoot) (absPath:list<string>)  = 
        let tas, restPath = match absPath with
                                        |m::tas::rest -> 
                                            let md = r.Modules |> Seq.find(fun x -> x.Name.Value = m)
                                            let ts = md.TypeAssignments |> Seq.find(fun x -> x.Name.Value = tas)
                                            ts, rest
                                        |_            -> raise(BugErrorException (sprintf "Invalid path %s" (absPath.StrJoin ".")))
        let rec GetLongChild (r:AstRoot) (t:Asn1Type) (pathToLongChild:list<string>)  = 
            match pathToLongChild with
            | []                -> t
            | fldName::restPart ->
                match t.Kind with
                | Sequence(children) | Choice(children) ->
                    match children |> Seq.tryFind(fun x -> x.Name.Value = fldName) with
                    | Some(ch)  ->  GetLongChild r (ch.Type) restPart 
                    | None      ->  raise(BugErrorException (sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
                | SequenceOf(ch) when fldName = "#" ->
                    GetLongChild r ch restPart 
                | ReferenceType(mdName, tsName, _) ->
                    GetLongChild r (GetBaseType t r) pathToLongChild 
                | _             ->  raise(BugErrorException (sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
        GetLongChild r tas.Type restPath


    let BreakVPath (r:AstRoot) (absPath:list<string>) =
        let tas, restPath = match absPath with
                                        |m::tas::rest -> 
                                            let md = r.Modules |> Seq.find(fun x -> x.Name.Value = m)
                                            let ts = md.TypeAssignments |> Seq.find(fun x -> x.Name.Value = tas)
                                            ts, rest
                                        |_            -> raise(BugErrorException (sprintf "Invalid path %s" (absPath.StrJoin ".")))
        let rec GetLongChild (r:AstRoot) (t:Asn1Type) (pathUpToHere:list<string>) (pathToLongChild:list<string>)  = 
            let rec IsComposite (t:Asn1Type) r =
                match t.Kind with
                | Sequence(_) | Choice(_) | SequenceOf(_)               -> true
                | Integer | Boolean | Real | NullType | Enumerated(_)   -> false
                | BitString | OctetString | IA5String | NumericString   -> false
                | ReferenceType(_)  ->
                    let baseType = Ast.GetBaseType t r
                    IsComposite baseType r
            seq {
                match pathToLongChild with
                | []                -> ()
                | fldName::restPart ->
                    match t.Kind with
                    | Sequence(children) | Choice(children) ->
                        match children |> Seq.tryFind(fun x -> x.Name.Value = fldName) with
                        | Some(ch)  ->  
                            let newPathUpToHere = pathUpToHere @ [fldName]
                            match ch.Type.Kind with
                            | ReferenceType(m,tas, _) when IsComposite ch.Type r->
                                yield newPathUpToHere, (m.Value,tas.Value)
                            
                                yield! GetLongChild r (GetActualType ch.Type r) [m.Value; tas.Value] restPart 
                            | _     -> yield! GetLongChild r (ch.Type) newPathUpToHere restPart 
                        | None      ->  raise(BugErrorException (sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
                    | SequenceOf(ch) when fldName = "#" ->
                        let newPathUpToHere = pathUpToHere @ [fldName]
                        match ch.Kind with
                        | ReferenceType(m,tas, _) when IsComposite ch r ->
                            yield newPathUpToHere, (m.Value,tas.Value)
                            yield! GetLongChild r (GetActualType ch r) [m.Value; tas.Value] restPart 
                        | _     -> yield! GetLongChild r (ch) newPathUpToHere restPart 
                    | _             ->  raise(BugErrorException (sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
            } |> Seq.toList
        GetLongChild r tas.Type (absPath |>Seq.take 2|>Seq.toList) restPath
    

    let IsVirtualPath (r:AstRoot) (absPath:list<string>)  = 
        let tas, restPath = match absPath with
                                        |m::tas::rest -> 
                                            let md = r.Modules |> Seq.find(fun x -> x.Name.Value = m)
                                            let ts = md.TypeAssignments |> Seq.find(fun x -> x.Name.Value = tas)
                                            ts, rest
                                        |_            -> raise(BugErrorException (sprintf "Invalid path %s" (absPath.StrJoin ".")))
        let rec IsVirtualPathAux (r:AstRoot) (t:Asn1Type) (pathToLongChild:list<string>)  pathContainsRefType= 
            match pathToLongChild with
            | []                -> false
            | fldName::restPart ->
                match t.Kind with
                | Sequence(children) | Choice(children) ->
                    match children |> Seq.tryFind(fun x -> x.Name.Value = fldName) with
                    | Some(ch)  ->  
                        match ch.AcnInsertedField with
                        | true   -> pathContainsRefType
                        | false      -> IsVirtualPathAux r (ch.Type) restPart pathContainsRefType
                    | None      ->  raise(BugErrorException (sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
                | SequenceOf(ch) when fldName = "#" ->
                    IsVirtualPathAux r ch restPart pathContainsRefType
                | ReferenceType(_, _, _) ->
                    IsVirtualPathAux r (GetBaseType t r) pathToLongChild true
                | _             ->  raise(BugErrorException (sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
        IsVirtualPathAux r tas.Type restPath false


module Resolve =
    let rec GetLongChild (r:AstRoot, acn:AcnAst) (t:Asn1Type, absPath:list<string>) (pathToLongChild:list<string>) loc = 
        match pathToLongChild with
        | []                -> t
        | fldName::restPart ->
            match t.Kind with
            | Sequence(children) | Choice(children) ->
                match children |> Seq.tryFind(fun x -> x.Name.Value = fldName) with
                | Some(ch)  ->  GetLongChild (r,acn) (ch.Type, absPath@[fldName]) restPart loc
                | None      ->  
                    //it may be an ACN Inserted child so look at acn
                    match acn.Types |> Seq.tryFind(fun x -> x.TypeID = absPath@[fldName]) with
                    | Some(acnType) ->
                        match acnType.ImpMode with
                        | RecordField       -> raise(BugErrorException "Child exists in ASN.1")
                        | AcnTypeImplMode.LocalVariable(asn1Type) | AcnTypeImplMode.FunctionParameter(asn1Type) ->
                            match asn1Type with
                            | AcnTypes.Integer   -> {Asn1Type.Kind = Ast.Integer; Constraints=[]; Location=emptyLocation; AcnProperties=[]}
                            | AcnTypes.Boolean   -> {Asn1Type.Kind = Ast.Boolean; Constraints=[]; Location=emptyLocation; AcnProperties=[]}
                            | AcnTypes.NullType  -> {Asn1Type.Kind = Ast.NullType; Constraints=[]; Location=emptyLocation; AcnProperties=[]}
                            | RefTypeCon(md,ts)  -> {Asn1Type.Kind = Ast.ReferenceType(md,ts, false); Constraints=[]; Location=emptyLocation; AcnProperties=[]}
                    | None -> raise(SemanticError (loc,sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))
            | SequenceOf(ch) when fldName = "#" ->
                GetLongChild (r,acn) (ch ,absPath@[fldName]) restPart loc
            | ReferenceType(mdName, tsName, _) ->
                GetLongChild (r,acn) ((GetBaseType t r),[mdName.Value; tsName.Value]) pathToLongChild loc
            | _             ->  raise(SemanticError (loc,sprintf "Invalid Reference: %s" (pathToLongChild.StrJoin ".")))

    let GetTypeFromAbsPath (r:AstRoot, acn:AcnAst) (p:AbsPath) loc =
        match p with
        | []  | _::[]               -> raise(SemanticError (loc,sprintf "Invalid Reference: %s" (p.StrJoin ".")))
        | modName::tasName::restPart -> 
            GetLongChild (r,acn) ((Ast.GetActualTypeByNameLoc modName tasName loc r), [modName;tasName]) restPart loc



    let ResolveRelativePaths (acn:AcnAst) (asn1:AstRoot) : AcnAstResolved =
        let ResolveLongRef (r:LongReference) : LongReferenceResolved =
            let modName, tasName = match r.TypeID with
                                   | []  | _::[]       -> raise(BugErrorException "Invalid Abs Path")
                                   | mName::tName::_   -> mName,tName
            let FixLongReferenceKind (r:LongReference) =
                match r.Kind with
                | RefTypeArgument("")   -> 
                    let argIndex = acn.References |> Seq.filter(fun x -> x.TypeID = r.TypeID) |> Seq.findIndex(fun x -> x = r)
                    let decType = GetTypeFromAbsPath (asn1,acn) r.TypeID r.Location
                    let prm = 
                        match decType.Kind with
                        | ReferenceType(md,ts, _)  ->
                            let asn1Module = asn1.GetModuleByName md
                            let tas = asn1Module.GetTypeAssignmentByName ts
                            let prms = acn.Parameters |> List.filter(fun x -> x.ModName = md.Value && x.TasName=ts.Value) 
                            match argIndex < (Seq.length prms)  with
                                          | false   -> raise(FsUtils.SemanticError(r.Location, "Too many arguments"))
                                          | true    -> (Seq.nth argIndex prms).Name
                        | _                     -> raise(BugErrorException("Expecting Reference Type"))
                    RefTypeArgument prm
                | _                     -> r.Kind
            let resolvedPoint = 
                let makeTypePoint() = 
                    let decType = GetTypeFromAbsPath (asn1,acn) r.TypeID r.Location
                    let parPath = r.TypeID |> List.rev |> List.tail |> List.rev
                    let parType = GetTypeFromAbsPath (asn1,acn) parPath r.Location
                    let determinant = GetLongChild (asn1,acn) (parType,parPath)  r.LongRef r.Location
                    //we have to check that determinant and decType match based on the r.Kind
                    TypePoint (parPath@r.LongRef)
                match r.LongRef with
                | []            -> raise(SemanticError (r.Location,"Invalid Reference (empty path)" ))
                | fldName::[]   ->
                    match acn.Parameters |> Seq.tryFind(fun x -> x.ModName = modName && x.TasName = tasName && x.Name = fldName) with
                    | Some(p)   -> ParamPoint [modName; tasName; fldName]
                    | None      -> makeTypePoint()
                | _             -> makeTypePoint()
            {
                LongReferenceResolved.decType = TypePoint r.TypeID
                determinant = resolvedPoint
                Kind = FixLongReferenceKind r
            }
        {
            AcnAstResolved.Constants = acn.Constants
            Parameters = acn.Parameters
            TmpTypes = []
            References = acn.References |> List.map ResolveLongRef
            Files = acn.Files
        }





//
//let IsVirtualPath 

let GetVirtualPaths (asn1:AstRoot)  (acn:AcnTypes.AcnAstResolved) =
    let virtualPaths = seq {
                            for r in acn.References do
                                match r.determinant with
                                | AcnTypes.TypePoint(pth)    when aux.IsVirtualPath asn1 pth -> 
                                    yield r
                                | _         -> ()
                            } |> Seq.toList
    let nonVirtualPaths = seq {
                            for r in acn.References do
                                match r.determinant with
                                | AcnTypes.TypePoint(pth)    when not (aux.IsVirtualPath asn1 pth) -> 
                                    yield r
                                | _         -> yield r
                            } |> Seq.toList
    virtualPaths, nonVirtualPaths    


let Asn1Type2AcnAsn1Type (t:Asn1Type) : AcnTypes.AcnAsn1Type =
    match t.Kind with
    | Ast.Integer               -> AcnTypes.Integer
    | Ast.ReferenceType(m,t,_)  -> AcnTypes.RefTypeCon(m,t)
    | Ast.Boolean               -> AcnTypes.Boolean
    | Ast.NullType              -> AcnTypes.NullType
    | _                         -> raise(BugErrorException "")




let RemoveVirtualPaths (asn1:AstRoot)  (acn:AcnTypes.AcnAstResolved) : AcnTypes.AcnAstResolved=
    
    let vPaths,restPaths = GetVirtualPaths asn1 acn

    //let HandleVirtualPath(r:LongReferenceResolved) =
    let GetNameTypeFromVirtualPath (r:LongReferenceResolved) =
        let name = r.determinant.AbsPath |> List.rev |> List.head
        let asn1Type = aux.GetTypeByAbsPath asn1 r.determinant.AbsPath
        name,asn1Type

    //Adds a temp type (if required) in the appropriate tas
    let AddTempType (r:LongReferenceResolved) (acn:AcnTypes.AcnAstResolved) =
        let modName = r.determinant.AbsPath.Head
        let tasName = r.determinant.AbsPath.Tail.Head
        let name, asn1Type = GetNameTypeFromVirtualPath r
        match acn.TmpTypes |> Seq.tryFind(fun x -> x.ModName=modName && x.TasName=tasName && x.Name=name) with
        |Some(_)        -> acn
        | None          ->
            let tmpType = {AcnTypes.AcnTempType.ModName = modName; TasName=tasName; Name=name; Asn1Type=(Asn1Type2AcnAsn1Type asn1Type)}
            {acn with TmpTypes=tmpType::acn.TmpTypes}

    //Change existing Reference, so that determinant points to the temp type and not to the virtual type        
    let ChangReference (r:LongReferenceResolved) (acn:AcnTypes.AcnAstResolved) =
        let newDetePath = (r.determinant.AbsPath |> Seq.take 2 |> Seq.toList) @ [r.determinant.AbsPath |> List.rev |> List.head]
        let newRef = {r with determinant= TempPoint newDetePath}
        let newRefs = acn.References |> Seq.map(fun x -> if x = r then newRef else x) |> Seq.toList
        {acn with References = newRefs}

    let AddArgsAndParams  (r:LongReferenceResolved) (acn:AcnTypes.AcnAstResolved) =
        let points = aux.BreakVPath asn1 r.determinant.AbsPath
        let name, asn1Type = GetNameTypeFromVirtualPath r
        let newParms = seq {
                        for (_, (md,tas)) in points do
                               match acn.Parameters |> Seq.tryFind(fun x-> x.ModName=md && x.TasName=tas && x.Name=name) with
                               |Some(_)  -> ()
                               |None     -> yield {AcnTypes.AcnParameter.ModName=md; TasName=tas; Name=name; Asn1Type=(Asn1Type2AcnAsn1Type asn1Type);Mode=EncodeDecodeMode;Location=emptyLocation}
                        } |> Seq.toList
        let addArgIfNotExists decTypePath =
            let decType = TypePoint decTypePath
            let mdName = decTypePath.Head
            let tsName = decTypePath.Tail.Head
            let determ  = match acn.TmpTypes |> Seq.tryFind(fun x -> x.ModName = mdName && x.TasName = tsName && x.Name=name) with
                          | None    -> ParamPoint [mdName; tsName; name]
                          | Some(_) -> TempPoint [mdName; tsName; name]
            let newArg = {LongReferenceResolved.decType = decType; determinant=determ; Kind=RefTypeArgument name}
            match acn.References |> Seq.tryFind(fun x-> x=newArg) with
            | Some(_)   -> None
            | None      -> Some newArg
            
        let newArgs = seq {
                        for (refTypePath, _) in points do
                            match addArgIfNotExists refTypePath with
                            | Some(newArg)  -> yield newArg
                            | None          -> ()
                      } |> Seq.toList
        {acn with Parameters=acn.Parameters@newParms; References=acn.References@newArgs}
         
    let HandleVirtualPath  (acn:AcnTypes.AcnAstResolved) (r:LongReferenceResolved) =
        acn|> AddTempType r |> ChangReference r |> AddArgsAndParams r
    
    vPaths |> Seq.fold HandleVirtualPath acn
    


let CheckForUnreferencedAcnInsertedFields (asn1:AstRoot)  (acn:AcnTypes.AcnAstResolved) =
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:unit) = 
        match t.Kind with
        | Sequence(children)    -> 
            let tasName = match ass with
                          | Assignment.TypeAssignment(ts)   -> ts.Name.Value
                          | Assignment.ValueAssignment(vl)  -> match vl.Type.Kind with
                                                               |ReferenceType(md,ts,_)  -> ts.Value
                        
                                                               | _                      -> raise(BugErrorException "could not determin Type Assignment Name")
            // Check for unreferenced acn inserted children
            children |> 
            Seq.filter(fun x -> x.AcnInsertedField) |>  // get only acn Inserted fields
            Seq.filter(fun x -> (Ast.GetActualType x.Type asn1).Kind <> NullType) |>    // exclude NULL types
            // and also exclude those fields that become Parameters
            Seq.filter(fun x -> acn.Parameters |> Seq.exists(fun p -> p.ModName = m.Name.Value && p.TasName = tasName && p.Name = x.Name.Value ) |> not) |>
            Seq.iter(fun x -> 
                        let chPath = path@[x.Name.Value]
                        let lc = x.Name.Location
                        match acn.References |> Seq.tryFind(fun y -> y.determinant.AbsPath = chPath) with
                        | Some(_)  -> ()
                        | None     -> raise(SemanticError(lc,sprintf "the ACN inserted field '%s' is not reference by any other field (e.g. as length determinant or presence determinant etc)" x.Name.Value))
                       )
            // Check for referenced ASN1 children
            children |> 
            Seq.filter(fun x -> not x.AcnInsertedField) |>  
            Seq.iter(fun x -> 
                        let chPath = path@[x.Name.Value]
                        let lc = x.Name.Location
                        match acn.References |> Seq.tryFind(fun y -> y.determinant.AbsPath = chPath && match y.Kind with AcnTypes.RefTypeArgument(_) -> false | _ -> true) with
                        | Some(ref)  -> 
                            raise(SemanticError(lc, sprintf "ASN.1 fields cannot act as encoding determinants. Remove field '%s' from the ASN.1 grammar and introduce it in the ACN grammar" x.Name.Value))
                        | None     -> ()
                       )


            
        | _                     -> ()
    

    let CheckForReferencedASN1children () =
        acn.References |> Seq.iter(fun rf ->match rf.determinant with
                                            | TypePoint(pth)        -> 
                                                match pth with
                                                | md::ts::sq::rest  -> 
                                                    let parPath = pth |> List.rev |> List.tail |> List.rev
                                                    let parType =  Ast.GetActualType (Ast.GetTypeByAbsPath parPath asn1) asn1
                                                    match parType.Kind with
                                                    | Sequence(children)  -> 
                                                        let chName = pth |> List.rev |> List.head
                                                        match children |> Seq.tryFind(fun x -> x.Name.Value = chName && (not x.AcnInsertedField)) with
                                                        | Some(child)       -> 
                                                            raise(SemanticError(child.Name.Location, sprintf "ASN.1 fields cannot act as encoding determinants. Remove field '%s' from the ASN.1 grammar and introduce it in the ACN grammar" child.Name.Value))
                                                        | _                 -> ()
                                                    | _                   -> ()
                                                | _                 -> ()
                                            | ParamPoint(pth)       -> ()           
                                            | TempPoint(oth)        -> ()
                                              )
    VisitTree asn1 {DefaultVisitors with visitType=OnType_collerLocalVariables} ()
    CheckForReferencedASN1children ()
