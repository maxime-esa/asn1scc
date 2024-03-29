﻿module CAstAcnEncodingClasses


open System
open System.Numerics
open Constraints
open CAst
open FsUtils

type State = {
    currentTypes : Asn1Type list
}




let rec GetBooleanEncoding (acnProps: AcnTypes.AcnProperty list)  =
    match acnProps |> List.choose(fun x -> match x with AcnTypes.BooleanEncoding(a) -> Some a | _ -> None ) with
    | hd::_   -> hd
    | []      -> AcnTypes.TrueValue "1".AsLoc


let rec GetNullEncodingValue (acnProps: AcnTypes.AcnProperty list)   =
    match acnProps |> List.choose(fun x -> match x with AcnTypes.NullValue(a) -> Some a | _ -> None ) with
    | hd::_   -> Some hd.Value
    | []      -> None

let rec GetEndianness (acnProps: AcnTypes.AcnProperty list)   =
    match acnProps |> List.choose(fun x -> match x with AcnTypes.Endianness(a) -> Some a | _ -> None ) with
    | hd::_   -> hd
    | []      -> AcnTypes.endianness.BigEndianness


let rec isEnumEncodingValues (acnProps: AcnTypes.AcnProperty list)   =
    acnProps |> List.exists(fun x -> match x with AcnTypes.EncodeValues -> true | _ -> false )

let GetEncodingProperty (acnProps: AcnTypes.AcnProperty list) =
    match acnProps |> List.choose(fun x -> match x with AcnTypes.Encoding(a) -> Some a | _ -> None ) with
    | hd::_ -> Some hd
    | []    -> None



type sizePropertyPriv =
    | SP_Fixed          of int
    | SP_NullTerminated of byte


///helper function
let sizeToPriv (constants:AcnTypes.AcnConstant list)  sizeProperty =
    match sizeProperty with
    | AcnTypes.sizeProperty.Fixed(c)            -> SP_Fixed (int (AcnTypes.EvaluateConstant constants c))
    | AcnTypes.sizeProperty.NullTerminated  b    -> SP_NullTerminated b

let GetSizeProperty  (constants:AcnTypes.AcnConstant list) (acnProps: AcnTypes.AcnProperty list) =
    match acnProps |> List.choose(fun x -> match x with AcnTypes.SizeProperty(a) -> Some a | _ -> None ) with
    | hd::_ -> (sizeToPriv constants hd )
    | []    -> raise(BugErrorException "mandatory property missing")


let getAcnProps (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) (typeId:ReferenceToType) =
    let acnKey = typeId.AcnAbsPath
    match acnTypes.TryFind acnKey with
    | None  -> []
    | Some t -> t.Properties



let GetAlignment (acnProps: AcnTypes.AcnProperty list)  =
    match acnProps |> List.choose(fun x -> match x with AcnTypes.Alignment(al) -> Some al | _ -> None ) with
    | (AcnTypes.NextByte)::_   -> Some NextByte, 8
    | (AcnTypes.NextWord)::_   -> Some NextWord, 16
    | (AcnTypes.NextDWord)::_  -> Some NextDWord, 32
    | []       -> None, 0

//The banner was generated by the following url
//http://patorjk.com/software/taag/#p=display&h=2&v=1&f=Banner&t=Integer

(*
 ###
  #  #    # ##### ######  ####  ###### #####
  #  ##   #   #   #      #    # #      #    #
  #  # #  #   #   #####  #      #####  #    #
  #  #  # #   #   #      #  ### #      #####
  #  #   ##   #   #      #    # #      #   #
 ### #    #   #   ######  ####  ###### #    #
*)
let GetIntEncodingClass_private (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (aid:ReferenceToType) uperMinSizeInBits uperMaxSizeInBits isUnsigned=
    let acnProps = getAcnProps acnTypes aid
    let alignment, alignmentSize = GetAlignment acnProps
    let encClass, minSizeInBits, maxSizeInBits =
        // if the mandatory property size is missing => the type will be encoded like uPER
        match acnProps |> List.exists(fun x -> match x with AcnTypes.SizeProperty(_) -> true | _ -> false ) with
        | false -> Integer_uPER, uperMinSizeInBits, uperMaxSizeInBits
        | true  ->
            let endianness = GetEndianness acnProps
            let encProp = (GetEncodingProperty acnProps).Value
            let sizeProp = GetSizeProperty acn.Constants acnProps
            let bUINT = isUnsigned

            match encProp, sizeProp, endianness with
            | AcnTypes.PosInt, SP_Fixed(8) , AcnTypes.BigEndianness               ->  PositiveInteger_ConstSize_8, 8, 8
            | AcnTypes.PosInt, SP_Fixed(16), AcnTypes.BigEndianness               ->  PositiveInteger_ConstSize_big_endian_16, 16, 16
            | AcnTypes.PosInt, SP_Fixed(16), AcnTypes.LittleEndianness            ->  PositiveInteger_ConstSize_little_endian_16, 16, 16
            | AcnTypes.PosInt, SP_Fixed(32), AcnTypes.BigEndianness               ->  PositiveInteger_ConstSize_big_endian_32, 32, 32
            | AcnTypes.PosInt, SP_Fixed(32), AcnTypes.LittleEndianness            ->  PositiveInteger_ConstSize_little_endian_32, 32, 32
            | AcnTypes.PosInt, SP_Fixed(64), AcnTypes.BigEndianness               ->  PositiveInteger_ConstSize_big_endian_64, 64, 64
            | AcnTypes.PosInt, SP_Fixed(64), AcnTypes.LittleEndianness            ->  PositiveInteger_ConstSize_little_endian_64, 64, 64
            | AcnTypes.PosInt, SP_Fixed(fxVal) , AcnTypes.BigEndianness           ->  PositiveInteger_ConstSize fxVal, fxVal, fxVal
            | AcnTypes.PosInt, SP_NullTerminated _, _                    ->  raise(SemanticError(errLoc, "Acn properties pos-int and null-terminated are mutually exclusive"))
            | AcnTypes.TwosComplement, _,_              when bUINT       ->  raise(SemanticError(errLoc, "Acn property twos-complement cannot be applied to non negative INTEGER types"))
            | AcnTypes.TwosComplement, SP_Fixed(8) , AcnTypes.BigEndianness       ->  TwosComplement_ConstSize_8, 8, 8
            | AcnTypes.TwosComplement, SP_Fixed(16), AcnTypes.BigEndianness       ->  TwosComplement_ConstSize_big_endian_16, 16, 16
            | AcnTypes.TwosComplement, SP_Fixed(16), AcnTypes.LittleEndianness    ->  TwosComplement_ConstSize_little_endian_16, 16, 16
            | AcnTypes.TwosComplement, SP_Fixed(32), AcnTypes.BigEndianness       ->  TwosComplement_ConstSize_big_endian_32, 32, 32
            | AcnTypes.TwosComplement, SP_Fixed(32), AcnTypes.LittleEndianness    ->  TwosComplement_ConstSize_little_endian_32, 32, 32
            | AcnTypes.TwosComplement, SP_Fixed(64), AcnTypes.BigEndianness       ->  TwosComplement_ConstSize_big_endian_64, 64, 64
            | AcnTypes.TwosComplement, SP_Fixed(64), AcnTypes.LittleEndianness    ->  TwosComplement_ConstSize_little_endian_64, 64, 64
            | AcnTypes.TwosComplement, SP_Fixed(fxVal) , AcnTypes.BigEndianness   ->  TwosComplement_ConstSize fxVal, fxVal, fxVal
            | AcnTypes.TwosComplement, SP_NullTerminated _, _            ->  raise(SemanticError(errLoc, "Acn properties twos-complement and null-terminated are mutually exclusive"))
            | AcnTypes.Ascii, SP_Fixed(fxVal) , AcnTypes.BigEndianness            ->
                match bUINT with
                | true                                                            -> ASCII_UINT_ConstSize fxVal, fxVal, fxVal
                | false                                                           -> ASCII_ConstSize  fxVal, fxVal, fxVal
            | AcnTypes.BCD, SP_Fixed(fxVal) , AcnTypes.BigEndianness              ->  BCD_ConstSize fxVal, fxVal, fxVal
            | AcnTypes.BCD, SP_NullTerminated b, AcnTypes.BigEndianness           ->  BCD_VarSize_NullTerminated b, 4, 19*4
            | AcnTypes.Ascii, SP_NullTerminated b, AcnTypes.BigEndianness         ->
                match bUINT with
                | true                                                            -> ASCII_UINT_VarSize_NullTerminated b, 8, 8+8+18*8
                | false                                                           -> ASCII_VarSize_NullTerminated b, 8, 8+8+18*8
            | _, SP_NullTerminated _, _                                  ->  raise(SemanticError(errLoc, "null-terminated can be applied only for ASCII or BCD encodings"))
            | _, _ , AcnTypes.LittleEndianness                           ->  raise(SemanticError(errLoc, "Little endian can be applied only for fixed size encodings and size must be 16 or 32 or 64"))
            | AcnTypes.IEEE754_32, _, AcnTypes.BigEndianness             ->  raise(SemanticError(errLoc, "invalid encoding value (choose one of pos-int, twos-complement, ascii, BCD)"))
            | AcnTypes.IEEE754_64, _, AcnTypes.BigEndianness             ->  raise(SemanticError(errLoc, "invalid encoding value (choose one of pos-int, twos-complement, ascii, BCD)"))

    encClass, alignment, minSizeInBits+alignmentSize, maxSizeInBits+alignmentSize


let GetIntEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.Integer) =
    GetIntEncodingClass_private acn acnTypes errLoc a.id a.uperMinSizeInBits a.uperMaxSizeInBits a.IsUnsigned

let GetEnumeratedEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.Enumerated) =
    let acnProps = getAcnProps acnTypes a.id
    match isEnumEncodingValues acnProps with
    | false ->
        let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetIntEncodingClass_private acn acnTypes errLoc a.id a.uperMinSizeInBits a.uperMaxSizeInBits true
        EncodeIndexes encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits
    | true  ->
        let minVal = a.items |> List.map(fun x -> x.Value) |> List.min
        let maxVal = a.items |> List.map(fun x -> x.Value) |> List.max
        let uperSizeForValues = int (GetNumberOfBitsForNonNegativeInteger(maxVal-minVal))
        let encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits = GetIntEncodingClass_private acn acnTypes errLoc a.id uperSizeForValues uperSizeForValues (minVal >= 0I)
        EncodeValues encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits


(*
 ######
 #     # ######   ##   #
 #     # #       #  #  #
 ######  #####  #    # #
 #   #   #      ###### #
 #    #  #      #    # #
 #     # ###### #    # ######

*)

let GetRealEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.Real) =
    let acnProps = getAcnProps acnTypes a.id
    let alignment, alignmentSize = GetAlignment acnProps
    let encClass, minSizeInBits, maxSizeInBits =
        match acnProps |> List.exists(fun x -> match x with AcnTypes.Encoding(_) -> true | _ -> false ) with
        | false     -> Real_uPER, a.uperMinSizeInBits, a.uperMaxSizeInBits
        | true      ->
            let enc = (GetEncodingProperty acnProps).Value
            let endianness = GetEndianness acnProps
            match enc, endianness with
            | AcnTypes.IEEE754_32, AcnTypes.BigEndianness     -> Real_IEEE754_32_big_endian, 32, 32
            | AcnTypes.IEEE754_64, AcnTypes.BigEndianness     -> Real_IEEE754_64_big_endian, 64, 64
            | AcnTypes.IEEE754_32, AcnTypes.LittleEndianness  -> Real_IEEE754_32_little_endian, 32, 32
            | AcnTypes.IEEE754_64, AcnTypes.LittleEndianness  -> Real_IEEE754_64_little_endian, 64, 64
            | _,_                                             -> raise(BugErrorException "Invalid combination")
    encClass, alignment, minSizeInBits+alignmentSize, maxSizeInBits+alignmentSize

(*
███╗   ██╗██╗   ██╗██╗     ██╗  ████████╗██╗   ██╗██████╗ ███████╗
████╗  ██║██║   ██║██║     ██║  ╚══██╔══╝╚██╗ ██╔╝██╔══██╗██╔════╝
██╔██╗ ██║██║   ██║██║     ██║     ██║    ╚████╔╝ ██████╔╝█████╗
██║╚██╗██║██║   ██║██║     ██║     ██║     ╚██╔╝  ██╔═══╝ ██╔══╝
██║ ╚████║╚██████╔╝███████╗███████╗██║      ██║   ██║     ███████╗
╚═╝  ╚═══╝ ╚═════╝ ╚══════╝╚══════╝╚═╝      ╚═╝   ╚═╝     ╚══════╝
*)

let GetNullTypeEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.NullType) =
    let acnProps = getAcnProps acnTypes a.id
    let alignment, alignmentSize = GetAlignment acnProps
    let encClass, minSizeInBits, maxSizeInBits =
        match GetNullEncodingValue acnProps with
        | Some(s)   ->
            let arrBytes = bitStringValueToByteArray (s.AsLoc) |> Seq.toList
            {NullAcnEncodingClass.byteMask = arrBytes; patternSizeInBits = s.Length}, s.Length, s.Length
        | None      -> {NullAcnEncodingClass.byteMask = []; patternSizeInBits = 0}, 0, 0
    encClass, alignment, minSizeInBits+alignmentSize, maxSizeInBits+alignmentSize


let GetBooleanTypeEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.Boolean) =
    let acnProps = getAcnProps acnTypes a.id
    let alignment, alignmentSize = GetAlignment acnProps
    let encClass, minSizeInBits, maxSizeInBits =
        match GetBooleanEncoding acnProps with
        | AcnTypes.TrueValue(bitVal)   ->
            let arrBytes = bitStringValueToByteArray bitVal |> Seq.toList
            let encClass = {BooleanAcnEncodingClass.truePattern = arrBytes; falsePattern = (arrBytes |> List.map (~~~));patternSizeInBits = bitVal.Value.Length;encodingValueIsTrue = true}
            encClass, bitVal.Value.Length, bitVal.Value.Length
        | AcnTypes.FalseValue(bitVal)  ->
            let arrBytes = bitStringValueToByteArray bitVal |> Seq.toList
            let encClass = {BooleanAcnEncodingClass.truePattern = (arrBytes |> List.map (~~~)); falsePattern = arrBytes;patternSizeInBits = bitVal.Value.Length;encodingValueIsTrue = false}
            encClass, bitVal.Value.Length, bitVal.Value.Length
    encClass, alignment, minSizeInBits+alignmentSize, maxSizeInBits+alignmentSize

(*
 ###    #    #######  #####
  #    # #   #       #     # ##### #####  # #    #  ####
  #   #   #  #       #         #   #    # # ##   # #    #
  #  #     # ######   #####    #   #    # # # #  # #
  #  #######       #       #   #   #####  # #  # # #  ###
  #  #     # #     # #     #   #   #   #  # #   ## #    #
 ### #     #  #####   #####    #   #    # # #    #  ####
*)


type PrivateSizeableEncodingClass =
    | PrivateFixedSize of int
    | PrivateAutoSize
    | PrivateExternalField
    | PrivateNullTerminated of byte

let getPrivateSizeableEncodingClass (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) (acn:AcnTypes.AcnAst)  (id:ReferenceToType) (acnParams: AcnParameter list) (us:State)=
    let acnProps = getAcnProps acnTypes id
    match acnProps |> List.choose(fun x -> match x with AcnTypes.SizeProperty(a) -> Some a | _ -> None ) with
    | hd::_ ->
        match hd with
        | AcnTypes.sizeProperty.Fixed(c)            -> PrivateFixedSize (int (AcnTypes.EvaluateConstant acn.Constants c)), us
        | AcnTypes.sizeProperty.NullTerminated b    -> PrivateNullTerminated b, us
    | []    ->
        match acn.References |> Seq.tryFind(fun x -> x.TypeID = id.AcnAbsPath && x.Kind = AcnTypes.SizeDeterminant) with
        | Some(r)       ->  PrivateExternalField, us
        | None          ->  PrivateAutoSize, us

let GetStringEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.StringType) (acnParams: AcnParameter list) (us:State) =
    let asn1Min, asn1Max = a.minSize, a.maxSize
    let acnProps = getAcnProps acnTypes a.id
    let alignment, alignmentSize = GetAlignment acnProps
    let bAsn1FixedSize = asn1Min = asn1Max
    let bAsciiEncoding =
        match GetEncodingProperty acnProps with
        | Some AcnTypes.Ascii     -> true
        | _                       -> false
    let sizeClass, fs = getPrivateSizeableEncodingClass acnTypes acn  a.id acnParams us

    let alphaSet = a.charSet
    let allowedBytes = alphaSet |> Array.map(fun c -> (System.Text.Encoding.ASCII.GetBytes (c.ToString())).[0]) |> Set.ofArray
    let lengthDeterminantSize = GetNumberOfBitsForNonNegativeInt (asn1Max-asn1Min)
    let charSizeInBits =
        match  bAsciiEncoding with
        | true      -> 8
        | false     -> GetNumberOfBitsForNonNegativeInt (alphaSet.Length - 1)
    let encClass, minSizeInBits, maxSizeInBits =
        match  bAsciiEncoding, bAsn1FixedSize, sizeClass  with
        | true, true, PrivateAutoSize                                          -> Acn_Enc_String_Ascii_FixSize asn1Max, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
        | true, true, PrivateNullTerminated  b                                 ->
            match allowedBytes.Contains b && (not (b=0uy && alphaSet.Length = 128))with
            | true  -> raise(SemanticError(errLoc, "The termination-pattern defines a character which belongs to the allowed values of the ASN.1 type. Use another value in the termination-pattern or apply different constraints in the ASN.1 type."))
            | false -> Acn_Enc_String_Ascii_Null_Terminated b, (asn1Max+1)*charSizeInBits, (asn1Max+1)*charSizeInBits
        | true, true, PrivateFixedSize(nItems)    when nItems = asn1Max        -> Acn_Enc_String_Ascii_FixSize asn1Max, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
        | true, true, PrivateFixedSize(nItems)                                 -> raise(BugErrorException(sprintf "size property value should be set to %A" asn1Max))
        | true, true, PrivateExternalField                                     -> Acn_Enc_String_Ascii_External_Field_Determinant , asn1Max*charSizeInBits,  asn1Max*charSizeInBits

        | true, false, PrivateAutoSize                                         -> Acn_Enc_String_Ascii_Internal_Field_Determinant lengthDeterminantSize, lengthDeterminantSize + asn1Min*charSizeInBits, lengthDeterminantSize + asn1Max*charSizeInBits
        | true, false, PrivateNullTerminated b                                 ->
            match allowedBytes.Contains b && (not (b=0uy && alphaSet.Length = 128))with
            | true  -> raise(SemanticError(errLoc, "The termination-pattern defines a character which belongs to the allowed values of the ASN.1 type. Use another value in the termination-pattern or apply different constraints in the ASN.1 type."))
            | false -> Acn_Enc_String_Ascii_Null_Terminated b, (asn1Max+1)*charSizeInBits, (asn1Max+1)*charSizeInBits
        | true, false, PrivateFixedSize(nItems)                                -> raise(BugErrorException(sprintf "The size constraints of the ASN.1  allows variable items (%A .. %A). Therefore, you should either remove the size property (in which case the size determinant will be encoded automatically exactly like uPER), or use a an Integer field as size determinant" asn1Min asn1Max))
        | true, false, PrivateExternalField                                    -> Acn_Enc_String_Ascii_External_Field_Determinant , asn1Max*charSizeInBits,  asn1Max*charSizeInBits

        | false, true, PrivateAutoSize                                         -> Acn_Enc_String_CharIndex_FixSize asn1Max, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
        | false, true, PrivateNullTerminated  _                                -> raise(BugErrorException(sprintf "when a string type has the acn property 'size null-terminated' it must also have the acn property 'encoding ASCII'" ))
        | false, true, PrivateFixedSize(nItems)    when nItems = asn1Max       -> Acn_Enc_String_CharIndex_FixSize asn1Max, asn1Max*charSizeInBits,  asn1Max*charSizeInBits
        | false, true, PrivateFixedSize(nItems)                                -> raise(BugErrorException(sprintf "size property value should be set to %A" asn1Max))
        | false, true, PrivateExternalField                                   -> Acn_Enc_String_CharIndex_External_Field_Determinant , asn1Max*charSizeInBits,  asn1Max*charSizeInBits

        | false, false, PrivateAutoSize                                        -> Acn_Enc_String_CharIndex_Internal_Field_Determinant lengthDeterminantSize, lengthDeterminantSize + asn1Min*charSizeInBits, lengthDeterminantSize + asn1Max*charSizeInBits
        | false, false, PrivateNullTerminated  _                               -> raise(BugErrorException(sprintf "when a string type has the acn property 'size null-terminated' it must also have the acn property 'encoding ASCII'" ))
        | false, false, PrivateFixedSize(nItems)                               -> raise(BugErrorException(sprintf "The size constraints of the ASN.1  allows variable items (%A .. %A). Therefore, you should either remove the size property (in which case the size determinant will be encoded automatically exactly like uPER), or use a an Integer field as size determinant" asn1Min asn1Max))
        | false, false, PrivateExternalField                                   -> Acn_Enc_String_CharIndex_External_Field_Determinant , asn1Min*charSizeInBits, asn1Max*charSizeInBits

    encClass, alignment, minSizeInBits+alignmentSize, maxSizeInBits+alignmentSize, fs

//banner text from this link
//http://patorjk.com/software/taag/#p=display&v=2&f=ANSI%20Shadow&t=Octet%20String%0A
(*
 ███████╗███████╗ ██████╗ ██╗   ██╗███████╗███╗   ██╗ ██████╗███████╗     ██████╗ ███████╗     ██████╗  ██████╗████████╗███████╗████████╗ ██╗██████╗ ██╗████████╗    ███████╗████████╗██████╗ ██╗███╗   ██╗ ██████╗
██╔════╝██╔════╝██╔═══██╗██║   ██║██╔════╝████╗  ██║██╔════╝██╔════╝    ██╔═══██╗██╔════╝    ██╔═══██╗██╔════╝╚══██╔══╝██╔════╝╚══██╔══╝██╔╝██╔══██╗██║╚══██╔══╝    ██╔════╝╚══██╔══╝██╔══██╗██║████╗  ██║██╔════╝
███████╗█████╗  ██║   ██║██║   ██║█████╗  ██╔██╗ ██║██║     █████╗      ██║   ██║█████╗      ██║   ██║██║        ██║   █████╗     ██║  ██╔╝ ██████╔╝██║   ██║       ███████╗   ██║   ██████╔╝██║██╔██╗ ██║██║  ███╗
╚════██║██╔══╝  ██║▄▄ ██║██║   ██║██╔══╝  ██║╚██╗██║██║     ██╔══╝      ██║   ██║██╔══╝      ██║   ██║██║        ██║   ██╔══╝     ██║ ██╔╝  ██╔══██╗██║   ██║       ╚════██║   ██║   ██╔══██╗██║██║╚██╗██║██║   ██║
███████║███████╗╚██████╔╝╚██████╔╝███████╗██║ ╚████║╚██████╗███████╗    ╚██████╔╝██║         ╚██████╔╝╚██████╗   ██║   ███████╗   ██║██╔╝   ██████╔╝██║   ██║       ███████║   ██║   ██║  ██║██║██║ ╚████║╚██████╔╝
╚══════╝╚══════╝ ╚══▀▀═╝  ╚═════╝ ╚══════╝╚═╝  ╚═══╝ ╚═════╝╚══════╝     ╚═════╝ ╚═╝          ╚═════╝  ╚═════╝   ╚═╝   ╚══════╝   ╚═╝╚═╝    ╚═════╝ ╚═╝   ╚═╝       ╚══════╝   ╚═╝   ╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝ ╚═════╝
*)

let GetOctetBitSeqofEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (id:ReferenceToType) asn1Min asn1Max internalMinSize internalMaxSize (acnParams: AcnParameter list) (us:State) =
    let acnProps = getAcnProps acnTypes id
    let bAsn1FixedSize = asn1Min = asn1Max
    let alignment, alignmentSize = GetAlignment acnProps
    let sizeClass, fs = getPrivateSizeableEncodingClass acnTypes acn  id acnParams us
    let encClass =
        match sizeClass with
        | PrivateFixedSize c when bAsn1FixedSize && asn1Min = c           -> FixedSize c
        | PrivateFixedSize c          ->
            raise(SemanticError(errLoc, sprintf "The size constraints of the ASN.1  allows variable items (%A .. %A). Therefore, you should either remove the size property (in which case the size determinant will be encoded automatically exactly like uPER), or use a an Integer field as size determinant" asn1Min asn1Max))
        | PrivateAutoSize               -> AutoSize
        | PrivateExternalField          -> ExternalField
        | PrivateNullTerminated _       -> raise(SemanticError(errLoc, "NULL TERMINATED cannot be applied in this type"))
    let minSize, maxSize =
        match encClass with
        | FixedSize   s     -> s*internalMinSize, s*internalMaxSize
        | AutoSize          ->
            let det = GetNumberOfBitsForNonNegativeInt(asn1Max-asn1Min)
            det + asn1Min*internalMinSize, det + asn1Max*internalMaxSize
        | ExternalField     -> asn1Min*internalMinSize, asn1Max*internalMaxSize
    encClass, alignment, minSize+alignmentSize, maxSize+alignmentSize, fs

let GetOctetStringEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.OctetString) (acnParams: AcnParameter list) (us:State) =
    GetOctetBitSeqofEncodingClass acn  acnTypes errLoc a.id  a.minSize a.maxSize 8 8 acnParams us

let GetBitStringEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.BitString) (acnParams: AcnParameter list) (us:State) =
    GetOctetBitSeqofEncodingClass acn  acnTypes errLoc a.id  a.minSize a.maxSize 1 1 acnParams us

let GetSequenceOfEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.SequenceOf) internalMinSize internalMaxSize (acnParams: AcnParameter list) (us:State) =
    GetOctetBitSeqofEncodingClass acn  acnTypes errLoc a.id  a.minSize a.maxSize internalMinSize internalMaxSize acnParams us

(*
███████╗███████╗ ██████╗ ██╗   ██╗███████╗███╗   ██╗ ██████╗███████╗     ██████╗██╗  ██╗██╗██╗     ██████╗
██╔════╝██╔════╝██╔═══██╗██║   ██║██╔════╝████╗  ██║██╔════╝██╔════╝    ██╔════╝██║  ██║██║██║     ██╔══██╗
███████╗█████╗  ██║   ██║██║   ██║█████╗  ██╔██╗ ██║██║     █████╗      ██║     ███████║██║██║     ██║  ██║
╚════██║██╔══╝  ██║▄▄ ██║██║   ██║██╔══╝  ██║╚██╗██║██║     ██╔══╝      ██║     ██╔══██║██║██║     ██║  ██║
███████║███████╗╚██████╔╝╚██████╔╝███████╗██║ ╚████║╚██████╗███████╗    ╚██████╗██║  ██║██║███████╗██████╔╝
╚══════╝╚══════╝ ╚══▀▀═╝  ╚═════╝ ╚══════╝╚═╝  ╚═══╝ ╚═════╝╚══════╝     ╚═════╝╚═╝  ╚═╝╚═╝╚══════╝╚═════╝
*)

let GetSeqChildOptionality (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (chType: Asn1Type) (oldOptionality:BAst.Asn1Optionality option) (acnParams: AcnParameter list) (us:State) =
    let defValue =
        match oldOptionality with
        | Some(BAst.Default v)      -> Some v
        | _                         -> None

    match oldOptionality with
    | None                      -> None, us
    | Some(BAst.AlwaysAbsent)   -> Some(AlwaysAbsent), us
    | Some(BAst.AlwaysPresent)  -> Some(AlwaysPresent), us
    | Some(BAst.Optional)
    | Some(BAst.Default _)      ->
        match acn.References |> Seq.tryFind(fun x -> x.TypeID = chType.id.AcnAbsPath && x.Kind = AcnTypes.PresenceBool) with
        | None          -> Some (Optional {Optional.defaultValue = defValue; ancEncodingClass = OptionLikeUper}), us
        | Some(r)       -> Some (Optional {Optional.defaultValue = defValue; ancEncodingClass = OptionExtField}), us

(*
 ██████╗██╗  ██╗ ██████╗ ██╗ ██████╗███████╗     ██████╗██╗  ██╗██╗██╗     ██████╗
██╔════╝██║  ██║██╔═══██╗██║██╔════╝██╔════╝    ██╔════╝██║  ██║██║██║     ██╔══██╗
██║     ███████║██║   ██║██║██║     █████╗      ██║     ███████║██║██║     ██║  ██║
██║     ██╔══██║██║   ██║██║██║     ██╔══╝      ██║     ██╔══██║██║██║     ██║  ██║
╚██████╗██║  ██║╚██████╔╝██║╚██████╗███████╗    ╚██████╗██║  ██║██║███████╗██████╔╝
 ╚═════╝╚═╝  ╚═╝ ╚═════╝ ╚═╝ ╚═════╝╚══════╝     ╚═════╝╚═╝  ╚═╝╚═╝╚══════╝╚═════╝
*)
let getChildLinks (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (chType: Asn1Type)  (acnParams: AcnParameter list) (us:State) =

    let newLinks =
        acn.References |>
        List.filter(fun x -> x.TypeID = chType.id.AcnAbsPath) |>
        List.filter(fun r ->
            match r.Kind with
            | AcnTypes.SizeDeterminant      -> false
            | AcnTypes.RefTypeArgument _    -> false
            | AcnTypes.ChoiceDeterminant  -> false
            | AcnTypes.PresenceBool         -> true
            | AcnTypes.PresenceInt intVal   -> true
            | AcnTypes.PresenceStr strVal   -> true)
    let presenceIsHandleByExtField = not newLinks.IsEmpty
    presenceIsHandleByExtField , us

let GetChoiceEncodingClass (acn:AcnTypes.AcnAst)  (acnTypes:Map<AcnTypes.AbsPath,AcnTypes.AcnType>) errLoc (a:BAst.Choice) (children:ChChildInfo list) (acnParams: AcnParameter list) (us:State) =
    let acnProps = getAcnProps acnTypes a.id
    let alignment, alignmentSize = GetAlignment acnProps
    let encClass, nus, indexSize =
        match acn.References |> Seq.tryFind(fun x -> x.TypeID = a.id.AcnAbsPath && x.Kind = AcnTypes.ChoiceDeterminant) with
        | Some(r)       ->
            match children |> Seq.exists(fun c -> c.presenceIsHandleByExtField) with
            | true  -> raise(SemanticError(errLoc, "ACN property 'determinant' can not be applied when children have their own presence conditions"))
            | false -> ()
            EnumDeterminant, us, 0
        | None  ->
            match children |> Seq.exists(fun c -> c.presenceIsHandleByExtField) with
            | true  -> PresentWhenOnChildren, us, 0
            | false ->
                let indexSize = int (GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children)))
                EmbeddedChoiceIndexLikeUper, us, indexSize

    let acnMaxSizeInBits = alignmentSize + indexSize + (children |> List.map(fun c -> c.chType.acnMaxSizeInBits) |> List.sum)
    let acnMinSizeInBits = alignmentSize + indexSize + (children |> List.map(fun c -> c.chType.acnMinSizeInBits) |> List.sum)

    encClass, alignment, acnMinSizeInBits, acnMaxSizeInBits, nus
