module acn_c
open System
open System.Numerics
open Ast

let A () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "A" []

let MF (soMF:string option) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "MF" [("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let Tas (sName:string) (sStar:string) (arrsLocalVariables:seq<string>) (sContent:string) (arrsExtraParams:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Tas_encode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("arrsExtraParams",(arrsExtraParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "acn" "Tas_decode" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("arrsLocalVariables",(arrsLocalVariables|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("arrsExtraParams",(arrsExtraParams|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintType (sMainBody:string) (bAligmentApplied:bool) (sAligmentValue:string) (bHasDependencies:bool) (sDependencyUpdates:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PrintType_encode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("sAligmentValue",(if sAligmentValue = null then null else ST.StrHelper sAligmentValue:>Object) );("bHasDependencies",bHasDependencies :>Object);("sDependencyUpdates",(if sDependencyUpdates = null then null else ST.StrHelper sDependencyUpdates:>Object) )]
    | Decode    ->
        ST.call "acn" "PrintType_decode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("sAligmentValue",(if sAligmentValue = null then null else ST.StrHelper sAligmentValue:>Object) );("bHasDependencies",bHasDependencies :>Object);("sDependencyUpdates",(if sDependencyUpdates = null then null else ST.StrHelper sDependencyUpdates:>Object) )]

let PrintTypeNoUpdate (sMainBody:string) (bAligmentApplied:bool) (sAligmentValue:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PrintTypeNoUpdate_encode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("sAligmentValue",(if sAligmentValue = null then null else ST.StrHelper sAligmentValue:>Object) )]
    | Decode    ->
        ST.call "acn" "PrintTypeNoUpdate_decode" [("sMainBody",(if sMainBody = null then null else ST.StrHelper sMainBody:>Object) );("bAligmentApplied",bAligmentApplied :>Object);("sAligmentValue",(if sAligmentValue = null then null else ST.StrHelper sAligmentValue:>Object) )]

let PositiveInteger_ConstSize (p:string) (nFixedSize:BigInteger) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_encode" [("p",p :>Object);("nFixedSize",nFixedSize :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_decode" [("p",p :>Object);("nFixedSize",nFixedSize :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_8 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_8_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_8_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_big_endian_16 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_big_endian_16_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_big_endian_16_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_big_endian_32 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_big_endian_32_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_big_endian_32_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_big_endian_64 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_big_endian_64_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_big_endian_64_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_little_endian_16 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_little_endian_16_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_little_endian_16_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_little_endian_32 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_little_endian_32_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_little_endian_32_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_ConstSize_little_endian_64 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_ConstSize_little_endian_64_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_ConstSize_little_endian_64_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let PositiveInteger_VarSize_LengthEmbedded (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "PositiveInteger_VarSize_LengthEmbedded_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "PositiveInteger_VarSize_LengthEmbedded_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize (p:string) (nFixedSize:BigInteger) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_encode" [("p",p :>Object);("nFixedSize",nFixedSize :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_decode" [("p",p :>Object);("nFixedSize",nFixedSize :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_8 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_8_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_8_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_big_endian_16 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_big_endian_16_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_big_endian_16_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_big_endian_32 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_big_endian_32_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_big_endian_32_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_big_endian_64 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_big_endian_64_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_big_endian_64_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_little_endian_16 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_little_endian_16_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_little_endian_16_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_little_endian_32 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_little_endian_32_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_little_endian_32_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_ConstSize_little_endian_64 (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_ConstSize_little_endian_64_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_ConstSize_little_endian_64_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let TwosComplement_VarSize_LengthEmbedded (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "TwosComplement_VarSize_LengthEmbedded_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "TwosComplement_VarSize_LengthEmbedded_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let BCD_ConstSize (p:string) (nNibbles:BigInteger) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "BCD_ConstSize_encode" [("p",p :>Object);("nNibbles",nNibbles :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "BCD_ConstSize_decode" [("p",p :>Object);("nNibbles",nNibbles :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let BCD_VarSize_LengthEmbedded (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "BCD_VarSize_LengthEmbedded_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "BCD_VarSize_LengthEmbedded_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let BCD_VarSize_NullTerminated (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "BCD_VarSize_NullTerminated_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "BCD_VarSize_NullTerminated_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let ASCII_ConstSize (p:string) (nSizeInBytes:BigInteger) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ASCII_ConstSize_encode" [("p",p :>Object);("nSizeInBytes",nSizeInBytes :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "ASCII_ConstSize_decode" [("p",p :>Object);("nSizeInBytes",nSizeInBytes :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let ASCII_VarSize_LengthEmbedded (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ASCII_VarSize_LengthEmbedded_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "ASCII_VarSize_LengthEmbedded_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let ASCII_VarSize_NullTerminated (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ASCII_VarSize_NullTerminated_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "ASCII_VarSize_NullTerminated_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let ASCII_UINT_ConstSize (p:string) (nSizeInBytes:BigInteger) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ASCII_UINT_ConstSize_encode" [("p",p :>Object);("nSizeInBytes",nSizeInBytes :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "ASCII_UINT_ConstSize_decode" [("p",p :>Object);("nSizeInBytes",nSizeInBytes :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let ASCII_UINT_VarSize_LengthEmbedded (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ASCII_UINT_VarSize_LengthEmbedded_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "ASCII_UINT_VarSize_LengthEmbedded_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let ASCII_UINT_VarSize_NullTerminated (p:string) (soMF:string option) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ASCII_UINT_VarSize_NullTerminated_encode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]
    | Decode    ->
        ST.call "acn" "ASCII_UINT_VarSize_NullTerminated_decode" [("p",p :>Object);("soMF",(if soMF.IsNone then null else ST.StrHelper soMF.Value:>Object) )]

let Real_32_big_endian (p:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Real_32_big_endian_encode" [("p",p :>Object)]
    | Decode    ->
        ST.call "acn" "Real_32_big_endian_decode" [("p",p :>Object)]

let Real_64_big_endian (p:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Real_64_big_endian_encode" [("p",p :>Object)]
    | Decode    ->
        ST.call "acn" "Real_64_big_endian_decode" [("p",p :>Object)]

let Real_32_little_endian (p:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Real_32_little_endian_encode" [("p",p :>Object)]
    | Decode    ->
        ST.call "acn" "Real_32_little_endian_decode" [("p",p :>Object)]

let Real_64_little_endian (p:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Real_64_little_endian_encode" [("p",p :>Object)]
    | Decode    ->
        ST.call "acn" "Real_64_little_endian_decode" [("p",p :>Object)]

let Boolean (p:string) (ptr:string) (bEncValIsTrue:bool) (nSize:BigInteger) (arruTrueValueAsByteArray:seq<byte>) (arruFalseValueAsByteArray:seq<byte>) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Boolean_encode" [("p",p :>Object);("ptr",ptr :>Object);("bEncValIsTrue",bEncValIsTrue :>Object);("nSize",nSize :>Object);("arruTrueValueAsByteArray",arruTrueValueAsByteArray|>Seq.toArray :>Object);("arruFalseValueAsByteArray",arruFalseValueAsByteArray|>Seq.toArray :>Object)]
    | Decode    ->
        ST.call "acn" "Boolean_decode" [("p",p :>Object);("ptr",ptr :>Object);("bEncValIsTrue",bEncValIsTrue :>Object);("nSize",nSize :>Object);("arruTrueValueAsByteArray",arruTrueValueAsByteArray|>Seq.toArray :>Object);("arruFalseValueAsByteArray",arruFalseValueAsByteArray|>Seq.toArray :>Object)]

let Null (arruNullValueAsByteArray:seq<byte>) (nSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Null_encode" [("arruNullValueAsByteArray",arruNullValueAsByteArray|>Seq.toArray :>Object);("nSize",nSize :>Object)]
    | Decode    ->
        ST.call "acn" "Null_decode" [("arruNullValueAsByteArray",arruNullValueAsByteArray|>Seq.toArray :>Object);("nSize",nSize :>Object)]

let Null_empty_pattern () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "Null_empty_pattern" []

let Declare_EnumValueUInt () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "Declare_EnumValueUInt" []

let Declare_EnumValueSInt () =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "Declare_EnumValueSInt" []

let Enumerated_item (p:string) (sName:string) (nItemIdxOrVal:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Enumerated_item_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nItemIdxOrVal",nItemIdxOrVal :>Object)]
    | Decode    ->
        ST.call "acn" "Enumerated_item_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("nItemIdxOrVal",nItemIdxOrVal :>Object)]

let EnumeratedEncIdx (p:string) (sTasName:string) (arrsItem:seq<string>) (sActualCodecFunc:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "EnumeratedEncIdx_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sActualCodecFunc",(if sActualCodecFunc = null then null else ST.StrHelper sActualCodecFunc:>Object) )]
    | Decode    ->
        ST.call "acn" "EnumeratedEncIdx_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sActualCodecFunc",(if sActualCodecFunc = null then null else ST.StrHelper sActualCodecFunc:>Object) )]

let EnumeratedEncValues (p:string) (sTasName:string) (arrsItem:seq<string>) (sActualCodecFunc:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "EnumeratedEncValues_encode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sActualCodecFunc",(if sActualCodecFunc = null then null else ST.StrHelper sActualCodecFunc:>Object) )]
    | Decode    ->
        ST.call "acn" "EnumeratedEncValues_decode" [("p",p :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsItem",(arrsItem|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sActualCodecFunc",(if sActualCodecFunc = null then null else ST.StrHelper sActualCodecFunc:>Object) )]

let Acn_String_Ascii_FixSize (p:string) (nAsn1Max:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_Ascii_FixSize_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object)]
    | Decode    ->
        ST.call "acn" "Acn_String_Ascii_FixSize_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object)]

let Acn_String_Ascii_Null_Teminated (p:string) (nAsn1Max:BigInteger) (sNull:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_Ascii_Null_Teminated_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("sNull",(if sNull = null then null else ST.StrHelper sNull:>Object) )]
    | Decode    ->
        ST.call "acn" "Acn_String_Ascii_Null_Teminated_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("sNull",(if sNull = null then null else ST.StrHelper sNull:>Object) )]

let Acn_String_Ascii_External_Field_Determinant (p:string) (nAsn1Max:BigInteger) (sExtFld:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_Ascii_External_Field_Determinant_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]
    | Decode    ->
        ST.call "acn" "Acn_String_Ascii_External_Field_Determinant_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let Acn_String_Ascii_Internal_Field_Determinant (p:string) (nAsn1Max:BigInteger) (nAsn1Min:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_Ascii_Internal_Field_Determinant_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("nAsn1Min",nAsn1Min :>Object)]
    | Decode    ->
        ST.call "acn" "Acn_String_Ascii_Internal_Field_Determinant_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("nAsn1Min",nAsn1Min :>Object)]

let PrintAlphabet2 (arrnCharSet:seq<BigInteger>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "PrintAlphabet2" [("arrnCharSet",arrnCharSet|>Seq.toArray :>Object)]

let Acn_String_CharIndex_FixSize (p:string) (nAsn1Max:BigInteger) (arrnAlphabetAsciiCodes:seq<BigInteger>) (nCharSetSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_CharIndex_FixSize_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nCharSetSize",nCharSetSize :>Object)]
    | Decode    ->
        ST.call "acn" "Acn_String_CharIndex_FixSize_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nCharSetSize",nCharSetSize :>Object)]

let Acn_String_CharIndex_External_Field_Determinant (p:string) (nAsn1Max:BigInteger) (arrnAlphabetAsciiCodes:seq<BigInteger>) (nCharSetSize:BigInteger) (sExtFld:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_CharIndex_External_Field_Determinant_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nCharSetSize",nCharSetSize :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]
    | Decode    ->
        ST.call "acn" "Acn_String_CharIndex_External_Field_Determinant_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nCharSetSize",nCharSetSize :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let Acn_String_CharIndex_Internal_Field_Determinant (p:string) (nAsn1Max:BigInteger) (arrnAlphabetAsciiCodes:seq<BigInteger>) (nCharSetSize:BigInteger) (nAsn1Min:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Acn_String_CharIndex_Internal_Field_Determinant_encode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nCharSetSize",nCharSetSize :>Object);("nAsn1Min",nAsn1Min :>Object)]
    | Decode    ->
        ST.call "acn" "Acn_String_CharIndex_Internal_Field_Determinant_decode" [("p",p :>Object);("nAsn1Max",nAsn1Max :>Object);("arrnAlphabetAsciiCodes",arrnAlphabetAsciiCodes|>Seq.toArray :>Object);("nCharSetSize",nCharSetSize :>Object);("nAsn1Min",nAsn1Min :>Object)]

let string_InternalItem (p:string) (i:string) (nCharSetMaxIndex:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "string_InternalItem_encode" [("p",p :>Object);("i",i :>Object);("nCharSetMaxIndex",nCharSetMaxIndex :>Object)]
    | Decode    ->
        ST.call "acn" "string_InternalItem_decode" [("p",p :>Object);("i",i :>Object);("nCharSetMaxIndex",nCharSetMaxIndex :>Object)]

let str_FixedSize (p:string) (i:string) (sInternalItem:string) (nFixedSize:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "str_FixedSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object)]
    | Decode    ->
        ST.call "acn" "str_FixedSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nFixedSize",nFixedSize :>Object)]

let str_VarSize (p:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "str_VarSize_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object)]
    | Decode    ->
        ST.call "acn" "str_VarSize_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object)]

let str_VarSize_null_terminated (p:string) (nSizeMax:BigInteger) (sNullCharacter:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "str_VarSize_null_terminated_encode" [("p",p :>Object);("nSizeMax",nSizeMax :>Object);("sNullCharacter",(if sNullCharacter = null then null else ST.StrHelper sNullCharacter:>Object) )]
    | Decode    ->
        ST.call "acn" "str_VarSize_null_terminated_decode" [("p",p :>Object);("nSizeMax",nSizeMax :>Object);("sNullCharacter",(if sNullCharacter = null then null else ST.StrHelper sNullCharacter:>Object) )]

let str_external_field (p:string) (i:string) (sInternalItem:string) (nSizeMin:BigInteger) (nSizeMax:BigInteger) (sExtFld:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "str_external_field_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]
    | Decode    ->
        ST.call "acn" "str_external_field_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("nSizeMin",nSizeMin :>Object);("nSizeMax",nSizeMax :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let oct_sqf_external_field (p:string) (i:string) (sInternalItem:string) (noSizeMin:BigInteger option) (nSizeMax:BigInteger) (sExtFld:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "oct_sqf_external_field_encode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("noSizeMin",(if noSizeMin.IsNone then null else noSizeMin.Value:>Object) );("nSizeMax",nSizeMax :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]
    | Decode    ->
        ST.call "acn" "oct_sqf_external_field_decode" [("p",p :>Object);("i",i :>Object);("sInternalItem",(if sInternalItem = null then null else ST.StrHelper sInternalItem:>Object) );("noSizeMin",(if noSizeMin.IsNone then null else noSizeMin.Value:>Object) );("nSizeMax",nSizeMax :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let bit_string_external_field (p:string) (noSizeMin:BigInteger option) (nSizeMax:BigInteger) (sExtFld:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "bit_string_external_field_encode" [("p",p :>Object);("noSizeMin",(if noSizeMin.IsNone then null else noSizeMin.Value:>Object) );("nSizeMax",nSizeMax :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]
    | Decode    ->
        ST.call "acn" "bit_string_external_field_decode" [("p",p :>Object);("noSizeMin",(if noSizeMin.IsNone then null else noSizeMin.Value:>Object) );("nSizeMax",nSizeMax :>Object);("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let RefTypeParam_tmpVar (sName:string) (sTypeDecl:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "RefTypeParam_tmpVar" [("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("sTypeDecl",(if sTypeDecl = null then null else ST.StrHelper sTypeDecl:>Object) )]

let ReferenceType1 (p:string) (sName:string) (bAcnEncodeFuncRequiresResult:bool) (arrsArgs:seq<string>) (arrsLocalPrms:seq<string>) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ReferenceType1_encode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalPrms",(arrsLocalPrms|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]
    | Decode    ->
        ST.call "acn" "ReferenceType1_decode" [("p",p :>Object);("sName",(if sName = null then null else ST.StrHelper sName:>Object) );("bAcnEncodeFuncRequiresResult",bAcnEncodeFuncRequiresResult :>Object);("arrsArgs",(arrsArgs|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("arrsLocalPrms",(arrsLocalPrms|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let Sequence_presense_optChild (p:string) (sChName:string) (sErrCode:string) (sBitMaskName:string) (nByteIndex:BigInteger) (sAndMask:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_presense_optChild_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) );("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nByteIndex",nByteIndex :>Object);("sAndMask",(if sAndMask = null then null else ST.StrHelper sAndMask:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_presense_optChild_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) );("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) );("nByteIndex",nByteIndex :>Object);("sAndMask",(if sAndMask = null then null else ST.StrHelper sAndMask:>Object) )]

let Sequence_presense_optChild_pres_bool (p:string) (sChName:string) (sExtFldName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_presense_optChild_pres_bool_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_presense_optChild_pres_bool_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) )]

let Sequence_presense_optChild_pres_int (p:string) (sChName:string) (sExtFldName:string) (nIntVal:BigInteger) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_presense_optChild_pres_int_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("nIntVal",nIntVal :>Object)]
    | Decode    ->
        ST.call "acn" "Sequence_presense_optChild_pres_int_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("nIntVal",nIntVal :>Object)]

let Sequence_presense_optChild_pres_str (p:string) (sChName:string) (sExtFldName:string) (sVal:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_presense_optChild_pres_str_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_presense_optChild_pres_str_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sExtFldName",(if sExtFldName = null then null else ST.StrHelper sExtFldName:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let Sequence_mandatory_child (sChName:string) (sChildContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_mandatory_child_encode" [("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_mandatory_child_decode" [("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]

let Sequence_optional_child (p:string) (sChName:string) (sChildContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_optional_child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_optional_child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]

let Sequence_optional_always_present_child (p:string) (sChName:string) (sChildContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_optional_always_present_child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_optional_always_present_child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]

let Sequence_default_child (p:string) (sChName:string) (sChildContent:string) (sChildTypeDeclaration:string) (sDefaultValue:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_default_child_encode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sChildTypeDeclaration",(if sChildTypeDeclaration = null then null else ST.StrHelper sChildTypeDeclaration:>Object) );("sDefaultValue",(if sDefaultValue = null then null else ST.StrHelper sDefaultValue:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_default_child_decode" [("p",p :>Object);("sChName",(if sChName = null then null else ST.StrHelper sChName:>Object) );("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) );("sChildTypeDeclaration",(if sChildTypeDeclaration = null then null else ST.StrHelper sChildTypeDeclaration:>Object) );("sDefaultValue",(if sDefaultValue = null then null else ST.StrHelper sDefaultValue:>Object) )]

let Sequence (sChildren:string) (bHasUperOptionalChildren:bool) (nUperOptionalChildrenLength:BigInteger) (sBitMaskName:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Sequence_encode" [("sChildren",(if sChildren = null then null else ST.StrHelper sChildren:>Object) );("bHasUperOptionalChildren",bHasUperOptionalChildren :>Object);("nUperOptionalChildrenLength",nUperOptionalChildrenLength :>Object);("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) )]
    | Decode    ->
        ST.call "acn" "Sequence_decode" [("sChildren",(if sChildren = null then null else ST.StrHelper sChildren:>Object) );("bHasUperOptionalChildren",bHasUperOptionalChildren :>Object);("nUperOptionalChildrenLength",nUperOptionalChildrenLength :>Object);("sBitMaskName",(if sBitMaskName = null then null else ST.StrHelper sBitMaskName:>Object) )]

let JoinItems (sPart:string) (sNestedPart:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "JoinItems" [("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) )]

let ChoiceChild (p:string) (sChildID:string) (nChildIndex:BigInteger) (nLastItemIndex:BigInteger) (sChildContent:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ChoiceChild_encode" [("p",p :>Object);("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("nChildIndex",nChildIndex :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]
    | Decode    ->
        ST.call "acn" "ChoiceChild_decode" [("p",p :>Object);("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("nChildIndex",nChildIndex :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sChildContent",(if sChildContent = null then null else ST.StrHelper sChildContent:>Object) )]

let Choice (p:string) (arrsChildren:seq<string>) (nLastItemIndex:BigInteger) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Choice_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "acn" "Choice_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("nLastItemIndex",nLastItemIndex :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let ChoiceChild_preWhen (p:string) (sChildID:string) (sChildBody:string) (arrsConditions:seq<string>) (bFirst:bool) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ChoiceChild_preWhen_encode" [("p",p :>Object);("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("arrsConditions",(arrsConditions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bFirst",bFirst :>Object)]
    | Decode    ->
        ST.call "acn" "ChoiceChild_preWhen_decode" [("p",p :>Object);("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) );("arrsConditions",(arrsConditions|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("bFirst",bFirst :>Object)]

let ChoiceChild_preWhen_bool_condition (sExtFld:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceChild_preWhen_bool_condition" [("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) )]

let ChoiceChild_preWhen_int_condition (sExtFld:string) (nVal:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceChild_preWhen_int_condition" [("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("nVal",nVal :>Object)]

let ChoiceChild_preWhen_str_condition (sExtFld:string) (sVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceChild_preWhen_str_condition" [("sExtFld",(if sExtFld = null then null else ST.StrHelper sExtFld:>Object) );("sVal",(if sVal = null then null else ST.StrHelper sVal:>Object) )]

let Choice_preWhen (p:string) (arrsChildren:seq<string>) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Choice_preWhen_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "acn" "Choice_preWhen_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let ChoiceChild_Enum (p:string) (sEnmName:string) (sChildID:string) (sChildBody:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "ChoiceChild_Enum_encode" [("p",p :>Object);("sEnmName",(if sEnmName = null then null else ST.StrHelper sEnmName:>Object) );("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) )]
    | Decode    ->
        ST.call "acn" "ChoiceChild_Enum_decode" [("p",p :>Object);("sEnmName",(if sEnmName = null then null else ST.StrHelper sEnmName:>Object) );("sChildID",(if sChildID = null then null else ST.StrHelper sChildID:>Object) );("sChildBody",(if sChildBody = null then null else ST.StrHelper sChildBody:>Object) )]

let Choice_Enum (p:string) (arrsChildren:seq<string>) (sEnmExtFld:string) (sErrCode:string) codec =
    ST.lang <- Ast.ProgrammingLanguage.C
    match codec with
    | Encode    ->
        ST.call "acn" "Choice_Enum_encode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sEnmExtFld",(if sEnmExtFld = null then null else ST.StrHelper sEnmExtFld:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]
    | Decode    ->
        ST.call "acn" "Choice_Enum_decode" [("p",p :>Object);("arrsChildren",(arrsChildren|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object);("sEnmExtFld",(if sEnmExtFld = null then null else ST.StrHelper sEnmExtFld:>Object) );("sErrCode",(if sErrCode = null then null else ST.StrHelper sErrCode:>Object) )]

let PrintAcn_update_param (sTasName:string) (sStar:string) (sParamType:string) (sParamName:string) (sStarParm:string) (sContent:string) (arrsTmpVars:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "PrintAcn_update_param" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sStar",(if sStar = null then null else ST.StrHelper sStar:>Object) );("sParamType",(if sParamType = null then null else ST.StrHelper sParamType:>Object) );("sParamName",(if sParamName = null then null else ST.StrHelper sParamName:>Object) );("sStarParm",(if sStarParm = null then null else ST.StrHelper sStarParm:>Object) );("sContent",(if sContent = null then null else ST.StrHelper sContent:>Object) );("arrsTmpVars",(arrsTmpVars|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintAcn_update_param_body_choice_child (sChildPresentID:string) (sChildUpdateStatement:string) (bCheckSuccess:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "PrintAcn_update_param_body_choice_child" [("sChildPresentID",(if sChildPresentID = null then null else ST.StrHelper sChildPresentID:>Object) );("sChildUpdateStatement",(if sChildUpdateStatement = null then null else ST.StrHelper sChildUpdateStatement:>Object) );("bCheckSuccess",bCheckSuccess :>Object)]

let PrintAcn_update_param_body_choice (arrsChildUpdateStatements:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "PrintAcn_update_param_body_choice" [("arrsChildUpdateStatements",(arrsChildUpdateStatements|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PrintAcn_update_param_body (sPart:string) (sNestedPart:string) (bCheckSuccess:bool) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "PrintAcn_update_param_body" [("sPart",(if sPart = null then null else ST.StrHelper sPart:>Object) );("sNestedPart",(if sNestedPart = null then null else ST.StrHelper sNestedPart:>Object) );("bCheckSuccess",bCheckSuccess :>Object)]

let RefTypeArgument1 (v:string) (sTasName:string) (sParamName:string) (sRefTypePath:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "RefTypeArgument1" [("v",v :>Object);("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("sParamName",(if sParamName = null then null else ST.StrHelper sParamName:>Object) );("sRefTypePath",(if sRefTypePath = null then null else ST.StrHelper sRefTypePath:>Object) )]

let SizeDependency (v:string) (sCount:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "SizeDependency" [("v",v :>Object);("sCount",(if sCount = null then null else ST.StrHelper sCount:>Object) )]

let ChoiceDependencyEnum_Item (v:string) (sChildCID:string) (sEnumCName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceDependencyEnum_Item" [("v",v :>Object);("sChildCID",(if sChildCID = null then null else ST.StrHelper sChildCID:>Object) );("sEnumCName",(if sEnumCName = null then null else ST.StrHelper sEnumCName:>Object) )]

let ChoiceDependencyEnum (sTasName:string) (arrsChoiceEnumItems:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceDependencyEnum" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChoiceEnumItems",(arrsChoiceEnumItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let PresenceDependency (v:string) (sSeqPath:string) (sChildName:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "PresenceDependency" [("v",v :>Object);("sSeqPath",(if sSeqPath = null then null else ST.StrHelper sSeqPath:>Object) );("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) )]

let ChoiceDependencyIntPres_child (v:string) (sChildName:string) (nChildRetVal:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceDependencyIntPres_child" [("v",v :>Object);("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("nChildRetVal",nChildRetVal :>Object)]

let ChoiceDependencyStrPres_child (v:string) (sChildName:string) (sChildRetVal:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceDependencyStrPres_child" [("v",v :>Object);("sChildName",(if sChildName = null then null else ST.StrHelper sChildName:>Object) );("sChildRetVal",(if sChildRetVal = null then null else ST.StrHelper sChildRetVal:>Object) )]

let ChoiceDependencyPres (sTasName:string) (arrsChoiceItems:seq<string>) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "ChoiceDependencyPres" [("sTasName",(if sTasName = null then null else ST.StrHelper sTasName:>Object) );("arrsChoiceItems",(arrsChoiceItems|>Seq.map (fun s ->  if s = null then null else (ST.StrHelper s):>Object) |> Seq.toArray) :>Object)]

let MultiUpdateCheckWithFirstValue (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "MultiUpdateCheckWithFirstValue" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let MultiUpdateCheckWithFirstValueInteger (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "MultiUpdateCheckWithFirstValueInteger" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let MultiParamUpdateCheckWithFirstValue (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "MultiParamUpdateCheckWithFirstValue" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let CheckBeforeAssignToIntField_min_max (sTmpVar0:string) (nMin:BigInteger) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "CheckBeforeAssignToIntField_min_max" [("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("nMin",nMin :>Object);("nMax",nMax :>Object)]

let CheckBeforeAssignToIntField_max (sTmpVar0:string) (nMax:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "CheckBeforeAssignToIntField_max" [("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("nMax",nMax :>Object)]

let CheckBeforeAssignToIntField_min (sTmpVar0:string) (nMin:BigInteger) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "CheckBeforeAssignToIntField_min" [("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("nMin",nMin :>Object)]

let UpdateAsn1Field (sAcnField:string) (sTmpVar:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "UpdateAsn1Field" [("sAcnField",(if sAcnField = null then null else ST.StrHelper sAcnField:>Object) );("sTmpVar",(if sTmpVar = null then null else ST.StrHelper sTmpVar:>Object) )]

let UpdateAsn1IntegerField (sAcnField:string) (sTmpVar0:string) (sAsn1FieldType:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "UpdateAsn1IntegerField" [("sAcnField",(if sAcnField = null then null else ST.StrHelper sAcnField:>Object) );("sTmpVar0",(if sTmpVar0 = null then null else ST.StrHelper sTmpVar0:>Object) );("sAsn1FieldType",(if sAsn1FieldType = null then null else ST.StrHelper sAsn1FieldType:>Object) )]

let MultiUpdateCheckWithFirstValue2 (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "MultiUpdateCheckWithFirstValue2" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

let MultiParamUpdateCheckWithFirstValue2 (sCurValue:string) (sFirstValue:string) =
    ST.lang <- Ast.ProgrammingLanguage.C
    ST.call "acn" "MultiParamUpdateCheckWithFirstValue2" [("sCurValue",(if sCurValue = null then null else ST.StrHelper sCurValue:>Object) );("sFirstValue",(if sFirstValue = null then null else ST.StrHelper sFirstValue:>Object) )]

