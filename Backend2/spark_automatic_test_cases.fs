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

module spark_automatic_test_cases

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils


let GetEncodingString = function    
    | UPER  -> "uPER"
    | ACN   -> "ACN"
    | BER   -> "BER"
    | XER   -> "XER"


let PrintModuleSpec outDir (m:Asn1Module) r (acn:AcnTypes.AcnAstResolved) =
    let packageName = ToC m.Name.Value
    let PrintCodec (t:TypeAssignment)  = 
        let sTasName = GetTasCName t.Name.Value r.TypePrefix
        let printCodecAux encStr = stc.PrintCodec_spec packageName sTasName encStr
        r.Encodings |> Seq.map GetEncodingString |> Seq.map printCodecAux
    let includedPackages =  ss.rtlModuleName()::packageName::(m.Imports |> List.map (fun im -> ToC im.Name.Value)) 
    let funcs = m.TypeAssignments |> Seq.collect PrintCodec 
    let content = stc.PrintCodecsFile_spec packageName includedPackages funcs
    let fileName = Path.Combine(outDir, (ToC m.Name.Value).ToLower() + "_auto_encs_decs.ads")
    File.WriteAllText(fileName, content.Replace("\r",""))


type StatementKind =
    |Update_DecIn_param_no_result     of AcnTypes.AcnParameter       
    |Update_DecIn_param_with_result   of AcnTypes.AcnParameter     
    |Validate_input
    |Encode_input_with_result
    |Encode_input_no_result
    |Decode_output
    |Validate_output
    |Compare_input_output

let PrintModuleBody outDir (m:Asn1Module) r (acn:AcnTypes.AcnAstResolved) =
    let packageName = ToC m.Name.Value
    let PrintCodec (t:TypeAssignment)  = 
        let PrintCodeAux (enc:Asn1Encoding) =
            let sEnc = GetEncodingString enc
            let sTasName = GetTasCName t.Name.Value r.TypePrefix
            let bHasValidFunc = HasValidateFunc t.Type r
            let prmsEncInDecOut, prmsDecIn = 
                match enc with
                | ACN  -> 
                    let allParams = acn.Parameters |> List.filter(fun p -> p.ModName = m.Name.Value && p.TasName = t.Name.Value) 
                    allParams |> List.filter(fun x -> x.Mode = AcnTypes.EncodeDecodeMode), allParams |> List.filter(fun x -> x.Mode = AcnTypes.DecodeMode)
                | _      -> [],[]
            let arrsEncInDecOutParamsNames = prmsEncInDecOut |> List.map(fun p -> ToC p.Name)
            let arrsDecInParamsNames = prmsDecIn |> List.map(fun p -> ToC p.Name)
            let arrsParamNames = arrsEncInDecOutParamsNames@arrsDecInParamsNames
            let statements =
                seq {
                    for p in prmsDecIn do
                        if acn_backend_logic.Update_param_function_requires_result p.Name t m r acn then
                            yield Update_DecIn_param_with_result p
                        else
                            yield Update_DecIn_param_no_result   p
                    if bHasValidFunc then yield Validate_input
                    if bHasValidFunc then yield Encode_input_with_result else yield Encode_input_no_result
                    yield Decode_output
                    if bHasValidFunc then yield Validate_output
                    yield Compare_input_output
                } |> Seq.toList

            let printStatement stm sNestedContent = 
                let content, bCanFail = 
                    match stm with
                    |Update_DecIn_param_no_result(p)    -> stc.Codec_UpdateDecInParam_no_result packageName sTasName (ToC p.Name), false
                    |Update_DecIn_param_with_result(p)  -> stc.Codec_UpdateDecInParam_with_result packageName sTasName (ToC p.Name), true
                    |Validate_input                     -> stc.Codec_validate_input packageName sTasName, true
                    |Encode_input_with_result           -> stc.Codec_Encode_with_result packageName sTasName sEnc arrsEncInDecOutParamsNames, true
                    |Encode_input_no_result             -> stc.Codec_Encode_no_result packageName sTasName sEnc arrsEncInDecOutParamsNames, false
                    |Decode_output                      -> stc.Codec_Decode packageName sTasName sEnc arrsParamNames, true
                    |Validate_output                    -> stc.Codec_validate_output packageName sTasName , true
                    |Compare_input_output               -> stc.Codec_compare_input_with_output arrsEncInDecOutParamsNames sTasName, true
                stc.JoinItems content bCanFail sNestedContent

            let rec printStatements  = function
                |[]     -> null
                |x::xs  -> printStatement x  (printStatements xs)

            let GetValueFromParam (p:AcnTypes.AcnParameter) =
                let asn1Type = Ast.AcnAsn1Type2Asn1Type p.Asn1Type
                let value = {Asn1Value.Kind = (acn_backend_logic.GenerateValues asn1Type m.Name r acn |> Seq.head); Location = emptyLocation}
                spark_variables.PrintAsn1Value value false false asn1Type (sTasName,0) {m with Name ="".AsLoc} r

            

            let arrsEncInDecOutParamsLocalVars = prmsEncInDecOut |> Seq.map(fun p -> stc.Codec_declare_EncInDecOut_variable (ToC p.Name) (spark_spec.DeclateAcnAsn1Type p.Asn1Type {m with Name = "".AsLoc} r) (GetValueFromParam p) )
            let arrsDecInLocalVars = prmsDecIn |> Seq.map(fun p -> stc.Codec_declare_DecIn_variable  (ToC p.Name) (spark_spec.DeclateAcnAsn1Type p.Asn1Type {m with Name = "".AsLoc} r) )
            let sNestedStatements = printStatements statements
            stc.PrintCodec_body packageName sTasName sEnc arrsEncInDecOutParamsLocalVars arrsDecInLocalVars sNestedStatements
        r.Encodings |> Seq.map PrintCodeAux

    let includedPackages =  packageName::(m.Imports |> List.map (fun im -> ToC im.Name.Value)) 
    
    let tass = m.TypeAssignments 
               |> Seq.choose(fun x -> 
                                match x.Type.Kind with
                                | Integer           -> None
                                | Real              -> None
                                | Boolean           -> None
                                | ReferenceType(modName, refName,_)  -> 
                                    match m.Name.Value = modName.Value with
                                    | true -> None
                                    | false -> Some ( (ToC modName.Value) + "." + (Ast.GetTasCName refName.Value r.TypePrefix)) 
                                | NullType          -> None
                                | IA5String         -> None
                                | NumericString     -> None
                                | _                 -> Some ( (ToC m.Name.Value) + "." + (Ast.GetTasCName x.Name.Value r.TypePrefix)) )
    
    let funcs = m.TypeAssignments |> Seq.collect PrintCodec 
    let content = stc.PrintCodecsFile_body packageName includedPackages tass funcs
    let fileName = Path.Combine(outDir, (ToC m.Name.Value).ToLower() + "_auto_encs_decs.adb")
    File.WriteAllText(fileName, content.Replace("\r",""))

let CreateFile f outDir (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    f.Modules |> 
    Seq.iter(fun m -> 
                if (ModuleHasAutoCodecs m r) then 
                    PrintModuleSpec outDir m r acn
                    PrintModuleBody outDir m r acn) 





let CreateTestCases (r:AstRoot) (acn:AcnTypes.AcnAstResolved) outDir  =
    r.Files |> Seq.iter(fun f -> CreateFile f outDir r acn)  









