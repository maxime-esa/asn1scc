module spark_main

open System.Numerics
open FsUtils
open Ast
open System.IO
open uPER
open spark_utils



let CreateMainFile (r:AstRoot) (acn:AcnTypes.AcnAstResolved) outDir vasName =
    let includedPackages =  r.Modules |> List.collect(fun im -> if (ModuleHasAutoCodecs im r) then [ToC im.Name.Value; ToC im.Name.Value+"_auto_encs_decs"] else [ToC im.Name.Value])
    let usedPackages = r.Modules |> Seq.map(fun x -> ToC x.Name.Value)
    let encoding = "uPER"
    let PrintTestCase (v:ValueAssignment) (m:Asn1Module) =
        let tasName = match v.Type.Kind with
                      | ReferenceType(md, ts, _)   -> ts.Value
                      | _                       -> ""
        let sTasName = spark_variables.GetTasNameByKind v.Type.Kind m r
        let packageName = ToC m.Name.Value
        let sValue = spark_variables.PrintAsn1Value v.Value false false v.Type (sTasName,0) m r
        let sAsn1Val0 = (PrintAsn1.PrintValueAss v m).Replace("\"","'")
        let sAsn1Val = match sAsn1Val0.Length>1000 with
                       | true -> sAsn1Val0.Substring(0,1000)
                       | false -> sAsn1Val0
        let bGenIsValidFunc = HasValidateFunc v.Type r
        r.Encodings |> Seq.map(fun e -> match e with
                                        | UPER  -> smain.PrintMain_call_codec sTasName packageName "uPER" sValue sAsn1Val (ToC v.Name.Value) bGenIsValidFunc (r.CheckWithOss && v.Name.Value = "testPDU")
                                        | ACN   -> smain.PrintMain_call_codec sTasName packageName "ACN" sValue sAsn1Val (ToC v.Name.Value) bGenIsValidFunc false
//                                            match acn.Parameters |> Seq.exists(fun p -> p.ModName = m.Name.Value && p.TasName = tasName) with
//                                            | false -> smain.PrintMain_call_codec sTasName packageName "ACN" sValue sAsn1Val (ToC v.Name.Value) bGenIsValidFunc false
//                                            | true  -> ""
                                        | XER   -> smain.PrintMain_call_codec sTasName packageName "XER" sValue sAsn1Val (ToC v.Name.Value) bGenIsValidFunc (r.CheckWithOss && v.Name.Value = "testPDU")
                                        | BER   -> smain.PrintMain_call_codec sTasName packageName "BER" sValue sAsn1Val (ToC v.Name.Value) bGenIsValidFunc (r.CheckWithOss && v.Name.Value = "testPDU")
                                 ) |> Seq.StrJoin "\n\n"
        
    
    let funcs = seq {
            for m in r.Modules do
                let autoVases = m.TypeAssignments |> Seq.collect(fun x -> acn_backend_logic.GenerateVases x m.Name r acn) |> Seq.toList
                for v in m.ValueAssignments@autoVases do
                    match v.Type.Kind with
                    | ReferenceType(md,ts, _)  -> 
                        let actMod = r.GetModuleByName md
                        if vasName = "ALL" || v.Name.Value = vasName then
                            yield PrintTestCase v actMod
                    | _                 -> ()
        }
    let initCalls = seq {
            for m in r.Modules do
                for tas in m.TypeAssignments do
                    let sTasName = GetTasCName tas.Name.Value r.TypePrefix
                    yield smain.PrintMain_call_init sTasName (ToC m.Name.Value)
        }
    let choiceVases = seq {
            for m in r.Modules do
                for v in m.ValueAssignments do
                    match v.Type.Kind, Ast.IsOrContainsChoice v.Type r with
                    | ReferenceType(md, ts, _), true     ->
                        let sTasName = GetTasCName ts.Value r.TypePrefix
                        let mdName = ToC md.Value
                        let vsName = ToC v.Name.Value
                        let sVasModule = m.CName
                        yield smain.PrintMain_call_choice_valAss sTasName mdName vsName sVasModule
                    | _ -> ()
        }

    let content = smain.PrintMain_testCases includedPackages funcs usedPackages initCalls choiceVases r.CheckWithOss
    let outFileName = Path.Combine(outDir, "mainprogram.adb")
    File.WriteAllText(outFileName, content.Replace("\r",""))



let CreateSparkIndexFile (r:AstRoot) bGenTestCases outDir =
    let mods = r.Modules |> Seq.map(fun x -> (ToC x.Name.Value).ToLower()) |>Seq.toList
    let mds = match bGenTestCases with
              | true  -> mods @ (r.Modules |> Seq.filter(fun x -> ModuleHasAutoCodecs x r) |> Seq.map(fun x -> (ToC x.Name.Value+"_auto_encs_decs").ToLower() ) |>Seq.toList)
              | false -> mods
    let fullPath = (System.IO.Path.GetFullPath outDir) + System.String(System.IO.Path.DirectorySeparatorChar,1)
    let lines = (ss.rtlModuleName())::mds |> List.map(fun x -> smain.PrintLineInIndexFile x fullPath)
    let content = match bGenTestCases with
                  | true    -> smain.PrintIndexFile ("mainprogram    main_program  is in MainProgram.adb"::lines)
                  | false   -> smain.PrintIndexFile lines
    let outFileName = Path.Combine(outDir, "spark.idx")
    File.WriteAllText(outFileName, content.Replace("\r",""))

let CreateMakeFile (r:AstRoot) outDir =
    let mods = ss.rtlModuleName()::(r.Modules |> List.filter(fun x -> (ModuleHasAdaBody x r)) |>List.map(fun m -> (ToC m.Name.Value).ToLower() ))
    let content = smain.PrintMakeFile  mods
    let outFileName = Path.Combine(outDir, "Makefile")
    File.WriteAllText(outFileName, content.Replace("\r",""))

