open Argu
open FsUtils
open System
open System.IO
open CommonTypes
open System.Resources

type CliArguments =
    | [<AltCommandLine("-c")>]C_lang 
    | [<AltCommandLine("-Ada")>]Ada_Lang
    | [<AltCommandLine("-py")>]Py_Lang
    | [<AltCommandLine("-uPER")>]UPER_enc
    | [<AltCommandLine("-ACN")>]ACN_enc
    | [<AltCommandLine("-atc")>]Auto_test_cases
    | [<AltCommandLine("-o")>]Out of dir:string
    | [<AltCommandLine("-equal")>]Equal_Func 
    | [<AltCommandLine("-typePrefix")>]Type_Prefix of prefix:string
    | [<AltCommandLine("-x")>] Xml_Ast of xmlFilename:string
    | [<AltCommandLine("-renamePolicy")>] Rename_Policy of int

    | [<MainCommand; ExactlyOnce; Last>] Files of files:string list
with
    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | C_lang           -> "generate code for the C/C++ programming language"
            | Ada_Lang         -> "generate code for the Ada/SPARK programming language"
            | Py_Lang          -> "generate code for the Python 3.6 programming language"
            | UPER_enc         -> "generates encoding and decoding functions for unaligned Packed Encoding Rules (uPER)"
            | ACN_enc          -> "generates encoding and decoding functions using the ASSERT ASN.1 encoding Control Notation"
            | Auto_test_cases  -> "create automatic test cases."
            | Out (_)          -> "directory where all files are produced."
            | Files (_)        -> "List of ASN.1 and ACN files to process."
            | Type_Prefix _    -> "adds 'prefix' to all generated C or Ada/SPARK data types."
            | Equal_Func       -> "generate functions for testing type equality."
            | Xml_Ast _        -> "dump internal AST in an xml file"
            | Rename_Policy _  -> "Specify rename policy for enums 0 no rename (Ada default), 1 rename only conflicting enumerants (C default), 2 rename all enumerants of an enum with at lest one conflicting enumerant"



let checkArguement arg =
    match arg with
    | C_lang           -> ()
    | Ada_Lang         -> ()
    | Py_Lang          -> ()
    | UPER_enc         -> ()
    | ACN_enc          -> ()
    | Auto_test_cases  -> ()
    | Equal_Func       -> ()
    | Xml_Ast xmlFileName   -> 
        match xmlFileName.ToLower().EndsWith ".xml" with
        | true  -> ()
        | false -> 
            let msg = sprintf "Invalid output filename '%s'\nGenerated ast xml files must have an .xml extension." xmlFileName
            raise (UserException msg)
    | Out outDir       -> 
        match System.IO.Directory.Exists outDir with
        | true  -> ()
        | false -> raise (UserException (sprintf "directory '%s' does not exist." outDir))
    | Files files      -> 
        files |> Seq.iter(fun f -> match File.Exists f with true -> () | false -> raise (UserException (sprintf "File '%s' does not exist." f)))
    | Type_Prefix _    -> ()
    | Rename_Policy _   -> ()



let constructCommandLineSettings args (parserResults: ParseResults<CliArguments>)=
    let files = parserResults.GetResult <@ Files @>
    {
        CommandLineSettings.asn1Files = files |> List.filter(fun a -> (a.ToLower().EndsWith(".asn1")) || (a.ToLower().EndsWith(".asn")) )
        acnFiles  = files |> List.filter(fun a -> (a.ToLower().EndsWith(".acn")) )
        encodings = 
            args |> 
            List.choose(fun arg ->
                match arg with
                |UPER_enc -> Some CommonTypes.Asn1Encoding.UPER
                |ACN_enc  -> Some CommonTypes.Asn1Encoding.ACN
                | _       -> None )

        GenerateEqualFunctions = parserResults.Contains<@ Equal_Func @> || parserResults.Contains<@ Auto_test_cases @>
        TypePrefix = parserResults.GetResult(<@ Type_Prefix@>, defaultValue = "")
        CheckWithOss = false
        AstXmlAbsFileName = parserResults.GetResult(<@Xml_Ast@>, defaultValue = "")
        IcdUperHtmlFileName = ""
        IcdAcnHtmlFileName = ""
        mappingFunctionsModule = None
        integerSizeInBytes = 8
        renamePolicy = CommonTypes.EnumRenamePolicy.SelectiveEnumerants
    }    


let exportRTL outDir  (l:DAst.ProgrammingLanguage) =
    let writeTextFile fileName (content:String) =
        System.IO.File.WriteAllText(fileName, content.Replace("\r",""))
    let rm = new ResourceManager("Resource1", System.Reflection.Assembly.GetExecutingAssembly());
    match l with
    | DAst.ProgrammingLanguage.C ->
                writeTextFile (Path.Combine(outDir, "asn1crt.c")) (rm.GetString("asn1crt",null)) 
                writeTextFile (Path.Combine(outDir, "asn1crt.h")) (rm.GetString("asn1crt1",null)) 
                writeTextFile (Path.Combine(outDir, "acn.c"))     (rm.GetString("Acn",null)) 
                writeTextFile (Path.Combine(outDir, "real.c"))    (rm.GetString("real",null)) 
    | DAst.ProgrammingLanguage.Ada ->
                writeTextFile (Path.Combine(outDir, "adaasn1rtl.adb")) (rm.GetString("adaasn1rtl_adb",null)) 
                writeTextFile (Path.Combine(outDir, "adaasn1rtl.ads")) (rm.GetString("adaasn1rtl_ads",null)) 
                writeTextFile (Path.Combine(outDir, "IgnoredExaminerWarnings.wrn"))     (rm.GetString("IgnoredExaminerWarnings",null)) 
                writeTextFile (Path.Combine(outDir, "gnat.cfg"))    (rm.GetString("gnat",null)) 
                writeTextFile (Path.Combine(outDir, "runSpark.sh"))    (rm.GetString("run",null)) 
                writeTextFile (Path.Combine(outDir, "GPS_project.gpr"))    (rm.GetString("GPS_project",null)) 
    | DAst.ProgrammingLanguage.Python ->
                writeTextFile (Path.Combine(outDir, "asn1.py")) (rm.GetString("asn1py",null)) 
                if not <| System.IO.Directory.Exists(Path.Combine(outDir, "tests")) then
                        System.IO.Directory.CreateDirectory(Path.Combine(outDir, "tests")) |> ignore
                writeTextFile (Path.Combine(outDir, "tests", "BitStreamTest.py")) (rm.GetString("py_bitstream_test",null)) 



[<EntryPoint>]
let main argv = 

    let parser = ArgumentParser.Create<CliArguments>(programName = "Asn1f4.exe")
    try
        let parserResults = parser.Parse argv
        let cliArgs = parserResults.GetAllResults()
        cliArgs |> Seq.iter checkArguement 
        let args = constructCommandLineSettings cliArgs parserResults
        
        // create front ent ast
        let frontEntAst, acnDeps = FrontEntMain.constructAst args
        
        // print front ent ast as xml 
        match args.AstXmlAbsFileName with
        | ""    -> ()
        | _     -> 
            ExportToXml.exportFile frontEntAst acnDeps args.AstXmlAbsFileName


        // construct backend ast
        let backends = 
            cliArgs |> 
            List.choose (fun a -> 
                match a with
                | C_lang        -> Some (DAstConstruction.DoWork frontEntAst acnDeps CommonTypes.ProgrammingLanguage.C args.encodings)
                | Ada_Lang      -> Some (DAstConstruction.DoWork frontEntAst acnDeps CommonTypes.ProgrammingLanguage.Ada args.encodings)
                | Py_Lang       -> Some (DAstConstruction.DoWork frontEntAst acnDeps CommonTypes.ProgrammingLanguage.Python args.encodings)
                | _             -> None)

        //generate code
        let outDir = parserResults.GetResult(<@Out@>, defaultValue = ".")
        backends |> 
            Seq.iter (fun r -> 
                GenerateFiles.generateAll outDir r args.encodings
                exportRTL outDir r.lang
                match args.AstXmlAbsFileName with
                | ""    -> ()
                | _     -> DAstExportToXml.exportFile r acnDeps ("backend_" + args.AstXmlAbsFileName)
                
                )


        0
    with
        | :? Argu.ArguParseException as ex -> 
            Console.Error.WriteLine(ex.Message)
            1    
        | UserException msg            ->
            Console.Error.WriteLine(msg)
            2
        | :? Antlr.Asn1.asn1Parser.SyntaxErrorException as ex            ->
            Console.Error.WriteLine(ex.Message)
            2
        | SemanticError (loc,msg)            ->
            Console.Error.WriteLine("File:{0}, line:{1}, {2}", Path.GetFileName(loc.srcFilename), loc.srcLine, msg);
            3
        (*
        | ex            ->
            Console.Error.WriteLine(ex.Message)
            Console.Error.WriteLine(ex.StackTrace)
            4
            *)
