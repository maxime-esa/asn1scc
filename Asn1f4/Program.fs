open Argu
open FsUtils
open System
open System.IO
open CommonTypes

type CliArguments =
    | [<AltCommandLine("-c")>]C_lang 
    | [<AltCommandLine("-Ada")>]Ada_Lang
    | [<AltCommandLine("-uPER")>]UPER_enc
    | [<AltCommandLine("-ACN")>]ACN_enc
    | [<AltCommandLine("-atc")>]Auto_test_cases
    | [<AltCommandLine("-o")>]Out of dir:string
    | [<AltCommandLine("-equal")>]Equal_Func 
    | [<AltCommandLine("-typePrefix")>]Type_Prefix of prefix:string
    | [<MainCommand; ExactlyOnce; Last>] Files of files:string list
with
    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | C_lang           -> "generate code for the C/C++ programming language"
            | Ada_Lang         -> "generate code for the Ada/SPARK programming language"
            | UPER_enc         -> "generates encoding and decoding functions for unaligned Packed Encoding Rules (uPER)"
            | ACN_enc          -> "generates encoding and decoding functions using the ASSERT ASN.1 encoding Control Notation"
            | Auto_test_cases  -> "create automatic test cases."
            | Out (_)          -> "directory where all files are produced."
            | Files (_)        -> "List of ASN.1 and ACN files to process."
            | Type_Prefix _    -> "adds 'prefix' to all generated C or Ada/SPARK data types."
            | Equal_Func       -> "generate functions for testing type equality."



let checkArguement arg =
    match arg with
    | C_lang           -> ()
    | Ada_Lang         -> ()
    | UPER_enc         -> ()
    | ACN_enc          -> ()
    | Auto_test_cases  -> ()
    | Equal_Func       -> ()
    | Out outDir       -> 
        match System.IO.Directory.Exists outDir with
        | true  -> ()
        | false -> raise (UserException (sprintf "directory '%s' does not exist." outDir))
    | Files files      -> 
        files |> Seq.iter(fun f -> match File.Exists f with true -> () | false -> raise (UserException (sprintf "File '%s' does not exist." f)))
    | Type_Prefix _    -> ()



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
        AstXmlAbsFileName = ""
        IcdUperHtmlFileName = ""
        IcdAcnHtmlFileName = ""
        mappingFunctionsModule = None
        integerSizeInBytes = 8
    }    

[<EntryPoint>]
let main argv = 

    let parser = ArgumentParser.Create<CliArguments>(programName = "Asn1f4.exe")
    try
        let parserResults = parser.Parse argv
        let cliArgs = parserResults.GetAllResults()
        cliArgs |> Seq.iter checkArguement 
        let args = constructCommandLineSettings cliArgs parserResults
        let frontEntAst = FrontEntMain.constructAst args
        0
    with
        | :? Argu.ArguParseException as ex -> 
            Console.Error.WriteLine(ex.Message)
            1    
        | UserException msg            ->
            Console.Error.WriteLine(msg)
            2
        | SemanticError (loc,msg)            ->
            Console.Error.WriteLine(msg)
            Console.Error.WriteLine("File:{0}, line:{1}, {2}", Path.GetFileName(loc.srcFilename), loc.srcLine, msg);
            3
        | ex            ->
            Console.Error.WriteLine(ex.Message)
            Console.Error.WriteLine(ex.StackTrace)
            4


    
