module CommonTypes
open FsUtils


let c_keyworkds =  [ "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"; "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; "while"; ]
let ada_keyworkds =  [ "abort"; "else"; "new"; "return"; "abs"; "elsif"; "not"; "reverse"; "abstract"; "end"; "null"; "accept"; "entry"; "select"; "access"; "exception"; "of"; "separate"; "aliased"; "exit"; "or"; "some"; "all"; "others"; "subtype"; "and"; "for"; "out"; "synchronized"; "array"; "function"; "overriding"; "at"; "tagged"; "generic"; "package"; "task"; "begin"; "goto"; "pragma"; "terminate"; "body"; "private"; "then"; "if"; "procedure"; "type"; "case"; "in"; "protected"; "constant"; "interface"; "until"; "is"; "raise"; "use"; "declare"; "range"; "delay"; "limited"; "record"; "when"; "delta"; "loop"; "rem"; "while"; "digits"; "renames"; "with"; "do"; "mod"; "requeue"; "xor" ]

type ProgrammingLanguage =
    |C
    |Ada
    |Spark
    |Html
    |Unknown
    with 
        member l.cmp (s1:string) (s2:string) =
            match l with
            |C          -> s1 = s2
            |Ada
            |Spark      -> s1.icompare s2
            |Html       -> s1 = s2
            |Unknown    -> s1 = s2
        member l.DefinitionsFileExt = 
            match l with
            |C          -> ".h"
            |Ada
            |Spark      -> ".ads"
            |Html       -> ""
            |Unknown    -> ""
        member l.keywords = 
            match l with
            |C          -> c_keyworkds
            |Ada
            |Spark      -> ada_keyworkds
            |Html       -> []
            |Unknown    -> []

type Codec =
    |Encode
    |Decode
 with
    member this.suffix =
        match this with
        | Encode    -> "_Encode"
        | Decode    -> "_Decode"


type Asn1Encoding =
    | UPER
    | ACN
    | BER
    | XER


type CommandLineSettings = {
    asn1Files : string list
    acnFiles  : string list
    encodings: Asn1Encoding list
    GenerateEqualFunctions : bool
    TypePrefix:string
    CheckWithOss:bool
    AstXmlAbsFileName:string
    IcdUperHtmlFileName:string
    IcdAcnHtmlFileName:string
    mappingFunctionsModule : string option
    integerSizeInBytes : int            //currently only the value of 8 bytes (64 bits) is supported
}