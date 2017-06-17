module BackendAstConstruct



let DoWork (lang:CommonTypes.ProgrammingLanguage) (r:Asn1AcnAst.AstRoot) =
    let l =
        match lang with
        | CommonTypes.ProgrammingLanguage.C     -> DAst.ProgrammingLanguage.C
        | CommonTypes.ProgrammingLanguage.Ada   
        | CommonTypes.ProgrammingLanguage.Spark -> DAst.ProgrammingLanguage.Ada
        | _                             -> raise(System.Exception "Unsupported programming language")
    
    DAstConstruction.DoWork r l 


