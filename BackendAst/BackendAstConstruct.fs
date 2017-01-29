module BackendAstConstruct

let DoWork (lang:Ast.ProgrammingLanguage) (app:Ast.AstRoot) (acn:AcnTypes.AcnAst) outdir =
    let l =
        match lang with
        | Ast.ProgrammingLanguage.C     -> DAst.C
        | Ast.ProgrammingLanguage.Ada   
        | Ast.ProgrammingLanguage.Spark -> DAst.Ada
        | _                             -> raise(System.Exception "Unsupported programming language")
    
    let bast = BAstConstruction.createValidationAst lang app acn

    let bastWithAcnInsertedFields = BastAddAcnInsertFields.doWork bast acn

    let cast = CAstConstruction.mapBAstToCast bastWithAcnInsertedFields acn

    let dast = DAstConstruction.DoWork cast l

    GenerateFiles.printDAst dast l outdir
