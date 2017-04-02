module BackendAstConstruct

open Constraints

let DoWork (lang:Ast.ProgrammingLanguage) (app:Ast.AstRoot) (acn:AcnTypes.AcnAst) outdir =
    let l =
        match lang with
        | Ast.ProgrammingLanguage.C     -> C
        | Ast.ProgrammingLanguage.Ada   
        | Ast.ProgrammingLanguage.Spark -> Ada
        | _                             -> raise(System.Exception "Unsupported programming language")
    
    let bast = BAstConstruction.createValidationAst lang app acn

    let bastWithAcnInsertedFields = BastAddAcnInsertFields.doWork bast acn

    let cast = CAstConstruction.mapBAstToCast bastWithAcnInsertedFields acn

    let dast = DAstConstruction.DoWork cast l

    GenerateFiles.printDAst dast l outdir
