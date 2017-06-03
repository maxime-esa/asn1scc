module BackendAstConstruct

open Constraints

let DoWork (lang:CommonTypes.ProgrammingLanguage) (app:Ast.AstRoot) (acn:AcnTypes.AcnAst) outdir =
    let l =
        match lang with
        | CommonTypes.ProgrammingLanguage.C     -> C
        | CommonTypes.ProgrammingLanguage.Ada   
        | CommonTypes.ProgrammingLanguage.Spark -> Ada
        | _                             -> raise(System.Exception "Unsupported programming language")
    
    let bast = BAstConstruction.createValidationAst l app 

    let bastWithAcnInsertedFields = BastAddAcnInsertFields.doWork bast acn

    let cast = CAstConstruction.mapBAstToCast bastWithAcnInsertedFields acn

    let dast = DAstConstruction.DoWork cast l

    GenerateFiles.printDAst dast l outdir
