module BackendAstConstruct

let DoWork (lang:Ast.ProgrammingLanguage) (app:Ast.AstRoot) (acn:AcnTypes.AcnAst) =
    
    let bast = BAstConstruction.createValidationAst lang app acn

    let bastWithAcnInsertedFields = BastAddAcnInsertFields.doWork bast acn

    let cast = CAstConstruction.mapBAstToCast bastWithAcnInsertedFields acn
        
    cast
