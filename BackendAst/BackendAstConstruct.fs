module BackendAstConstruct

let DoWork (lang:Ast.ProgrammingLanguage) (app:Ast.AstRoot) (acn:AcnTypes.AcnAst) outdir =
    
    let bast = BAstConstruction.createValidationAst lang app acn

    let bastWithAcnInsertedFields = BastAddAcnInsertFields.doWork bast acn

    let cast = CAstConstruction.mapBAstToCast bastWithAcnInsertedFields acn

    let dast = DAstConstruction.DoWork cast DAst.ProgrammingLanguage.C 
        
    DAstConstruction.printDAst dast DAst.ProgrammingLanguage.C outdir
