module DAstValidate

open System
open System.Numerics
open System.Globalization
open System.IO

open FsUtils
open Constraints
open DAst

let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) =
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_IsConstraintValid"))

let Lte (l:ProgrammingLanguage) eqIsInc  e1 e2 =
    match eqIsInc with
    | true   -> l.ExpLte e1 e2        
    | false  -> l.ExpLt  e1 e2

let foldGenericCon (l:ProgrammingLanguage) valToStrFunc  (p:String)  (c:GenericConstraint<'v>)  =
    foldGenericConstraint
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpEqual p (valToStrFunc v) ,s)
        c
        0 |> fst

let foldRangeCon (l:ProgrammingLanguage) valToStrFunc1 valToStrFunc2 (p:String)  (c:RangeTypeConstraint<'v1,'v2>)  =
    foldRangeTypeConstraint        
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpEqual p (valToStrFunc2 v) ,s)
        (fun v1 v2  minIsIn maxIsIn s   -> 
            l.ExpAnd (Lte l minIsIn (valToStrFunc1 v1) p) (Lte l maxIsIn p (valToStrFunc1 v2)), s)
        (fun v1 minIsIn s   -> Lte l minIsIn (valToStrFunc1 v1) p, s)
        (fun v2 maxIsIn s   -> Lte l maxIsIn p (valToStrFunc1 v2), s)
        c
        0 |> fst



let foldSizeRangeTypeConstraint (l:ProgrammingLanguage)  getSizeFunc (p:String) (c:PosIntTypeConstraint) = 
    foldRangeTypeConstraint        
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpEqual (getSizeFunc l p) (v.ToString()) ,s)
        (fun v1 v2  minIsIn maxIsIn s   -> 
            l.ExpAnd (Lte l minIsIn (v1.ToString()) (getSizeFunc l p)) (Lte l maxIsIn (getSizeFunc l p) (v2.ToString())), s)
        (fun v1 minIsIn s   -> Lte l minIsIn (v1.ToString()) (getSizeFunc l p), s)
        (fun v2 maxIsIn s   -> Lte l maxIsIn (getSizeFunc l p) (v2.ToString()), s)
        c
        0 


let foldSizableConstraint (l:ProgrammingLanguage) valToStrFunc  getSizeFunc (p:String) (c:SizableTypeConstraint<'v>) =
    foldSizableTypeConstraint2
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpStringEqual p (valToStrFunc v) ,s)
        (fun intCon s       -> foldSizeRangeTypeConstraint l getSizeFunc p intCon)
        c
        0 |> fst

let foldStringCon (l:ProgrammingLanguage) alphaFuncName (p:String)  (c:IA5StringConstraint)  =
    foldStringTypeConstraint2
        (fun e1 e2 b s      -> l.ExpOr e1 e2, s)
        (fun e1 e2 s        -> l.ExpAnd e1 e2, s)
        (fun e s            -> l.ExpNot e, s)
        (fun e1 e2 s        -> l.ExpAnd e1 (l.ExpNot e2), s)
        (fun e s            -> e, s)
        (fun e1 e2 s        -> l.ExpOr e1 e2, s)
        (fun v rv s         -> l.ExpStringEqual p v.IDQ ,s)
        (fun intCon s       -> foldSizeRangeTypeConstraint l (fun l p -> l.StrLen p) p intCon)
        (fun alphcon s      -> sprintf "%s(%s)" alphaFuncName p,s) 
        c
        0 |> fst

let createPrimitiveFunction (r:CAst.AstRoot) (l:ProgrammingLanguage)  tasInfo (typeId:ReferenceToType) allCons  conToStrFunc (typeDefinition:TypeDefinitionCommon) (alphaFuncs : AlphaFunc list) (us:State)  =
    match allCons with
    | []            -> None, us
    | _             ->
        let funcName            = getFuncName r l tasInfo
        let errCode             = ToC ("ERR_" + ((typeId.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")))
        let errCodeValue        = us.currErrCode

        let funcBody (p:String) = 
            let allCons = allCons |> List.map (conToStrFunc p)
            l.ExpAndMulti allCons, []

        let  func  = 
                match funcName  with
                | None              -> None
                | Some funcName     -> 
                    let p = "val"
                    let (exp, _) = funcBody p  
                    match l with
                    |C     -> Some(isvalid_c.EmitTypeAssignment_primitive funcName  typeDefinition.name exp errCode (alphaFuncs |> List.map(fun x -> x.funcBody)) )
                    |Ada   -> Some(isvalid_a.EmitTypeAssignment_primitive funcName  typeDefinition.name exp errCode (alphaFuncs |> List.map(fun x -> x.funcBody)) )
        let  funcDef  = 
                match funcName with
                | None              -> None
                | Some funcName     -> 
                    match l with
                    |C     ->  Some(isvalid_c.EmitTypeAssignment_primitive_def funcName  typeDefinition.name errCode (BigInteger errCodeValue))
                    |Ada   ->  Some(isvalid_a.EmitTypeAssignment_primitive_def funcName  typeDefinition.name errCode (BigInteger errCodeValue))
        
        let ret = 
            {
                IsValidFunction.funcName    = funcName
                errCode                     = errCode
                errCodeValue                = us.currErrCode
                func                        = func
                funcDef                     = funcDef
                funcBody                    = (fun p  -> [funcBody p ])
                alphaFuncs                  = alphaFuncs
            }    
        Some ret, {us with currErrCode = us.currErrCode + 1}



let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldRangeCon l (fun v -> v.ToString()) (fun v -> v.ToString())) typeDefinition [] us

let createRealFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Real) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldRangeCon l (fun v -> v.ToString("E20", NumberFormatInfo.InvariantInfo)) (fun v -> v.ToString("E20", NumberFormatInfo.InvariantInfo))) typeDefinition [] us

let createStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.StringType) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let alphafuncName = ToC (((o.id.AcnAbsPath |> Seq.skip 1 |> Seq.StrJoin("-")).Replace("#","elm")) + "_CharsAreValid")
    let foldAlpha = (foldRangeCon l (fun v -> v.ToString().ISQ) (fun v -> v.ToString().ISQ))
    let alpaCons = o.AllCons |> List.choose(fun x -> match x with AlphabetContraint al-> Some al | _ -> None) |> List.map (foldAlpha (sprintf "str%s" (l.ArrayAccess "i")))
    let alphaFuncs = 
        match alpaCons with
        | []    -> []
        | _     ->
            let funcBody =
                match l with
                | C    -> isvalid_c.Print_AlphabetCheckFunc alphafuncName alpaCons
                | Ada  -> isvalid_a.Print_AlphabetCheckFunc alphafuncName alpaCons
            let alphFunc = {AlphaFunc.funcName = alphafuncName; funcBody = funcBody }
            [alphFunc]
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldStringCon l alphafuncName) typeDefinition alphaFuncs us

let createBoolFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Boolean) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldGenericCon l  (fun v -> v.ToString().ToLower())) typeDefinition [] us

let createEnumeratedFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Enumerated) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let printNamedItem (v:string) =
        let itm = o.items |> Seq.find (fun x -> x.name = v)
        itm.getBackendName l
    createPrimitiveFunction r l o.tasInfo o.id o.AllCons (foldGenericCon l  printNamedItem) typeDefinition [] us

let createOctetStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.OctetString) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let allCons = 
        match o.minSize = o.maxSize with
        | false -> o.AllCons
        | true  -> o.AllCons |> List.filter(fun x -> match x with SizeContraint al-> false | _ -> true)
    createPrimitiveFunction r l o.tasInfo o.id allCons (foldSizableConstraint l (fun v -> v.ToString()) (fun l p -> l.Length p ".")) typeDefinition [] us

let createBitStringFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.BitString) (typeDefinition:TypeDefinitionCommon) (us:State)  =
    let allCons = 
        match o.minSize = o.maxSize with
        | false -> o.AllCons
        | true  -> o.AllCons |> List.filter(fun x -> match x with SizeContraint al-> false | _ -> true)
    createPrimitiveFunction r l o.tasInfo o.id allCons (foldSizableConstraint l (fun v -> v.ToString()) (fun l p -> l.Length p ".")) typeDefinition [] us
