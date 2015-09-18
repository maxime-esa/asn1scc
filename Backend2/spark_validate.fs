module spark_validate

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils

type State = spark_init.State



let rec PrintTypeContraint (t:ConstraintType) (path:list<string>) (c:Asn1Constraint) alphaName (tasList:list<(List<string>*(string*string))>) (m:Asn1Module) (r:AstRoot) = 
    let p = GetAccessFld path t r 
    let tasName = 
        match tasList with
        | []    -> 
            match path with
            | []
            | _::[] -> raise(BugErrorException("Invalid path"))
            | md::ts::_ ->
                match md = m.Name.Value with
                | true -> Ast.GetTasCName ts r.TypePrefix
                | false -> (ToC md) + "." + Ast.GetTasCName ts r.TypePrefix
        | _     ->
            match path with
            | []
            | _::[] -> raise(BugErrorException("Invalid path3"))
            | md::ts::[] ->
                match md = m.Name.Value with
                | true -> Ast.GetTasCName ts r.TypePrefix
                | false -> (ToC md) + "." + Ast.GetTasCName ts r.TypePrefix
            | _         ->
                match tasList |> Seq.tryFind(fun (pth, (md,ts)) -> pth = path ) with
                | Some(_,(md,ts)) ->
                    match md = m.Name.Value with
                    | true -> Ast.GetTasCName ts r.TypePrefix
                    | false -> (ToC md) + "." + Ast.GetTasCName ts r.TypePrefix
                | None           -> raise(BugErrorException("Invalid path2"))
        
    match c with
    | SingleValueContraint(v)     -> 
        match t with
        | AlphabetOf(_) -> 
            match (GetValueAstring v r).Length with
            | 1     -> sc.SingleValContraint p (spark_variables.PrintValue v t tasName m r)
            | _     -> sc.stringContainsChar (spark_variables.PrintValue v t tasName m r) p
        | _             -> sc.SingleValContraint p (spark_variables.PrintValue v t tasName m r)
    | RangeContraint(a,b, minIsIn, maxIsIn)         -> sc.RangeContraint p (spark_variables.PrintValue a t tasName m r) (spark_variables.PrintValue b t tasName m r) minIsIn maxIsIn
    | RangeContraint_val_MAX(a, minIsIn)   -> sc.RangeContraint_val_MAX p (spark_variables.PrintValue a t tasName m r) minIsIn
    | RangeContraint_MIN_val(b, maxIsIn)   -> sc.RangeContraint_MIN_val p (spark_variables.PrintValue b t tasName m r) maxIsIn
    | RangeContraint_MIN_MAX      -> raise(BugErrorException "This constraint should have been removed")
    | SizeContraint(inCon)        -> PrintTypeContraint  (LengthOf t.Type) path inCon alphaName tasList m r
    | AlphabetContraint(inCon)    -> sc.callAlphaFunc alphaName p
    | UnionConstraint(c1, c2,_)     -> sc.OR_Constraint (PrintTypeContraint t path c1 alphaName tasList m r) (PrintTypeContraint t path c2 alphaName tasList m r)
    | IntersectionConstraint(c1,c2)-> sc.AND_Constraint (PrintTypeContraint t path c1 alphaName tasList m r) (PrintTypeContraint t path c2 alphaName tasList m r)
    | AllExceptConstraint(c1)      -> sc.AllExceptConstraint (PrintTypeContraint t path c1 alphaName tasList m r)
    | ExceptConstraint(c1,c2)      -> sc.ExceptConstraint (PrintTypeContraint t path c1 alphaName tasList m r) (PrintTypeContraint t path c2 alphaName tasList m r)
    | RootConstraint(c1)           -> (PrintTypeContraint t path c1 alphaName tasList m r)
    | RootConstraint2(c1,c2)       -> sc.OR_Constraint (PrintTypeContraint t path c1 alphaName tasList m r) (PrintTypeContraint t path c2 alphaName tasList m r)
    | TypeInclusionConstraint(modName,tasName) ->
        let actualType = GetActualTypeByNameAllConsIncluded modName tasName r
        let arrCons = actualType.Constraints |> Seq.map(fun c -> PrintTypeContraint t path c alphaName tasList m r)
        sc.PrintMultipleConstraints arrCons
    | WithComponentConstraint(_)    -> raise(BugErrorException "Unexpected Constraint")
    | WithComponentsConstraint(_)   -> raise(BugErrorException "Unexpected Constraint")


let PrintAlphaFunction (t:ConstraintType) (path:list<string>) (cons:list<Asn1Constraint>) (tasList:list<(List<string>*(string*string))>) (m:Asn1Module) alphaName (r:AstRoot) = 
    let arrCons = cons |> List.map(fun c -> PrintTypeContraint t path c alphaName tasList m r)
    match (GetTypeConstraintsErrorCode cons path r) with
    | None  -> raise(BugErrorException "This type does not have constraints, so no ErrorCode exists")
    | Some(errCodeName) ->    sc.Print_AlphabetCheckFunc alphaName arrCons 
    

let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<LOCAL_VARIABLE>) = 
    match t.Kind with
    | SequenceOf(child) when HasValidateFunc child r-> 
        let nCurLevel =  (Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1
        let nAllocatedLevel = state |> Seq.filter(fun lv -> match lv with SEQUENCE_OF_INDEX(_)->true |_ -> false )|>Seq.length
        if nCurLevel>nAllocatedLevel then
            (SEQUENCE_OF_INDEX (nCurLevel,false))::state
        else
            state
    | _             -> state

let CollectLocalVars (t:Asn1Type) (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) =
    let lvs = VisitType t [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []
    let emitLocalVariable  = function
        | SEQUENCE_OF_INDEX(i,bHasInit) -> sc.Emit_local_variable_SQF_Index (BigInteger i) bHasInit
        | _                 -> ""
    lvs |> Seq.map emitLocalVariable


let EmitTypeBodyBase (t:ConstraintType) (path:list<string>)  (tasList:list<(List<string>*(string*string))>) (m:Asn1Module) (r:AstRoot)  =
    let alphaFuncName = ToC ((path |> Seq.skip 1).StrJoin("_").Replace("#","elem"))
    let arrCons = t.Type.Constraints |> Seq.map(fun c -> PrintTypeContraint t path c alphaFuncName tasList m r)
    match (GetTypeConstraintsErrorCode t.Type.Constraints path r) with
    | None  -> raise(BugErrorException "This type does not have constraints, so no ErrorCode exists")
    | Some(errCodeName) ->    sc.Emit_type  arrCons errCodeName        



let rec EmitTypeBody (t:ConstraintType) (path:list<string>)  (tasList:list<(List<string>*(string*string))>) (m:Asn1Module) (r:AstRoot)  =
    let p = GetAccessFld path t r 
    let SizeableTypeUperRange (t:Asn1TypeKind) cons=
            match (GetTypeUperRange t cons r) with
            |Concrete(min, max)        -> min,max
            |_                         -> raise(BugErrorException "SEQUENCE OF or OCTET STRING etc has no constraints")
    match t.Type.Kind with
    |Sequence(children) ->
        let itemsToCheck = 
            seq {
                for c in children |> Seq.filter(fun x-> not(x.AcnInsertedField)) do
                    match c.Optionality with
                    | None                              -> if (HasValidateFunc c.Type r) then yield (0, c)      // 0 = check component
                    | Some(Optional) | Some(Default(_)) -> if (HasValidateFunc c.Type r) then yield (1, c)      // 1 = check optional compoent
                    | Some(AlwaysPresent)               -> yield (2, c)      // 2 = check component is always present
                                                           if (HasValidateFunc c.Type r) then yield (0, c) 
                    | Some(AlwaysAbsent)                -> yield (3, c)      // 3 = check component is always absent
            } |> Seq.toList

        // if the first item to check is an optional item,
        // then we must initialize ret to true
        let itemsToCheck0 = 
                match itemsToCheck with
                | (1,c)::xs -> (-1,c)::itemsToCheck 
                | _         -> itemsToCheck

        let printChild (k:int, c:ChildInfo) sNestedContent = 
            let chKey = (path@[c.Name.Value])
            let errCode = match Ast.GetChildInfoErrorCode c  chKey r with
                          |Some(s)  -> s
                          |None     -> ""
            let sChildBody = EmitTypeBody (Same c.Type) chKey tasList m r
            let sChildName = c.CName ProgrammingLanguage.Spark
            let content, bCanFail = 
                match k with
                | -1    -> sc.Emit_fixedSize_constraint(), false
                | 0     -> sChildBody , true
                | 1     -> sc.Emit_sequence_optional_component p sChildName sChildBody, true
                | 2     -> sc.Emit_sequence_check_component_is_always_present_or_absent p sChildName 1I errCode, true
                | 3     -> sc.Emit_sequence_check_component_is_always_present_or_absent p sChildName 0I errCode, true
                | _     -> raise(BugErrorException "")
            sc.JoinItems content bCanFail sNestedContent

        let rec printChildren  = function
            |[]     -> sc.Emit_fixedSize_constraint()
            |x::xs  -> printChild x  (printChildren xs)

        printChildren itemsToCheck0
    |Choice(children)  -> 
        let printChild (c:ChildInfo) = 
            let chKey = (path@[c.Name.Value])
            let errCode = match Ast.GetChildInfoErrorCode c  chKey r with
                          |Some(s)  -> s
                          |None     -> ""
            let sChildBody =
                match HasValidateFunc c.Type r with
                | true ->  EmitTypeBody (Same c.Type) chKey tasList m r
                | false -> sc.Emit_fixedSize_constraint()
            sc.Emit_choice_child (c.CName ProgrammingLanguage.Spark) sChildBody (c.CName_Present Spark)

        let arrChildren = children |> List.map printChild 
        let sTasName = GetTasCName (path |> Seq.nth 1) r.TypePrefix
        sc.Emit_choice sTasName arrChildren
    |SequenceOf(child) -> 
        let min, max = SizeableTypeUperRange t.Type.Kind t.Type.Constraints
        let sizeCons = match min=max with
                       | false  -> EmitTypeBodyBase  (LengthOf t.Type) path tasList m r
                       | true   -> sc.Emit_fixedSize_constraint()
        match HasValidateFunc child r with
        |false  -> sizeCons
        |true   ->
            let rec breakPath (lst:string list)=
                let rec breakPathAux (ip:string list) (rp:string list)=
                    seq {
                        match rp with
                        | []     -> yield ip
                        | x::xs  -> 
                                    if x = "#" then yield ip;
                                    yield! (breakPathAux (ip@[x]) xs)
                    } |> Seq.toList
                breakPathAux [] lst
            let getIndexNameByPath (path:string list) =
                "I" + ((Seq.length (path |> Seq.filter(fun s -> s ="#"))) + 1).ToString()
            let handleSubPath (pth:string list) =
                let tp = Ast.GetTypeByAbsPath pth r
                let min, max = SizeableTypeUperRange tp.Kind tp.Constraints
                let sI = getIndexNameByPath pth
                sc.Emit_sequence_of_assert sI max
            let sSizeCon = sizeCons
            let sChildBody = EmitTypeBody (Same child) (path@["#"]) tasList m r
            let sI = getIndexNameByPath path
            let arrsAssrtAnts = breakPath path |> Seq.map handleSubPath |> Seq.toList
            
            sc.Emit_sequence_of sI p max sSizeCon sChildBody (min=max) arrsAssrtAnts
    |ReferenceType(modName,tasName, _) -> 
        let tsName = Ast.GetTasCName tasName.Value r.TypePrefix
        match modName.Value = m.Name.Value with
        | true  -> sc.Emit_Reference1 p tsName
        | false -> sc.Emit_Reference2 p (ToC modName.Value) tsName
    |_                  -> EmitTypeBodyBase  t path tasList m r





let CollectAlphaFuncs (tas:TypeAssignment) (tasList:list<(List<string>*(string*string))>) (m:Asn1Module) (r:AstRoot) =
    let OnType_collerLocalVariables (t:Asn1Type) (path:list<string>) (parent:option<Asn1Type>) (ass:Assignment) (m:Asn1Module) (r:AstRoot) (state:list<string>) = 
        let alphaCons = t.Constraints |> List.choose(fun c -> match c with |AlphabetContraint(x) -> Some x |_ -> None )
        let alphaFuncName = ToC ((path |> Seq.skip 1).StrJoin("_").Replace("#","elem"))
        let alphaFuncs = 
            match alphaCons with
            | []    -> []
            | _     -> [PrintAlphaFunction (AlphabetOf t) path alphaCons tasList m alphaFuncName r]
        state@alphaFuncs
    VisitType tas.Type [m.Name.Value; tas.Name.Value] None (TypeAssignment tas)  m r {DefaultVisitors with visitType=OnType_collerLocalVariables} []

let EmitTypeAss (tas:TypeAssignment) (m:Asn1Module) (r:AstRoot) (state:State) = 
    let sTasName = tas.GetCName r.TypePrefix
    let t, tasList = RemoveWithComponents_priv tas.Type r [m.Name.Value; tas.Name.Value] []
    let localVars = CollectLocalVars t tas m r
    //let (sTypeBody, arrsAlphaCheckFunctions),_ = EmitTypeBody false (Same t) [m.Name.Value; tas.Name.Value] m r
    let sTypeBody = EmitTypeBody (Same t) [m.Name.Value; tas.Name.Value] tasList m r
    let arrsAlphaCheckFunctions = CollectAlphaFuncs tas tasList m r
    let sDebug0 = (PrintAsn1.PrintType tas.Type m).Split('\n') |> Seq.map(fun s -> "-- " + s) |> Seq.StrJoin "\n"
    let sDebug = (PrintAsn1.PrintType t m).Split('\n') |> Seq.map(fun s -> "-- " + s) |> Seq.StrJoin "\n"
    let result = sc.EmitTypeAssignment sTasName sTypeBody arrsAlphaCheckFunctions localVars (sDebug0+"-------\n"+sDebug)
    result, state   

