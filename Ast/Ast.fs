(*
* Copyright (c) 2008-2012 Semantix and (c) 2012-2015 Neuropublic
*
* This file is part of the ASN1SCC tool.
*
* Licensed under the terms of GNU General Public Licence as published by
* the Free Software Foundation.
*
*  For more informations see License.txt file
*)

module Ast
open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils

type AstRoot = {
    Files: list<Asn1File>
    Encodings:list<Asn1Encoding>
    GenerateEqualFunctions:bool
    TypePrefix:string
    AstXmlAbsFileName:string
    IcdUperHtmlFileName:string
    IcdAcnHtmlFileName:string
    CheckWithOss:bool
    mappingFunctionsModule : string option
}


and Asn1File = {
    FileName:string;
    Tokens: IToken array
    Modules : list<Asn1Module>
}

and Asn1Module = {
    Name : StringLoc
    TypeAssignments : list<TypeAssignment>
    ValueAssignments : list<ValueAssignment>
    Imports : list<ImportedModule>
    Exports : Exports
    Comments : string array
}

and Exports =
    | All
    | OnlySome of list<string>

and  ImportedModule = {
    Name:StringLoc
    Types:list<StringLoc>
    Values:list<StringLoc>
}

and TypeAssignment = {
    Name:StringLoc
    c_name:string
    ada_name:string
    Type:Asn1Type
    Comments: string array
}

and ValueAssignment = {
    Name:StringLoc
    c_name:string
    ada_name:string
    Type:Asn1Type
    Value:Asn1Value
    Scope : ValueScope
}

and ValueScope =
    | GlobalScope
    | TypeScope  of StringLoc*StringLoc     

and Asn1Type = {
    Kind:Asn1TypeKind;
    Constraints:list<Asn1Constraint>;
    AcnProperties : list<AcnTypes.AcnProperty>      //does not contain the properties with long fields 
    Location: SrcLoc   //Line no, Char pos
}

and Asn1TypeKind =
    | Integer
    | Real
    | IA5String
    | NumericString
    | OctetString 
    | NullType
    | BitString
    | Boolean 
    | Enumerated        of list<NamedItem>
    | SequenceOf        of Asn1Type
    | Sequence          of list<ChildInfo>
    | Choice            of list<ChildInfo>
    | ReferenceType     of StringLoc*StringLoc*bool  // Module, tas, flag indicating if type is tablularized (=true) or not

and NamedItem = {
    Name:StringLoc
    c_name:string
    ada_name:string
    _value:Asn1Value option
    Comments: string array
}

and ChildInfo = {
        Name:StringLoc;
        c_name:string
        ada_name:string                     
        present_when_name:string // used only by choices. Does not contain the "_PRESENT". Not to be used directly by backends.
        Type:Asn1Type;
        Optionality:Asn1Optionality option
        AcnInsertedField:bool
        Comments: string array
    }


and Asn1Optionality = 
    | AlwaysAbsent
    | AlwaysPresent
    | Optional  
    | Default   of Asn1Value


and Asn1Value = {
    Kind:Asn1ValueKind
    Location: SrcLoc
}


and Asn1ValueKind =
    |   IntegerValue        of IntLoc
    |   RealValue           of DoubleLoc
    |   StringValue         of StringLoc
    |   BooleanValue        of BoolLoc
    |   BitStringValue      of StringLoc
    |   OctetStringValue    of list<ByteLoc>
    |   RefValue            of StringLoc*StringLoc
    |   SeqOfValue          of list<Asn1Value>
    |   SeqValue            of list<StringLoc*Asn1Value>
    |   ChValue             of StringLoc*Asn1Value
    |   NullValue


and Asn1Constraint = 
    | SingleValueContraint              of Asn1Value             
    | RangeContraint                    of Asn1Value*Asn1Value*bool*bool    //min, max, InclusiveMin(=true), InclusiveMax(=true)
    | RangeContraint_val_MAX            of Asn1Value*bool         //min, InclusiveMin(=true)
    | RangeContraint_MIN_val            of Asn1Value*bool         //max, InclusiveMax(=true)
    | RangeContraint_MIN_MAX            
    | TypeInclusionConstraint           of StringLoc*StringLoc     
    | SizeContraint                     of Asn1Constraint               
    | AlphabetContraint                 of Asn1Constraint           
    | UnionConstraint                   of Asn1Constraint*Asn1Constraint*bool //left,righ, virtual constraint
    | IntersectionConstraint            of Asn1Constraint*Asn1Constraint
    | AllExceptConstraint               of Asn1Constraint
    | ExceptConstraint                  of Asn1Constraint*Asn1Constraint
    | RootConstraint                    of Asn1Constraint
    | RootConstraint2                   of Asn1Constraint*Asn1Constraint
    | WithComponentConstraint           of Asn1Constraint
    | WithComponentsConstraint          of list<NamedConstraint>

and NamedConstraint = {
    Name:StringLoc;
    Contraint:Asn1Constraint option
    Mark:NamedConstraintMark
}

and NamedConstraintMark =
    | NoMark
    | MarkPresent
    | MarkAbsent
    | MarkOptional

and Asn1Encoding =
    | UPER
    | ACN
    | BER
    | XER


type uperRange<'a> =
    | Concrete      of 'a*'a    //[a, b]
    | NegInf        of 'a               //(-inf, b]
    | PosInf        of 'a               //[a, +inf)
    | Empty
    | Full                                      // (-inf, +inf)

type Asn1Size<'a> =
    | Bounded of   'a
    | Infinite

type Codec =
    |Encode
    |Decode

type INTTYPE =
    | UINT      // declared as unsigned integer
    | SINT      // declared as signed integer

let getIntType (uperRange:uperRange<BigInteger>) =
    match uperRange with
    | Concrete(a,b) when a >= 0I    -> UINT
    | Concrete(a,b)                 -> SINT
    | NegInf(b)                     -> SINT
    | PosInf(a)  when a >= 0I       -> UINT
    | PosInf(a)                     -> SINT
    | Empty | Full                  -> SINT


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
        member l.keywords = 
            match l with
            |C          -> c_keyworkds
            |Ada
            |Spark      -> ada_keyworkds
            |Html       -> []
            |Unknown    -> []
        

type AstRoot with
    member r.Modules = seq { for f in r.Files do yield! f.Modules} |> Seq.toList
    member r.Modules2 = [ for f in r.Files do yield! f.Modules ]
    member r.GetModuleByName(name:StringLoc)  = 
        let (n,loc) = name.AsTupple
        match r.Modules |> Seq.tryFind( fun m -> m.Name = name)  with
        | Some(m) -> m
        | None    -> raise(SemanticError(loc, sprintf "No Module Defined with name: %s" n ))

type Asn1File with
    member f.FileNameWithoutExtension = System.IO.Path.GetFileNameWithoutExtension f.FileName
    member f.TypeAssignments =
        f.Modules |> List.collect(fun m -> m.TypeAssignments)
    member f.ValueAssignments =
        f.Modules |> List.collect(fun m -> m.ValueAssignments)
    member f.Imports =
        let allImports = f.Modules |> List.collect(fun m -> m.Imports) |> Seq.distinctBy(fun m -> m.Name.Value) |> Seq.toList
        let modNames = f.Modules |> List.map(fun x -> x.Name.Value)
        allImports |> List.filter(fun x -> not (List.exists (fun y -> y=x.Name.Value) modNames))


type Asn1Module with
    member m.CName = ToC2 m.Name.Value
    member this.ExportedTypes =
        match this.Exports with
        | All   -> 
            let importedTypes = this.Imports |> List.collect(fun imp -> imp.Types) |> List.map(fun x -> x.Value)
            (this.TypeAssignments |> List.map(fun x -> x.Name.Value))@importedTypes
        | OnlySome(typesAndVars)    ->
            typesAndVars |> List.filter(fun x -> System.Char.IsUpper (x.Chars 0))
    member this.ExportedVars =
        match this.Exports with
        | All   -> this.ValueAssignments |> List.map(fun x -> x.Name.Value)
        | OnlySome(typesAndVars)    ->
            typesAndVars |> List.filter(fun x -> not (System.Char.IsUpper (x.Chars 0)))
    member m.TryGetTypeAssignmentByName name (r:AstRoot) =
        match m.TypeAssignments|> Seq.tryFind(fun x -> x.Name = name) with
        | Some t   -> Some t
        | None      -> 
            let othMods = m.Imports |> Seq.filter(fun imp -> imp.Types |> Seq.exists((=) name)) 
                                |> Seq.map(fun imp -> imp.Name) |> Seq.toList
            match othMods with
            | firstMod::_   -> 
                match r.Modules |> Seq.tryFind( fun m -> m.Name = firstMod)  with
                | Some(m) -> m.TryGetTypeAssignmentByName name r
                | None    -> None
            | []            -> None

    member m.GetTypeAssignmentByName name (r:AstRoot) =
        match m.TypeAssignments|> Seq.tryFind(fun x -> x.Name = name) with
        | Some(t)   -> t
        | None      -> 
            let othMods = m.Imports |> Seq.filter(fun imp -> imp.Types |> Seq.exists((=) name)) 
                                |> Seq.map(fun imp -> imp.Name) |> Seq.toList
            match othMods with
            | firstMod::tail   -> r.GetModuleByName(firstMod).GetTypeAssignmentByName name r
            | []               ->            
                let (n,loc) = name.AsTupple
                raise(SemanticError(loc, sprintf "No Type Assignment with name: %s is defined in Module %s" n m.Name.Value))
    member m.GetValueAsigByName(name:StringLoc) (r:AstRoot) =
        let (n,loc) = name.AsTupple
        let value = m.ValueAssignments |> Seq.tryFind(fun x -> x.Name = name) 
        match value with
        | Some(v)       -> v
        | None          ->
            let othMods = m.Imports 
                          |> Seq.filter(fun imp -> imp.Values |> Seq.exists(fun vname -> vname = name)) 
                          |> Seq.map(fun imp -> imp.Name) |> Seq.toList
            match othMods with
            | firstMod::tail   -> r.GetModuleByName(firstMod).GetValueAsigByName name r
            | []               -> raise (SemanticError(loc, sprintf "No value assignment with name '%s' exists" n))


let GetTasCName name typePrefix = ToC2(typePrefix + name)

type TypeAssignment with
    member tas.GetCName typePrefix = GetTasCName tas.Name.Value typePrefix 



type ChildInfo with
    member c.CName (lang:ProgrammingLanguage) = 
        match lang with
        | Ada   | Spark     -> c.ada_name
        | C                 -> c.c_name
        | Html              -> raise(BugErrorException "invalid language")
        | Unknown           -> raise(BugErrorException "invalid language")

    member c.CName_Present  (lang:ProgrammingLanguage) = c.present_when_name + "_PRESENT"
    member c.AlwaysPresent = 
        match c.Optionality with
        | Some(AlwaysPresent)   -> true
        | _                     -> false
    member c.AlwaysAbsent = 
        match c.Optionality with
        | Some(AlwaysAbsent)   -> true
        | _                    -> false

type NamedItem with
    member c.CEnumName (r:AstRoot) (lang:ProgrammingLanguage) = 
        match lang with
        |Ada
        |Spark  -> ToC2 (r.TypePrefix + c.ada_name)
        |C      -> ToC2 (r.TypePrefix + c.c_name)
        | _     -> raise(BugErrorException "invalid language")
    member c.EnumName (lang:ProgrammingLanguage) = 
        match lang with
        |Ada
        |Spark  -> c.ada_name
        |C      -> c.c_name
        | _     -> raise(BugErrorException "invalid language")
        

let GetLongNameByKey_Asn1 (key:seq<string>) = (key |> Seq.skip 1).StrJoin("-").Replace("#","elm")
let GetLongNameByKey_C (key:seq<string>) = ToC (GetLongNameByKey_Asn1 key)


let rec TryGetActualType (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType(mn,tasname, _) ->
        match  r.Modules |> Seq.tryFind(fun m -> m.Name = mn) with
        | Some newmod ->
            match newmod.TryGetTypeAssignmentByName tasname r with
            | Some tas  -> TryGetActualType tas.Type r
            | None      -> None
        | None              -> None
    | _                         -> Some t

let rec GetActualType (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType(mn,tasname,_) ->
        let newmod = r.GetModuleByName(mn)
        let tas = newmod.GetTypeAssignmentByName tasname r
        GetActualType tas.Type r
    | _                         -> t


let GetBaseType (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType(mn,tasname, _) ->
        let newmod = r.GetModuleByName(mn)
        let tas = newmod.GetTypeAssignmentByName tasname r
        tas.Type
    | _                         -> t


let TryGetTypeByAbsPath (path:List<string>) (r:AstRoot) =
    let rec GetLongChildByName (parent:Asn1Type) (relPath:List<string>) =
        match relPath with
        | []    -> Some parent
        | xd::xs ->
            match parent.Kind with
            | Sequence(children) | Choice(children)   ->
                match  children |> Seq.tryFind(fun x -> x.Name.Value = xd) with
                | Some(child)   -> GetLongChildByName child.Type xs
                | _             -> None
            | ReferenceType(md, ts, _)  ->
                match r.Modules |> Seq.tryFind(fun m -> m.Name.Value = md.Value) with
                | Some m    ->
                    match TryGetActualType parent r with
                    | Some actType  -> GetLongChildByName actType relPath
                    | _             -> None
                | _         -> None
            | SequenceOf(child) when xd = "#"   -> GetLongChildByName child xs
            | _                -> None
    match path with
    | mdName::tasName::rstPath  ->
        match r.Modules |> Seq.tryFind(fun x -> x.Name.Value = mdName) with
        | Some(md)  ->
            match  md.TypeAssignments |> Seq.tryFind(fun x -> x.Name.Value = tasName) with
            | Some( tas)        -> GetLongChildByName tas.Type rstPath
            | _                 -> None
        | _         -> None
    | _     -> None

let GetTypeByAbsPathEx (path:List<string>) (r:AstRoot) exToThrow=
    let rec GetLongChildByName (parent:Asn1Type) (relPath:List<string>) =
        match relPath with
        | []    -> parent
        | xd::xs ->
            match parent.Kind with
            | Sequence(children) | Choice(children)   ->
                let child = children |> Seq.find(fun x -> x.Name.Value = xd)
                GetLongChildByName child.Type xs
            | ReferenceType(_)  ->
                let actType = GetActualType parent r
                GetLongChildByName actType relPath
            | SequenceOf(child) when xd = "#"   -> GetLongChildByName child xs
            | _                -> raise(exToThrow)
    match path with
    | mdName::tasName::rstPath  ->
        let md = r.Modules |> Seq.find(fun x -> x.Name.Value = mdName)
        let tas = md.TypeAssignments |> Seq.find(fun x -> x.Name.Value = tasName)
        GetLongChildByName tas.Type rstPath
    | _     -> raise(exToThrow)



let GetTypeByAbsPath (path:List<string>) (r:AstRoot) =
    GetTypeByAbsPathEx path r (BugErrorException "Invalid Path")


let AcnAsn1Type2Asn1Type (t:AcnTypes.AcnAsn1Type) :  Asn1Type =
    match t with
    | AcnTypes.Integer                   -> {Asn1Type.Kind = Integer; Constraints = []; AcnProperties=[]; Location= emptyLocation}
    | AcnTypes.Boolean                   -> {Asn1Type.Kind = Boolean; Constraints = []; AcnProperties=[]; Location= emptyLocation}
    | AcnTypes.NullType                  -> {Asn1Type.Kind = NullType; Constraints = []; AcnProperties=[]; Location= emptyLocation}
    | AcnTypes.RefTypeCon(mdName, tsName)->
        {Asn1Type.Kind = ReferenceType(mdName, tsName, false); Constraints = []; AcnProperties=[]; Location= emptyLocation}


let GetTypeByPoint (p:AcnTypes.Point) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    match p with
    | AcnTypes.TypePoint(absPath)   ->      GetTypeByAbsPath absPath r
    | AcnTypes.ParamPoint(absPath)  ->
        let modName, tasName, prmName = match p.AbsPath with
                                        | x1::x2::x3::[]   -> x1,x2,x3
                                        | _              -> raise(BugErrorException("Invalid Path"))
        let prm = acn.Parameters |> Seq.find(fun x -> x.ModName = modName && x.TasName=tasName && x.Name = prmName)
        AcnAsn1Type2Asn1Type prm.Asn1Type
    | AcnTypes.TempPoint(absPath)  ->
        let modName, tasName, prmName = match p.AbsPath with
                                        | x1::x2::x3::[]   -> x1,x2,x3
                                        | _              -> raise(BugErrorException("Invalid Path"))
        let prm = acn.TmpTypes |> Seq.find(fun x -> x.ModName = modName && x.TasName=tasName && x.Name = prmName)
        AcnAsn1Type2Asn1Type prm.Asn1Type

let GetBaseTypeByName modName tasName (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let tas = mdl.GetTypeAssignmentByName tasName r
    tas.Type


let GetActualTypeByName modName tasName (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let tas = mdl.GetTypeAssignmentByName tasName r
    GetActualType tas.Type r

let GetActualTypeByNameLoc modName (tasName:string) location (r:AstRoot) =
    GetActualTypeByName (loc modName) (tasName.WithLoc location) r

let GetBaseTypeConsIncluded (t:Asn1Type) (r:AstRoot) =
    match t.Kind with
    | ReferenceType(mn,tasname, _) ->
        let newmod = r.GetModuleByName(mn)
        let tas = newmod.GetTypeAssignmentByName tasname r
        let baseType = tas.Type
        {baseType with Constraints = baseType.Constraints@t.Constraints}
    | _                         -> t

let GetActualTypeAllConsIncluded t (r:AstRoot) =
    let rec GetActualTypeAux (t:Asn1Type) (addionalConstraints:list<Asn1Constraint>)  (additionalProps:list<AcnTypes.AcnProperty>) =
        match t.Kind with
        | ReferenceType(mn,tasname, _) ->
            let newmod = r.GetModuleByName(mn)
            let tas = newmod.GetTypeAssignmentByName tasname r
            GetActualTypeAux tas.Type (t.Constraints@addionalConstraints) (t.AcnProperties@additionalProps)
        | _                         -> {t with Constraints = (t.Constraints@addionalConstraints); AcnProperties=t.AcnProperties@additionalProps}
    GetActualTypeAux t [] []

let GetActualTypeByNameAllConsIncluded modName tasName (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let tas = mdl.GetTypeAssignmentByName tasName r
    GetActualTypeAllConsIncluded tas.Type r
    

    

let GetBaseValue  modName vasName  (r:AstRoot) =
    let mdl = r.GetModuleByName(modName)
    let vas = mdl.GetValueAsigByName vasName r
    vas.Value

let rec GetActualValue modName vasName  (r:AstRoot) =
    let baseVal = GetBaseValue  modName vasName  r
    match baseVal.Kind with
    |RefValue(newModName, newVasName)   -> GetActualValue newModName newVasName r
    | _                                 -> baseVal

let rec GetActualValue2 (v:Asn1Value) (r:AstRoot) =
    match v.Kind with
    |RefValue(newModName, newVasName)   -> GetActualValue newModName newVasName r
    | _                                 -> v


let rec GetValueAstring (v:Asn1Value)  (r:AstRoot) =
    match v.Kind with
    | StringValue(strVal)               -> strVal.Value
    | RefValue(newModName, newVasName)  -> GetValueAstring (GetActualValue newModName newVasName r) r
    | _                                 -> raise(SemanticError (v.Location, sprintf "Expecting String value")) 


let rec GetValueAsInt (v:Asn1Value) r=
    match v.Kind with
    | IntegerValue(a)                       -> a.Value
    | RefValue(modName,valName)             -> GetValueAsInt (GetActualValue modName valName r) r
    | _                                     -> raise(SemanticError (v.Location, sprintf "Expecting Integer value"))

let rec GetValueAsDouble (v:Asn1Value) r=
    match v.Kind with
    | IntegerValue(a)                       -> double (a.Value)
    | RealValue(a)                          -> a.Value
    | RefValue(modName,valName)             -> GetValueAsDouble (GetActualValue modName valName r) r
    | _                                     -> raise(SemanticError (v.Location, sprintf "Expecting Real value"))

let getChildType name (children:seq<ChildInfo>)= 
    match children |> Seq.tryFind(fun ch -> ch.Name = name) with
    | Some(x)       -> x.Type
    | None          -> 
        let (n,loc) = name.AsTupple
        raise(SemanticError(loc, sprintf "No Component with name: %s is defined." n))



let ModuleHasAdaBody (m:Asn1Module) (r:AstRoot) = 
    let hasChoiceVars = m.ValueAssignments |> List.exists(fun x -> match (GetActualType x.Type r).Kind with Choice(_) -> true | _ -> false)
    (m.TypeAssignments.Length > 0) || hasChoiceVars

let ModuleHasAutoCodecs (m:Asn1Module) (r:AstRoot) = 
    m.TypeAssignments.Length > 0

(* Funtions related with return error codes *)

/// key must contains the c.Name
let GetChildInfoErrorCode (c:ChildInfo) (key:list<string>) (r:AstRoot) =
    let name = ToC (r.TypePrefix + (GetLongNameByKey_C key))
    match c.Optionality with
    | Some(AlwaysPresent)   -> Some("ERR_" + name + "_IS_ABSENT")
    | Some(AlwaysAbsent)    -> Some("ERR_" + name + "_IS_PRESENT")
    |  _                    -> None

let GetTypeConstraintsErrorCode (cons:seq<Asn1Constraint>) (key:list<string>) (r:AstRoot) =
    let name = ToC (r.TypePrefix + (GetLongNameByKey_C key))
    match Seq.isEmpty cons with
    | true      -> None
    | false     -> Some("ERR_"+ name)

let GetEnumErrorCode (key:list<string>) (r:AstRoot) =
    let name = ToC (r.TypePrefix + (GetLongNameByKey_C key))
    "ERR_"+ name+"_unknown_enumeration_value"

let GetChoiceErrorCode (key:list<string>) (r:AstRoot) =
    let name = ToC (r.TypePrefix + (GetLongNameByKey_C key))
    "ERR_"+ name+"_unknown_choice_index"


let rec GetMySelfAndChildren (t:Asn1Type) = 
    seq {
        yield t
        match t.Kind with
        | SequenceOf(conType) ->  yield! GetMySelfAndChildren conType
        | Sequence(children) | Choice(children)-> 
            for ch in children do 
                yield! GetMySelfAndChildren ch.Type
        |_ -> ()    
    }

let rec GetMySelfAndChildren2 (t:Asn1Type) = 
    let rec GetMySelfAndChildren2_aux (acnInserted:bool) (t:Asn1Type) = 
        seq {
            yield (acnInserted, t)
            match t.Kind with
            | SequenceOf(conType) ->  yield! GetMySelfAndChildren2_aux false conType
            | Sequence(children) | Choice(children)-> 
                for ch in children do 
                    yield! GetMySelfAndChildren2_aux ch.AcnInsertedField ch.Type
            |_ -> ()    
        }
    GetMySelfAndChildren2_aux false t

let rec GetMySelfAndChildrenWithPath (t:Asn1Type) (curPath:list<string>) = 
    seq {
        yield (t, curPath)
        match t.Kind with
        | SequenceOf(conType) ->  yield! GetMySelfAndChildrenWithPath conType (curPath@["#"])
        | Sequence(children) | Choice(children)-> 
            for ch in children do 
                yield! GetMySelfAndChildrenWithPath ch.Type (curPath@[ch.Name.Value])
        |_ -> ()    
    }


let rec GetMySelfAndChildrenActual (t:Asn1Type) r = 
    seq {
        match t.Kind with
        | SequenceOf(conType) ->  yield t; yield! GetMySelfAndChildrenActual conType r
        | Sequence(children) | Choice(children)-> 
            yield t
            for ch in children do 
                yield! GetMySelfAndChildrenActual ch.Type r
        | ReferenceType(_)  -> yield! GetMySelfAndChildrenActual (GetActualType t r) r
        |_ -> yield t    
    }

let IsOrContainsChoice t r = 
    GetMySelfAndChildrenActual t r|> Seq.exists(fun c-> match c.Kind with Choice(_) -> true |_ ->false)


//1. For Seq, SqOf, Choice move WITH COMPOENET constraints to children and then call it recursivelly for the children
//2. For ref types with constraints call it for base type recursivelly
//3. else return input

let rec foldMap2 func state lst =
    match lst with
    | []        -> [],state
    | h::tail   -> 
        let procItem, newState = func state h
        let restList, finalState = tail |> foldMap2 func newState
        procItem::restList, finalState

let rec RemoveWithComponents_priv (t:Asn1Type) (r:AstRoot) path retList =
    let ApplyConstraintsToComponents (components:list<ChildInfo>) (parenConstraints:list<Asn1Constraint>) retList =
        let handleChild retList (ch:ChildInfo) =
            let chooseInnerCon = function
                | WithComponentsConstraint(namedItems) -> 
                    match namedItems |> Seq.tryFind(fun ni -> ni.Name.Value = ch.Name.Value) with
                    | Some(item)    -> item.Contraint
                    | _             -> None
                | _                                   -> None
            let chooseOptionality = function
                | WithComponentsConstraint(namedItems) -> 
                    match namedItems |> Seq.tryFind(fun ni -> ni.Name.Value = ch.Name.Value) with
                    | Some(item)    -> 
                        match item.Mark with
                        | NoMark        -> ch.Optionality
                        | MarkPresent   -> Some(AlwaysPresent)
                        | MarkAbsent    -> Some(AlwaysAbsent)
                        | MarkOptional  -> ch.Optionality
                    | _             -> None
                | _                                   -> None

            let extraCons = parenConstraints |> List.choose chooseInnerCon
            let newOptionality = match parenConstraints |> List.choose chooseOptionality with
                                 | []    -> ch.Optionality
                                 | x::xs -> Some x
            let newChType = {ch.Type with Constraints = (ch.Type.Constraints @ extraCons)}
            let newType, newRetList = RemoveWithComponents_priv newChType r (path@[ch.Name.Value]) retList
            {ch with Type = newType; Optionality = newOptionality}, newRetList
        components |> foldMap2 handleChild retList
    match t.Kind with
    | Sequence(children)    -> 
        let newComponents, newRetList = ApplyConstraintsToComponents children t.Constraints retList
        {t with Kind = Sequence(newComponents); Constraints=[]}, newRetList
    | Choice(children)      -> 
        let newComponents, newRetList = ApplyConstraintsToComponents children t.Constraints retList
        {t with Kind = Choice(newComponents); Constraints=[]}, newRetList
    | SequenceOf(child)     -> 
        let withComp = t.Constraints |> List.choose(fun c -> match c with WithComponentConstraint(innerC) -> Some innerC | _ -> None)
        let restComp = t.Constraints |> List.choose(fun c -> match c with WithComponentConstraint(_) -> None | _ -> Some c)
        let newChild, newRetList = RemoveWithComponents_priv {child with Constraints = (child.Constraints@withComp)} r (path@["#"]) retList
        {t with Kind = SequenceOf(newChild); Constraints=restComp}, newRetList
    | ReferenceType(md,ts,_) when not (Seq.isEmpty t.Constraints)  -> 
        let baseType = GetBaseType t r
        let baseTypeWithCons = {baseType with Constraints=baseType.Constraints @ t.Constraints}
        let newRetList =  (path, (md.Value,ts.Value))::retList 
        RemoveWithComponents_priv baseTypeWithCons r path newRetList
    | _                                                      -> t, retList

let rec RemoveWithComponents (t:Asn1Type) (r:AstRoot)  =
    RemoveWithComponents_priv t r [] [] |> fst



let ConvertOctetStringValue_to_BitStringValue (v:Asn1Value) =
    match v.Kind with
    | OctetStringValue(bytes)   ->
        let handleOctet (oct:byte) =
            let handleNibble (n:char) =
                match n with
                |'0'-> "0000"
                |'1'-> "0001"
                |'2'-> "0010"
                |'3'-> "0011"
                |'4'-> "0100"
                |'5'-> "0101"
                |'6'-> "0110"
                |'7'-> "0111"
                |'8'-> "1000"
                |'9'-> "1001"
                |'A'-> "1010"
                |'B'-> "1011"
                |'C'-> "1100"
                |'D'-> "1101"
                |'E'-> "1110"
                |'F'-> "1111"
                | _ -> raise(BugErrorException "")
            let octStr = sprintf "%02X" oct
            (handleNibble octStr.[0]) + (handleNibble octStr.[1])
        let bitStr = bytes |> Seq.map(fun x -> handleOctet x.Value ) |> Seq.StrJoin ""
        {v with Kind = BitStringValue({StringLoc.Value=bitStr; Location=v.Location})}
    | _                         -> raise(BugErrorException "")    


//let bitStringValueToByteArray (s:StringLoc) =
//    let s1 = s.Value.ToCharArray() |> Seq.map(fun x -> if x='0' then 0uy else 1uy) |> Seq.toList
//    let rec BitsToNibbles l:list<byte> =
//        match l with
//        | []                   -> []
//        | i1::[]               -> [i1*8uy]
//        | i1::i2::[]           -> [i1*8uy+i2*4uy]
//        | i1::i2::i3::[]       -> [i1*8uy+i2*4uy+i3*2uy]
//        | i1::i2::i3::i4::tail -> (i1*8uy+i2*4uy+i3*2uy+i4)::(BitsToNibbles tail)           
//    let rec NibblesToBytes l:list<byte> =
//        match l with
//        | []                    -> []
//        | i1::[]                -> [i1*16uy]
//        | i1::i2::tail          -> (i1*16uy+i2)::(NibblesToBytes tail)
//    NibblesToBytes (BitsToNibbles s1) 

let ConvertBitStringValue_to_OctetStringValue (v:Asn1Value) =
    match v.Kind with
    | BitStringValue(nBits) -> 
        let bytes = bitStringValueToByteArray nBits |> Array.toList |> List.map ByteLoc.ByValue
        {v with Kind = OctetStringValue(bytes)}
    | _                         -> raise(BugErrorException "")    





let rec GetConstraintValues (c:Asn1Constraint)  = 
    seq {
        match c with
        | SingleValueContraint(v)               -> yield v
        | RangeContraint(v1,v2,_,_)             -> yield v1; yield v2
        | RangeContraint_MIN_val(v1,_)          -> yield v1
        | RangeContraint_val_MAX(v2,_)          -> yield v2
        | RangeContraint_MIN_MAX                -> ()
        | TypeInclusionConstraint(_)            -> ()
        | SizeContraint(c)                      -> yield! GetConstraintValues  c
        | AlphabetContraint(c)                  -> yield! GetConstraintValues  c
        | UnionConstraint(a,b,_)                  -> yield! GetConstraintValues  a; yield! GetConstraintValues  b
        | IntersectionConstraint(a,b)           -> yield! GetConstraintValues  a; yield! GetConstraintValues  b
        | AllExceptConstraint(c)                -> yield! GetConstraintValues  c
        | ExceptConstraint(a,b)                 -> yield! GetConstraintValues  a; yield! GetConstraintValues  b
        | RootConstraint(c)                     -> yield! GetConstraintValues  c
        | RootConstraint2(a,b)                  -> yield! GetConstraintValues  a; yield! GetConstraintValues  b
        | WithComponentConstraint(c)            -> yield! GetConstraintValues  c
        | WithComponentsConstraint(namedCons)   -> for c in namedCons do 
                                                    match c.Contraint with Some(x) -> yield! GetConstraintValues  x | _ -> ()
    }



let rec GetTypeValues (t:Asn1Type) (curPath:List<string>)=
    seq {
        match t.Kind with
        | Sequence(children) ->
            for ch in children do
                match ch.Optionality with
                | Some(Default(v))  -> yield (ch.Type, v, curPath@[ch.Name.Value])
                | _                 -> ()
        | _ -> ()
        for c in t.Constraints do
            for v in GetConstraintValues c do
                yield (t, v, curPath)
    }


let GetValueID (v:Asn1Value) =
    let rec GetValueIDAux (v:Asn1Value) =
        match v.Kind with
        | IntegerValue(a)   -> a.GetHashCode2()
        | RealValue(a)      -> a.GetHashCode2()
        | StringValue(a)    -> a.GetHashCode2()
        | BooleanValue(a)   -> a.GetHashCode2()
        | BitStringValue(a) -> a.GetHashCode2()
        | OctetStringValue(a)-> a |> Seq.fold(fun acc cur-> acc ^^^ (cur.GetHashCode2())) 0
        | RefValue(s1,s2)    -> s1.GetHashCode2() ^^^ s2.GetHashCode2()
        | SeqOfValue(vals)   -> vals |> Seq.fold(fun acc cur -> acc ^^^ (GetValueIDAux cur)) 0
        | SeqValue(chVals)   -> chVals |> Seq.fold(fun acc (chName, chVal) -> acc ^^^ (GetValueIDAux chVal) ^^^ (chName.GetHashCode2())) 0
        | ChValue(altName,altVal)   ->  altName.GetHashCode2() ^^^ (GetValueIDAux altVal)
        | NullValue          -> 0
    "var"+(System.Math.Abs(GetValueIDAux v)).ToString()


let AdaUses (r:AstRoot) =
    seq {
        for f in r.Files do
            for m in f.Modules do
                for tas in m.TypeAssignments do
                    yield sprintf "%s:%s" tas.Name.Value (ToC m.Name.Value);
    } |> Seq.toList


let GetItemValue (nItems:NamedItem list) (item: NamedItem) (r:AstRoot) =
    match item._value with
    |Some(vl) -> GetValueAsInt vl r
    |None     ->
        let i = nItems |> Seq.findIndex (fun n -> n.Name.Value = item.Name.Value)       
        BigInteger i
