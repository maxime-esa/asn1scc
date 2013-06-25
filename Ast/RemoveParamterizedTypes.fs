module RemoveParamterizedTypes

open System.Numerics
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils
open ParameterizedAsn1Ast




let rec CloneType  (namedArgs:list<StringLoc*TemplateArgument>) (old:Asn1Type) :Asn1Type =
    let CloneChild (ch:ChildInfo) =
        {ch with Type = CloneType namedArgs ch.Type; Optionality = match ch.Optionality with
                                                                   | Some(Default(v))   -> Some(Default (CloneValue namedArgs v))
                                                                   | _                  -> ch.Optionality}
    let cloneSeqChild  = function
        | ComponentsOf (x,y) -> ComponentsOf (x,y)
        | ChildInfo ch   -> ChildInfo (CloneChild ch)
    let newKind, newCons = 
        let cons = old.Constraints |> List.map (CloneConstraint namedArgs)
        match old.Kind with
        | Sequence(children)  ->   Sequence(children |> List.map cloneSeqChild ), cons
        | Choice(children)    ->   Choice(children |> List.map CloneChild), cons
        | SequenceOf(child)   ->   SequenceOf(CloneType namedArgs child ), cons
        | ReferenceType(md,ts,args)    ->
            match args with
            | []        -> 
                match namedArgs |> Seq.tryFind (fun (nm, _) -> nm = ts) with
                | Some(_,arg)       -> 
                    match arg with
                    | ArgType(x)     -> x.Kind, (x.Constraints|> List.map (CloneConstraint namedArgs))@cons
                    | _                                     -> raise(BugErrorException "")
                | None              -> old.Kind, cons

            | _         -> old.Kind,cons
        | _                                        ->   old.Kind,cons
        
    {
        Asn1Type.Kind = newKind
        Constraints = newCons
        Location = old.Location
    }

and CloneConstraint  (namedArgs:list<StringLoc*TemplateArgument>) (c:Asn1Constraint) :Asn1Constraint =
    match c with
    | SingleValueContraint(v)          -> SingleValueContraint (CloneValue namedArgs v)
    | RangeContraint(v1,v2,b1,b2)            -> RangeContraint(CloneValue namedArgs v1,CloneValue namedArgs v2,b1,b2)
    | RangeContraint_val_MAX(v,b)        -> RangeContraint_val_MAX (CloneValue namedArgs v,b)
    | RangeContraint_MIN_val(v,b)        -> RangeContraint_MIN_val (CloneValue namedArgs v,b)
    | TypeInclusionConstraint(s1,s2)   -> TypeInclusionConstraint(s1,s2)
    | SizeContraint(c)                 -> SizeContraint(CloneConstraint namedArgs c)
    | AlphabetContraint(c)             -> AlphabetContraint(CloneConstraint namedArgs c)
    | UnionConstraint(c1,c2)           -> UnionConstraint(CloneConstraint namedArgs c1, CloneConstraint namedArgs c2)
    | IntersectionConstraint(c1,c2)    -> IntersectionConstraint(CloneConstraint namedArgs c1, CloneConstraint namedArgs c2)
    | AllExceptConstraint(c)           -> AllExceptConstraint(CloneConstraint namedArgs c)
    | ExceptConstraint(c1,c2)          -> ExceptConstraint(CloneConstraint namedArgs c1, CloneConstraint namedArgs c2)
    | RootConstraint(c1)               -> RootConstraint(CloneConstraint namedArgs c)
    | RootConstraint2(c1,c2)           -> RootConstraint2(CloneConstraint namedArgs c1, CloneConstraint namedArgs c2)
    | WithComponentConstraint(c)       -> WithComponentConstraint(CloneConstraint namedArgs c)
    | WithComponentsConstraint(ncs)    -> WithComponentsConstraint(ncs|> Seq.map (CloneNamedConstraint namedArgs))

and CloneNamedConstraint (namedArgs:list<StringLoc*TemplateArgument>) (x:NamedConstraint) :NamedConstraint =
    {
        NamedConstraint.Name = x.Name; 
        Mark = x.Mark 
        Contraint = match x.Contraint with
                    | None  -> None
                    | Some(cc)  -> Some (CloneConstraint namedArgs cc)
    }
    

and CloneValue  (namedArgs:list<StringLoc*TemplateArgument>) (v:Asn1Value) :Asn1Value =
    match v.Kind with
    |RefValue(v1,v2)       -> 
        match namedArgs |> Seq.tryFind (fun (nm, _) -> nm = v2) with
        | Some(_,arg)       -> 
            match arg with
            | ArgValue(vl)     -> vl
            | _                                     -> raise(BugErrorException "")
        | None              -> v
    |SeqOfValue(vals)      -> {v with Kind = SeqOfValue(vals |> List.map (CloneValue namedArgs))}
    |SeqValue(vals)        -> {v with Kind = SeqValue(vals |> List.map (fun (n,v) -> (n, CloneValue namedArgs v)))}
    |ChValue(n,v)          -> {v with Kind = ChValue(n, CloneValue namedArgs v)}
    | _                                         -> v


and SpecializeType (r:AstRoot) (t:Asn1Type) =
    match t.Kind with
    | ReferenceType(md,ts, args)   when args.Length>0 -> SpecializeRefType r md ts args
    | ReferenceType(md,ts, args)    -> 
        let parmTas = getModuleByName r md |> getTasByName ts
        match parmTas.Parameters with
        | []    -> t
        | _     -> raise(SemanticError(t.Location, "Missing template arguments"))
    | _         -> t

and SpecializeRefType (r:AstRoot) (mdName:StringLoc) (tsName:StringLoc) (args:list<TemplateArgument>) =
    let parmTas = getModuleByName r mdName |> getTasByName tsName
    let SpecializeTemplatizedArgument (arg:TemplateArgument) =
        match arg with
        | ArgValue(_)      -> arg
        | ArgType(tp)      -> ArgType(SpecializeType r tp)

    let args = args |> List.map SpecializeTemplatizedArgument
    match parmTas.Parameters.Length = args.Length with
    | true  -> ()
    | false -> raise (SemanticError(tsName.Location, sprintf "The number of template arguments do not match the number of parameter in the type assignment"))
    
    let getNameArg (arg:TemplateArgument, prm:TemplateParameter) =
        match prm, arg with
        | TypeParameter(s), ArgType(_)      -> (s, arg)
        | TypeParameter(_), ArgValue(_)     -> raise (SemanticError(tsName.Location, sprintf "Expecting type, not value"))
        | ValueParameter(_,_), ArgType(_)   -> raise (SemanticError(tsName.Location, sprintf "Expecting value, not type"))
        | ValueParameter(t,s), ArgValue(v)  -> (s,arg)
    let namedArgs = List.zip args parmTas.Parameters |> List.map getNameArg

    CloneType  namedArgs parmTas.Type



and DoAsn1Type (r:AstRoot) (t:Asn1Type) :Asn1Type =
    let DoChildInfo (r:AstRoot) (c:ChildInfo) :ChildInfo =
        {
            ChildInfo.Name = c.Name
            Type = DoAsn1Type r c.Type
            Optionality = c.Optionality 
            AcnInsertedField = c.AcnInsertedField
            Comments = c.Comments
        }
    let DoSeqChildInof r ch =
        match ch with
        | ChildInfo ch  -> ChildInfo (DoChildInfo r ch)
        | ComponentsOf (m,t) -> ComponentsOf (m,t)

    let aux kind : Asn1Type=
        {
            Asn1Type.Kind = kind
            Constraints = t.Constraints 
            Location = t.Location
        }        
    match t.Kind with
    | SequenceOf(child) -> aux (SequenceOf(DoAsn1Type r child))
    | Sequence(children)-> aux (Sequence(children |> List.map (DoSeqChildInof r) ))
    | Choice(children)  -> aux (Choice(children |> List.map (DoChildInfo r) ))
    | ReferenceType(_)  -> SpecializeType r t
    | _                 -> aux t.Kind

    

let DoTypeAssignment (r:AstRoot) (tas:TypeAssignment) :TypeAssignment =
    {
        TypeAssignment.Name = tas.Name
        Type = DoAsn1Type r tas.Type
        Comments = tas.Comments
        Parameters = []
    }

let DoValueAssignment (r:AstRoot) (vas:ValueAssignment) :ValueAssignment =
    {
        ValueAssignment.Name = vas.Name
        Type = DoAsn1Type r vas.Type
        Value = vas.Value
    }


let DoModule (r:AstRoot) (m:Asn1Module) :Asn1Module =
    let DoImportedModule (x:ImportedModule) : ImportedModule option =
        let types = x.Types |> List.choose(fun ts -> 
                                            let tas = getModuleByName r x.Name |> getTasByName ts
                                            match tas.Parameters with
                                            | []    -> Some ts
                                            | _     -> None     //Paramterized Import, so remove it
                                       )
        match types with
        | []    -> None
        | _     -> Some  { ImportedModule.Name = x.Name; Types = types; Values = x.Values}
    {
        m with
            TypeAssignments = m.TypeAssignments |> List.filter(fun x -> x.Parameters.Length = 0) |> List.map (DoTypeAssignment r)
            ValueAssignments = m.ValueAssignments |> List.map (DoValueAssignment r)
            Imports = m.Imports |> List.choose DoImportedModule
    }

let DoFile (r:AstRoot) (f:Asn1File) :Asn1File =
    { f with Modules = f.Modules |> List.map (DoModule r) }




let DoWork (r:AstRoot) : AstRoot =
    { r with Files = r.Files |> List.map (DoFile r)  }