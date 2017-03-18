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

module UpdateAcnProperties

open Ast
open CloneTree
open FsUtils
type State = AcnTypes.AcnAst



let CheckReference (newAsn1:AstRoot) (newAcn:AcnTypes.AcnAst) (r:AcnTypes.LongReference) =
    let loc = r.Location
    let asn1Type = Ast.GetTypeByAbsPath r.TypeID newAsn1
    let GetParameterType md ts prmName =
        newAcn.Parameters |> Seq.tryFind(fun x -> x.ModName = md && x.TasName=ts && x.Name=prmName)
    let CheckReferenceKindWithTargetTypeKind (r:AcnTypes.LongReference) actTargetAsn1TypeKind =
        match r.Kind ,  actTargetAsn1TypeKind with
        | AcnTypes.PresenceBool, Boolean    -> ()
        | AcnTypes.PresenceBool, _          -> raise(SemanticError(loc, "expecting boolean field"))
        | AcnTypes.SizeDeterminant, Integer -> ()
        | AcnTypes.SizeDeterminant, _       -> raise(SemanticError(loc, "expecting integer field"))
        | AcnTypes.PresenceInt(_), Integer  -> ()
        | AcnTypes.PresenceInt(_), _        -> raise(SemanticError(loc, "expecting integer field"))
        | AcnTypes.PresenceStr(_), IA5String-> ()
        | AcnTypes.PresenceStr(_), NumericString-> ()
        | AcnTypes.PresenceStr(_), _        -> raise(SemanticError(loc, "expecting IA5String field"))
        | AcnTypes.ChoiceDeteterminant, Enumerated(nItems)  ->
            let atcType = Ast.GetActualType asn1Type newAsn1 
            match atcType.Kind with
            | Choice(children)  ->
                let altNames = children |> List.map(fun x -> x.Name.Value) |> List.sort
                let enmNames = nItems |> List.map(fun x -> x.Name.Value) |> List.sort
                match altNames = enmNames with
                | true   -> ()
                | false  -> raise(SemanticError(loc, "expecting an enumerated field with names matching the choice names"))
            | _                 ->  raise(BugErrorException "")
        | AcnTypes.ChoiceDeteterminant, _  -> raise(SemanticError(loc, "expecting an enumerated field with names matching the choice names"))
        | AcnTypes.RefTypeArgument(prmName), _  -> 
            match asn1Type.Kind with
            | ReferenceType(mdName, tsName,_) -> 
                let prm = newAcn.Parameters |> Seq.find(fun x -> x.ModName = mdName.Value && x.TasName = tsName.Value && x.Name = prmName)
                let actPrmType = (Ast.GetActualType (Ast.AcnAsn1Type2Asn1Type prm.Asn1Type) newAsn1).Kind
                match actPrmType, actTargetAsn1TypeKind with
                | Integer, Integer          -> ()
                | Integer, _                -> raise(SemanticError(loc, "expecting integer field"))
                | IA5String, IA5String      -> ()
                | IA5String, _              -> raise(SemanticError(loc, "expecting string field"))
                | Boolean, Boolean          -> ()
                | Boolean, _                -> raise(SemanticError(loc, "expecting boolean field"))
                | Enumerated(n1), Enumerated(n2)   ->
                    let a1 = n1 |> List.map(fun x -> x.Name.Value) |> List.sort
                    let a2 = n2 |> List.map(fun x -> x.Name.Value) |> List.sort
                    match a1 = a2 with
                    | true   -> ()
                    | false  -> raise(SemanticError(loc, "expecting a matching enumerated field"))
                | Enumerated(_), _          -> raise(SemanticError(loc, "expecting a matching enumerated field"))
                | _                         -> raise(BugErrorException "")
            | _                             -> raise(SemanticError(loc, "Arguments can be applied only to reference types "))

    match r.TypeID with
    | []       -> raise(BugErrorException "")
    | x::[]    -> raise(BugErrorException "")
    | md::ts::[] -> 
        match r.LongRef with
        | []            -> raise(BugErrorException "")
        | prmName::[]   -> 
            match (GetParameterType md ts prmName) with
            | None          -> raise(SemanticError(loc, sprintf "invalid reference '%s'" prmName))
            | Some(p)       -> 
                let actPrmType = (Ast.GetActualType (Ast.AcnAsn1Type2Asn1Type p.Asn1Type) newAsn1).Kind
                CheckReferenceKindWithTargetTypeKind r actPrmType
        | _             -> raise(SemanticError(loc, "invalid field"))
    | md::ts::restPart  ->
        let CheckLongChild () =
            let parentPath = r.TypeID |> List.rev |> List.tail |> List.rev
            let parentAsn1Type = Ast.GetTypeByAbsPath parentPath newAsn1
            let targetAsn1Type = Acn.Resolve.GetLongChild (newAsn1, newAcn) (parentAsn1Type, parentPath) r.LongRef loc
            let actTargetAsn1TypeKind =  (Ast.GetActualType (Ast.GetActualType targetAsn1Type newAsn1) newAsn1).Kind
            CheckReferenceKindWithTargetTypeKind r actTargetAsn1TypeKind
        match r.LongRef with
        | []            -> raise(BugErrorException "")
        | prmName::[]   -> 
            match (GetParameterType md ts prmName) with
            | None          -> CheckLongChild ()
            | Some(p)       -> 
                let actPrmType = (Ast.GetActualType (Ast.AcnAsn1Type2Asn1Type p.Asn1Type) newAsn1).Kind
                CheckReferenceKindWithTargetTypeKind r actPrmType
        | _             -> CheckLongChild ()

let DoWork (ast:AstRoot) (acn:AcnTypes.AcnAst) =
    let CheckReferences (newAsn1:AstRoot) (newAcn:AcnTypes.AcnAst) =
        newAcn.References |> Seq.iter (CheckReference newAsn1 newAcn)

    let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) =
        let CloneChild s (ch:ChildInfo) =
            let t,ns = cons.cloneType ch.Type m (key@[ch.Name.Value]) cons s
            {ch with Type = t},ns

        let newKind  = 
            match old.Kind with
            | Sequence(children)  -> 
                let acnChildren = acn.Types |> Seq.filter(fun x -> x.TypeID.Length-1=key.Length && (x.TypeID|>Seq.take key.Length|>Seq.toList)=key) |> Seq.toList
                let newChich = 
                    match Seq.isEmpty acnChildren with
                    | true  ->  children |> foldMap CloneChild state |> fst
                    | false ->
                            seq {
                                for acnChild in acnChildren do
                                    let acnChildName = acnChild.TypeID |> List.rev |> List.head
                                    match children |> Seq.tryFind(fun x-> x.Name.Value = acnChildName) with
                                    |Some(asn1Child)    -> yield {(CloneChild state asn1Child|> fst) with Comments=acnChild.Comments}
                                    |None               ->
                                        yield {
                                                ChildInfo.Name = {StringLoc.Value = acnChildName; Location= acnChild.Location}
                                                c_name = ToC2 acnChildName
                                                ada_name = ToC2  acnChildName
                                                present_when_name = ToC2 acnChildName
                                                Type =  match acnChild.ImpMode with
                                                        | AcnTypes.RecordField       -> raise(BugErrorException "Child exists in ASN.1")
                                                        | AcnTypes.AcnTypeImplMode.LocalVariable(asn1Type) | AcnTypes.FunctionParameter(asn1Type) ->
                                                            match asn1Type with
                                                            | AcnTypes.Integer   -> {Asn1Type.Kind = Ast.Integer; Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
                                                            | AcnTypes.Boolean   -> {Asn1Type.Kind = Ast.Boolean; Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
                                                            | AcnTypes.NullType  -> {Asn1Type.Kind = Ast.NullType; Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
                                                            | AcnTypes.RefTypeCon(md,ts)  -> {Asn1Type.Kind = Ast.ReferenceType(md,ts, false); Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
                                                AcnInsertedField= match acnChild.ImpMode with
                                                                  | AcnTypes.RecordField       -> raise(BugErrorException "Child exists in ASN.1")
                                                                  | AcnTypes.AcnTypeImplMode.LocalVariable(_)    -> true
                                                                  | AcnTypes.FunctionParameter(_)                -> true
                                                Optionality = None
                                                Comments = acnChild.Comments
                                            }

                            } |>Seq.toList

                Sequence(newChich)
            | Choice(children)    -> 
                let newChildren, finalState = children |> foldMap CloneChild state
                Choice(newChildren)
            | SequenceOf(child)   -> 
                let nch,ns = cons.cloneType child m (key@["#"]) cons state
                SequenceOf(nch)
            | _                   -> old.Kind

        {
            Kind = newKind
            Constraints = old.Constraints
            Location = old.Location
            AcnProperties = match acn.Types |> Seq.tryFind(fun x -> x.TypeID=key) with
                            |None                -> []
                            |Some(acnType)       -> acnType.Properties
        }, state
    let (newAsn1,newAcn) = CloneTree ast {defaultConstructors with cloneType =  CloneType} acn
    CheckReferences newAsn1 newAcn
    (newAsn1,newAcn)

    

