module EnsureUniqueEnumNames

open FsUtils
open Ast
open System
open CloneTree


type State =  string list

let rec handleChoices (r:AstRoot) (renamePolicy:ParameterizedAsn1Ast.EnumRenamePolicy)=
    let doubleEnumNames = seq {
        for m in r.Modules do
            for tas in m.TypeAssignments do
                for t in GetMySelfAndChildren tas.Type  do
                    match t.Kind with
                    | Choice(children)  -> 
                        let names = children |> List.map(fun x -> x.uniqueName)
                        yield! names
                    | _                 -> () } |> Seq.toList |> List.keepDuplicates

    match doubleEnumNames with
    | []    -> r
    | _     ->
        let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) =
            let CloneChild s (ch:ChildInfo) =
                let t,ns = cons.cloneType ch.Type m (key@[ch.Name.Value]) cons s
                let newUniqueName =
                    match state |> Seq.exists ((=) ch.uniqueName) with
                    | false     -> ch.uniqueName
                    | true      ->
                        let newPrefix = key |> List.rev |> List.map ToC |> Seq.skipWhile(fun x -> ch.uniqueName.Contains x) |> Seq.head
                        newPrefix + "_" + ch.uniqueName
            
                {ch with Type = t; uniqueName= newUniqueName},ns

            match old.Kind with
            | Choice(children)    -> 
                //let newChildren, finalState = children |> foldMap CloneChild state
                let newChildren, finalState =
                    match renamePolicy with
                    | ParameterizedAsn1Ast.NoRenamePolicy           -> children, state
                    | ParameterizedAsn1Ast.SelectiveEnumerants      -> children |> foldMap CloneChild state
                    | ParameterizedAsn1Ast.AllEnumerants            -> 
                        let newChildren, finalState = children |> foldMap CloneChild state
                        let newPrefix = newChildren |> List.map(fun itm -> itm.uniqueName.Replace(itm.Name.Value,"")) |> List.maxBy(fun prf -> prf.Length)
                        let newChildren = newChildren |> List.map(fun ch -> {ch with uniqueName = newPrefix + ch.Name.Value})
                        newChildren, finalState
                {old with Kind =  Choice(newChildren)}, finalState
            | _             -> defaultConstructors.cloneType old m key cons state

        let newTree = CloneTree r {defaultConstructors with cloneType =  CloneType; } doubleEnumNames |> fst
        handleChoices newTree renamePolicy


let rec handleEnums (r:AstRoot) (renamePolicy:ParameterizedAsn1Ast.EnumRenamePolicy) =
    let doubleEnumNames = seq {
        for m in r.Modules do
            for tas in m.TypeAssignments do
                for t in GetMySelfAndChildren tas.Type  do
                    match t.Kind with
                    | Enumerated(itesm) -> 
                        let names = itesm |> List.map(fun x -> x.uniqueName)
                        yield! names
                    | _                 -> () } |> Seq.toList |> List.keepDuplicates

    match doubleEnumNames with
    | []    -> r
    | _     ->
        let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) =
            match old.Kind with
            | Enumerated(itesm)    -> 
                let copyItem (old:NamedItem) =
                    let newUniqueName =
                        match state |> Seq.exists ((=) old.uniqueName) with
                        | false     -> old.uniqueName
                        | true      ->
                            let newPrefix = key |> List.rev |> List.map ToC |> Seq.skipWhile(fun x -> old.uniqueName.Contains x) |> Seq.head
                            newPrefix + "_" + old.uniqueName
                    {old with uniqueName=newUniqueName}
                let newItems = 
                    match renamePolicy with
                    | ParameterizedAsn1Ast.NoRenamePolicy           -> itesm
                    | ParameterizedAsn1Ast.SelectiveEnumerants      -> itesm|> List.map copyItem
                    | ParameterizedAsn1Ast.AllEnumerants            -> 
                        let newPrefix = itesm|> List.map copyItem |> List.map(fun itm -> itm.uniqueName.Replace(itm.Name.Value,"")) |> List.maxBy(fun prf -> prf.Length)
                        itesm|> List.map (fun itm -> {itm with uniqueName = newPrefix + itm.uniqueName})
                {old with Kind =  Enumerated(newItems)}, state
            | _             -> defaultConstructors.cloneType old m key cons state

        let newTree = CloneTree r {defaultConstructors with cloneType =  CloneType; } doubleEnumNames |> fst
        handleEnums newTree renamePolicy


let DoWork (ast:AstRoot) (renamePolicy:ParameterizedAsn1Ast.EnumRenamePolicy) =
    match renamePolicy with
    | ParameterizedAsn1Ast.NoRenamePolicy           -> ast
    | _                                             ->
        let r1 = handleChoices ast renamePolicy
        let r2 = handleEnums r1 renamePolicy
        r2


