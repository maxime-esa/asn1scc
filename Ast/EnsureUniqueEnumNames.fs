module EnsureUniqueEnumNames

open FsUtils
open Ast
open System
open CloneTree


type State =  string list

let rec handleChoices (r:AstRoot) =
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
                let newChildren, finalState = children |> foldMap CloneChild state
                {old with Kind =  Choice(newChildren)}, finalState
            | _             -> defaultConstructors.cloneType old m key cons state

        let newTree = CloneTree r {defaultConstructors with cloneType =  CloneType; } doubleEnumNames |> fst
        handleChoices newTree


let rec handleEnums (r:AstRoot) =
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
                {old with Kind =  Enumerated(itesm|> List.map copyItem)}, state
            | _             -> defaultConstructors.cloneType old m key cons state

        let newTree = CloneTree r {defaultConstructors with cloneType =  CloneType; } doubleEnumNames |> fst
        handleEnums newTree


let DoWork (ast:AstRoot)=
    let r1 = handleChoices ast
    let r2 = handleEnums r1
    r2


