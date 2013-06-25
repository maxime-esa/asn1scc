module RemoveNumericStrings

open FsUtils
open Ast
open System
open CloneTree


type State = int //dumy

let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) =
    match old.Kind with
    |NumericString  -> 
        let zero = {Asn1Value.Kind = StringValue("0".AsLoc); Location = emptyLocation}
        let nine = {Asn1Value.Kind = StringValue("9".AsLoc); Location = emptyLocation}
        let space = {Asn1Value.Kind = StringValue(" ".AsLoc); Location = emptyLocation}
        let newConstraint = AlphabetContraint(UnionConstraint(RangeContraint(zero,nine, true, true),SingleValueContraint(space)))
        {old with Kind = IA5String; Constraints = newConstraint::old.Constraints}, state
    | _             -> defaultConstructors.cloneType old m key cons state

let DoWork ast =
    CloneTree ast {defaultConstructors with cloneType =  CloneType; } 0 |> fst


