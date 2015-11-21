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

module RemoveNumericStringsAndFixEnums

open System
open System.Numerics
open FsUtils
open Ast
open System
open CloneTree


type State = Ast.AstRoot //dumy

let CloneType (old:Asn1Type) m (key:list<string>) (cons:Constructors<State>) (state:State) =
    match old.Kind with
    |NumericString  -> 
        let zero = {Asn1Value.Kind = StringValue("0".AsLoc); Location = emptyLocation}
        let nine = {Asn1Value.Kind = StringValue("9".AsLoc); Location = emptyLocation}
        let space = {Asn1Value.Kind = StringValue(" ".AsLoc); Location = emptyLocation}
        let newConstraint = AlphabetContraint(UnionConstraint(RangeContraint(zero,nine, true, true),SingleValueContraint(space), false))
        {old with Kind = IA5String; Constraints = newConstraint::old.Constraints}, state
    | Enumerated(namedItems) ->

        let createAsn1ValueByBigInt biVal = { Asn1Value.Kind = IntegerValue (IntLoc.ByValue biVal); Location = emptyLocation}

        let allocated = namedItems |> List.filter(fun x -> x._value.IsSome)
        let unallocated = namedItems |> List.filter(fun x -> x._value.IsNone)
        let rec allocateItems (unallocated:NamedItem list) (allocated:NamedItem list) potentialValue: NamedItem list =
            match unallocated with
            | []    -> allocated
            |x::xs  -> 
                let rec getValue (allocated:NamedItem list) (vl:BigInteger) =
                    match allocated |> Seq.exists(fun ni -> match ni._value with Some value -> vl = (Ast.GetValueAsInt value state) | None -> false) with
                    | false -> vl
                    | true  -> getValue allocated (vl + 1I)
                let vl = getValue allocated potentialValue
                let newAllocatedItems = allocated@[{x with _value = Some (createAsn1ValueByBigInt vl)} ]
                allocateItems xs newAllocatedItems (vl + 1I)
        let newItems = allocateItems unallocated allocated 0I |> List.sortBy(fun ni -> namedItems |> Seq.findIndex(fun x -> x.Name.Value = ni.Name.Value) )
        {old with Kind = Enumerated(newItems) }, state
    | _             -> defaultConstructors.cloneType old m key cons state

let DoWork ast =
    CloneTree ast {defaultConstructors with cloneType =  CloneType; } ast |> fst


