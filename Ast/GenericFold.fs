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

module GenericFold
open Ast
open Monads
open FsUtils

let enumIntegerType = 
    {
        Asn1Type.Kind = Integer
        Constraints = []
        AcnProperties = []
        Location = FsUtils.emptyLocation
    }

let stringType = 
    {
        Asn1Type.Kind = IA5String
        Constraints = []
        AcnProperties = []
        Location = FsUtils.emptyLocation
    }

let sizeIntegerType = 
    {
        Asn1Type.Kind = Integer
        Constraints = [RangeContraint_val_MAX ({Asn1Value.Kind = IntegerValue(FsUtils.IntLoc.ByValue 0I); Location=FsUtils.emptyLocation},true)]
        AcnProperties = []
        Location = FsUtils.emptyLocation
    }





type Scope = {
    r : AstRoot
    f : Asn1File
    m : Asn1Module
    a : TypeOrValueAssignment
    parents : ((ChildInfo option)*Asn1Type) list
}

and TypeOrValueAssignment = 
    | TAS of TypeAssignment
    | VAS of ValueAssignment


let error (loc: SrcLoc) format = 
    let doAfter s = 
        raise (SemanticError (loc, s))
    Printf.ksprintf doAfter format 

type CheckContext =
    | CheckContent
    | CheckSize          
    | CheckCharacter    


let foldAstRoot 
    roorFunc                    
    fileFunc        
    modFunc 
    tasFunc 
    vasFunc 
    refTypeFunc 
    baseTypeFunc 
    enmItemFunc 
    seqOfTypeFunc 
    seqTypeFunc 
    chTypeFunc 
    sequenceChildFunc 
    choiceChildFunc 
    refValueFunc  
    enumValueFunc 
    intValFunc 
    realValFunc 
    ia5StringValFunc 
    numStringValFunc 
    boolValFunc 
    octetStringValueFunc 
    bitStringValueFunc 
    nullValueFunc 
    seqOfValueFunc 
    seqValueFunc 
    chValueFunc
    singleValueContraintFunc 
    rangeContraintFunc 
    greaterThanContraintFunc
    lessThanContraintFunc
    alwaysTtrueContraintFunc
    typeInclConstraintFunc
    unionConstraintFunc
    intersectionConstraintFunc
    notConstraintFunc
    exceptConstraintFunc
    rootConstraintFunc
    root2ConstraintFunc
    (r:AstRoot) =

    let rec loopAstRoot (r:AstRoot) =
        cont {
            let! files = r.Files |> mmap  (loopFile r)
            return roorFunc r files
        }
    and loopFile (r:AstRoot) (f:Asn1File) =
        cont {
            let! modules = f.Modules |> mmap  (loopModule r f)
            return fileFunc r f modules
        }
    and loopModule (r:AstRoot) (f:Asn1File) (m:Asn1Module) =
        cont {
            let! tases = m.TypeAssignments |> mmap  (loopTypeAssignment r f m)
            let! vases = m.ValueAssignments |> mmap  (loopValueAssignments r f m)
            return modFunc r f m tases vases
        }
    and loopTypeAssignment (r:AstRoot) (f:Asn1File) (m:Asn1Module) (tas:TypeAssignment) =
        cont {
            let s = {Scope.r = r; f = f; m=m; a= TAS tas; parents=[]}
            let! asn1Type = loopType s tas.Type
            return tasFunc r f m tas asn1Type
        }
    and loopValueAssignments (r:AstRoot) (f:Asn1File) (m:Asn1Module) (vas:ValueAssignment) =
        cont {
            let s = {Scope.r = r; f = f; m=m; a= VAS vas; parents=[]}
            let actType = GetActualType vas.Type  r
            let! asn1Type = loopType s vas.Type
            let! asn1Value = loopAsn1Value s actType vas.Value
            return vasFunc r f m vas asn1Type asn1Value
        }
    and loopType (s:Scope) (t:Asn1Type) =
        cont {
            match t.Kind with
            | ReferenceType (mdName,tasName, argList) ->
                let eqType = GetActualType t r 
                let! refCons = t.Constraints |> mmap  (loopConstraint s eqType CheckContent)
                let! newActType = loopType s eqType 
                return refTypeFunc s mdName.Value tasName.Value newActType refCons
            | Integer 
            | Real    
            | IA5String 
            | NumericString 
            | OctetString 
            | NullType 
            | BitString 
            | Boolean           ->
                let! newCons = t.Constraints |> mmap  (loopConstraint s t CheckContent)
                return baseTypeFunc s t newCons            
            | Enumerated (enmItems) ->  
                let! newCons = t.Constraints |> mmap  (loopConstraint s t CheckContent)
                let! newEnmItems = enmItems |> mmap (loopNamedItem s)
                return enmItemFunc s t newEnmItems newCons            
            | SequenceOf (innerType)  ->
                let! newCons = t.Constraints |> mmap  (loopConstraint s t CheckContent)
                let childScope = {s with parents = s.parents@[None, t]}
                let! newInnerType = loopType childScope  innerType
                return seqOfTypeFunc s t  newInnerType newCons
            | Sequence (children)     ->
                let! newCons = t.Constraints |> mmap  (loopConstraint s t CheckContent)
                let! newChildren = 
                    children |> mmap  (fun chInfo -> 
                        let childScope = {s with parents = s.parents@[(Some chInfo, t)]}
                        loopSequenceChild childScope chInfo)
                return seqTypeFunc s t newChildren newCons
            | Choice (children)       ->
                let! newCons = t.Constraints |> mmap  (loopConstraint s t CheckContent)
                let! newChildren = 
                    children |> mmap  (fun chInfo ->
                        let childScope = {s with parents = s.parents@[(Some chInfo, t)]}
                        loopChoiceChild childScope chInfo)
                return chTypeFunc s t newChildren newCons
        }

   
    and loopNamedItem (s:Scope) (ni:NamedItem) =
        cont {
            match ni._value with
            | Some v    ->
                let! newValue = loopAsn1Value s enumIntegerType v
                return (ni.Name, ni.Comments, Some newValue)
            | None      ->
                return (ni.Name, ni.Comments, None)
        }
    and loopSequenceChild (s:Scope)  (chInfo:ChildInfo) =
        cont {
            let! newType = loopType s  chInfo.Type
            let! newDefValue = 
                cont {
                    match chInfo.Optionality with
                    | Some Asn1Optionality.AlwaysAbsent
                    | Some Asn1Optionality.AlwaysPresent
                    | Some Asn1Optionality.Optional          
                    | None                                  -> 
                        return None
                    | Some  (Asn1Optionality.Default   vl)  ->
                        let eqType = GetActualType chInfo.Type r
                        let! newValue = loopAsn1Value s eqType vl
                        return Some newValue
                }
            return sequenceChildFunc s chInfo newType newDefValue
        }

    and loopChoiceChild (s:Scope)  (chInfo:ChildInfo) =
        cont {
            let! newType = loopType s  chInfo.Type
            return choiceChildFunc s   chInfo newType
        }
    and loopAsn1Value (s:Scope) (t:Asn1Type) (v:Asn1Value) =
        match v.Kind, t.Kind with
        | RefValue (md,vas), Enumerated (enmItems)   ->
                match enmItems |> Seq.tryFind (fun x -> x.Name.Value = vas.Value) with
                | Some enmItem    ->
                    cont {
                        let! actType = loopType s t
                        let! ni = loopNamedItem s enmItem
                        return enumValueFunc s t actType enmItem  ni          
                    }
                | None          ->
                    cont {
                        let actValue = GetActualValue md vas r
                        let! newActVal = loopAsn1Value s t actValue
                        return refValueFunc s t (md.Value, vas.Value) newActVal            
                    }
        | RefValue (md,vas), _   ->
                cont {
                    let actValue = GetActualValue md vas r
                    let! newActVal = loopAsn1Value s t actValue
                    return refValueFunc s t (md.Value, vas.Value) newActVal            
                }
        | IntegerValue bi, Integer          ->
            cont {
                let! actType = loopType s t
                return intValFunc s t actType bi.Value
            }
        | IntegerValue bi, Real  _           ->
            cont {
                let! actType = loopType s t
                let dc:double = (double)bi.Value
                return realValFunc s t actType dc
            }
        | RealValue dc , Real   _                  -> 
            cont {
                let! actType = loopType s t
                return realValFunc s t actType dc.Value
            }
        | StringValue str, IA5String _   -> 
            cont {
                let! actType = loopType s t
                return ia5StringValFunc s t actType str.Value
            }
        | StringValue str , NumericString _   -> 
            cont {
                let! actType = loopType s t
                return numStringValFunc s t actType str.Value
            }
        | BooleanValue b, Boolean _       ->
            cont {
                let! actType = loopType s t
                return boolValFunc s t actType b.Value
            }
        | OctetStringValue b, OctetString _         ->
            cont {
                let! actType = loopType s t
                return octetStringValueFunc s t actType b
            }
        | OctetStringValue b, BitString _        ->
            cont {
                let! actType = loopType s t
                return octetStringValueFunc s t actType b
            }
        | BitStringValue b, BitString _           ->
            cont {
                let! actType = loopType s t
                return bitStringValueFunc s t actType b 
            }
        | NullValue , NullType _   ->
            cont {
                let! actType = loopType s t
                return nullValueFunc s t actType             
            }
        | SeqOfValue  vals, SequenceOf chType    ->
            cont {
                let! actType = loopType s t
                let eqType = GetActualType chType r
                let! newVals = vals |> mmap  (loopAsn1Value s eqType)
                return seqOfValueFunc s t actType  newVals
            }
        | SeqValue    namedValues, Sequence children ->
            cont {
                let! actType = loopType s t
                let! newValues =  namedValues |> mmap  (loopSeqValueChild s  children )
                return seqValueFunc s t actType newValues
            }
        | ChValue (name,vl), Choice children         ->
            match children |> Seq.tryFind(fun ch -> ch.Name.Value = name.Value) with
            | Some chType   ->
                cont {
                    let! actType = loopType s t
                    let eqType = GetActualType chType.Type r 
                    let! newValue = loopAsn1Value s eqType vl
                    return chValueFunc s t actType name newValue
                }
            | None  -> 
                error name.Location "Invalid alternative name '%s'" name.Value
        | _         ->
            error v.Location "Invalid combination ASN.1 type and ASN.1 value"


    and loopSeqValueChild (s:Scope)  (children: list<ChildInfo>) (nm:StringLoc, chv:Asn1Value) = 
        cont {
            let child = 
                match children |> Seq.tryFind (fun ch -> ch.Name.Value = nm.Value) with
                | Some ch -> ch
                | None    -> error nm.Location "Invalid child name '%s'" nm.Value

            let eqType = GetActualType child.Type r
            let! newValue = loopAsn1Value s eqType chv
            return ((nm,loc),newValue)
        }

    and loopConstraint (s:Scope) (t:Asn1Type) (checContent:CheckContext) (c:Asn1Constraint) =
        let vtype =
            match checContent with
            | CheckSize         -> sizeIntegerType
            | CheckCharacter    -> stringType
            | CheckContent      -> t                 

        match c with
        | SingleValueContraint v        ->
            cont {
                let! actType = loopType s t
                let! newValue = loopAsn1Value s vtype v
                return singleValueContraintFunc s t checContent actType newValue
            }
        | RangeContraint(v1,v2,b1,b2)   -> 
            cont {
                let! actType = loopType s t
                let! newValue1 = loopAsn1Value s vtype v1
                let! newValue2 = loopAsn1Value s vtype v2
                return rangeContraintFunc s t checContent actType newValue1 newValue2 b1 b2
            }
        | RangeContraint_val_MAX (v,b)  ->
            cont {
                let! actType = loopType s t
                let! newValue = loopAsn1Value s vtype v
                return greaterThanContraintFunc s t checContent actType newValue  b
            }
        | RangeContraint_MIN_val (v,b)  ->
            cont {
                let! actType = loopType s t
                let! newValue = loopAsn1Value s vtype v
                return lessThanContraintFunc s t checContent actType newValue  b
            }
        | RangeContraint_MIN_MAX             -> 
            cont {
                let! actType = loopType s t
                return alwaysTtrueContraintFunc s t checContent actType 
            }
        | TypeInclusionConstraint (md,tas)  ->
            cont {
                let! actType = loopType s t
                return typeInclConstraintFunc s t actType (md,tas)
            }
        | UnionConstraint (c1,c2,v)      ->
            cont {
                let! actType = loopType s t
                let! nc1 = loopConstraint s t checContent c1
                let! nc2 = loopConstraint s t checContent c2
                return unionConstraintFunc s t actType nc1 nc2
            }
        | IntersectionConstraint(c1,c2)         ->
            cont {
                let! actType = loopType s t
                let! nc1 = loopConstraint s t checContent c1
                let! nc2 = loopConstraint s t checContent c2
                return intersectionConstraintFunc s t actType nc1 nc2
            }
        | AllExceptConstraint c ->
            cont {
                let! actType = loopType s t
                let! nc = loopConstraint s t checContent c
                return notConstraintFunc s t actType nc
            }
        | ExceptConstraint (c1,c2)  ->
            cont {
                let! actType = loopType s t
                let! nc1 = loopConstraint s t checContent c1
                let! nc2 = loopConstraint s t checContent c2
                return exceptConstraintFunc s t actType nc1 nc2
            }
        | RootConstraint c  ->
            cont {
                let! actType = loopType s t
                let! nc = loopConstraint s t checContent c
                return rootConstraintFunc s t actType nc 
            }
        | RootConstraint2 (c1,c2)  ->
            cont {
                let! actType = loopType s t
                let! nc1 = loopConstraint s t checContent c1
                let! nc2 = loopConstraint s t checContent c2
                return root2ConstraintFunc s t actType nc1 nc2
            }

        | SizeContraint(sc)         -> loopConstraint s t CheckSize sc

        | AlphabetContraint c       -> loopConstraint s t CheckCharacter c

        | WithComponentConstraint _          -> raise(BugErrorException "This constraint should have been removed")
        | WithComponentsConstraint _         -> raise(BugErrorException "This constraint should have been removed")
                

    loopAstRoot r id 
