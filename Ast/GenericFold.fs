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
            let! asn1Type = loopType r f m tas.Type
            return tasFunc r f m tas asn1Type
        }
    and loopValueAssignments (r:AstRoot) (f:Asn1File) (m:Asn1Module) (vas:ValueAssignment) =
        cont {
            let actType = GetActualType vas.Type  r
            let! asn1Type = loopType r f m vas.Type
            let! asn1Value = loopAsn1Value r f m actType vas.Value
            return vasFunc r f m vas asn1Type asn1Value
        }
    and loopType (r:AstRoot) (f:Asn1File) (m:Asn1Module) (t:Asn1Type) =
        cont {
            match t.Kind with
            | ReferenceType (mdName,tasName, argList) ->
                let eqType = GetActualType t r 
                let! refCons = t.Constraints |> mmap  (loopConstraint r f m eqType CheckContent)
                let! newActType = loopType r f m eqType 
                return refTypeFunc r f m mdName.Value tasName.Value newActType refCons
            | Integer 
            | Real    
            | IA5String 
            | NumericString 
            | OctetString 
            | NullType 
            | BitString 
            | Boolean           ->
                let! newCons = t.Constraints |> mmap  (loopConstraint r f m t CheckContent)
                return baseTypeFunc r f m t newCons            
            | Enumerated (enmItems) ->  
                let! newCons = t.Constraints |> mmap  (loopConstraint r f m t CheckContent)
                let! newEnmItems = enmItems |> mmap (loopNamedItem r f m)
                // to do : values in new named items should be resolved and always present
                // plus a flag in the enum type whether values where provided by user or not/
                return enmItemFunc r f m t newEnmItems newCons            
            | SequenceOf (innerType)  ->
                let! newCons = t.Constraints |> mmap  (loopConstraint r f m t CheckContent)
                let! newInnerType = loopType r f m  innerType
                return seqOfTypeFunc r f m t  newInnerType newCons
            | Sequence (children)     ->
                let! newCons = t.Constraints |> mmap  (loopConstraint r f m t CheckContent)
                let! newChildren = children |> mmap  (loopSequenceChild r f m )
                return seqTypeFunc r f m t newChildren newCons
            | Choice (children)       ->
                let! newCons = t.Constraints |> mmap  (loopConstraint r f m t CheckContent)
                let! newChildren = children |> mmap  (loopChoiceChild r f m )
                return chTypeFunc r f m t newChildren newCons
        }

   
    and loopNamedItem (r:AstRoot) (f:Asn1File) (m:Asn1Module) (ni:NamedItem) =
        cont {
            match ni._value with
            | Some v    ->
                let! newValue = loopAsn1Value r f m enumIntegerType v
                return (ni.Name, ni.Comments, Some newValue)
            | None      ->
                return (ni.Name, ni.Comments, None)
        }
    and loopSequenceChild (r:AstRoot) (f:Asn1File) (m:Asn1Module)  (chInfo:ChildInfo) =
        cont {
            let! newType = loopType r f m  chInfo.Type
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
                        let! newValue = loopAsn1Value r f m eqType vl
                        return Some newValue
                }
            return sequenceChildFunc r f m chInfo newType newDefValue
        }

    and loopChoiceChild (r:AstRoot) (f:Asn1File) (m:Asn1Module) (chInfo:ChildInfo) =
        cont {
            let! newType = loopType r f m  chInfo.Type
            return choiceChildFunc r f m   chInfo newType
        }
    and loopAsn1Value (r:AstRoot) (f:Asn1File) (m:Asn1Module) (t:Asn1Type) (v:Asn1Value) =
        match v.Kind, t.Kind with
        | RefValue (md,vas), Enumerated (enmItems)   ->
                match enmItems |> Seq.tryFind (fun x -> x.Name.Value = vas.Value) with
                | Some enmItem    ->
                    cont {
                        let! actType = loopType r f m t
                        let! ni = loopNamedItem r f m enmItem
                        return enumValueFunc r f m t actType enmItem  ni          
                    }
                | None          ->
                    cont {
                        let actValue = GetActualValue md vas r
                        let! newActVal = loopAsn1Value r f m t actValue
                        return refValueFunc r f m t (md.Value, vas.Value) newActVal            
                    }
        | RefValue (md,vas), _   ->
                cont {
                    let actValue = GetActualValue md vas r
                    let! newActVal = loopAsn1Value r f m t actValue
                    return refValueFunc r f m t (md.Value, vas.Value) newActVal            
                }
        | IntegerValue bi, Integer          ->
            cont {
                let! actType = loopType r f m t
                return intValFunc r f m t actType bi.Value
            }
        | IntegerValue bi, Real  _           ->
            cont {
                let! actType = loopType r f m t
                let dc:double = (double)bi.Value
                return realValFunc r f m t actType dc
            }
        | RealValue dc , Real   _                  -> 
            cont {
                let! actType = loopType r f m t
                return realValFunc r f m t actType dc.Value
            }
        | StringValue s, IA5String _   -> 
            cont {
                let! actType = loopType r f m t
                return ia5StringValFunc r f m t actType s.Value
            }
        | StringValue s , NumericString _   -> 
            cont {
                let! actType = loopType r f m t
                return numStringValFunc r f m t actType s.Value
            }
        | BooleanValue b, Boolean _       ->
            cont {
                let! actType = loopType r f m t
                return boolValFunc r f m t actType b.Value
            }
        | OctetStringValue b, OctetString _         ->
            cont {
                let! actType = loopType r f m t
                return octetStringValueFunc r f m t actType b
            }
        | OctetStringValue b, BitString _        ->
            cont {
                let! actType = loopType r f m t
                return octetStringValueFunc r f m t actType b
            }
        | BitStringValue b, BitString _           ->
            cont {
                let! actType = loopType r f m t
                return bitStringValueFunc r f m t actType b 
            }
        | NullValue , NullType _   ->
            cont {
                let! actType = loopType r f m t
                return nullValueFunc r f m t actType             
            }
        | SeqOfValue  vals, SequenceOf chType    ->
            cont {
                let! actType = loopType r f m t
                let eqType = GetActualType chType r
                let! newVals = vals |> mmap  (loopAsn1Value r f m eqType)
                return seqOfValueFunc r f m t actType  newVals
            }
        | SeqValue    namedValues, Sequence children ->
            cont {
                let! actType = loopType r f m t
                let! newValues =  namedValues |> mmap  (loopSeqValueChild r f m  children )
                return seqValueFunc r f m t actType newValues
            }
        | ChValue (name,vl), Choice children         ->
            match children |> Seq.tryFind(fun ch -> ch.Name.Value = name.Value) with
            | Some chType   ->
                cont {
                    let! actType = loopType r f m t
                    let eqType = GetActualType chType.Type r 
                    let! newValue = loopAsn1Value r f m eqType vl
                    return chValueFunc r f m t actType name newValue
                }
            | None  -> 
                error name.Location "Invalid alternative name '%s'" name.Value
        | _         ->
            error v.Location "Invalid combination ASN.1 type and ASN.1 value"


    and loopSeqValueChild (r:AstRoot) (f:Asn1File) (m:Asn1Module)  (children: list<ChildInfo>) (nm:StringLoc, chv:Asn1Value) = 
        cont {
            let child = 
                match children |> Seq.tryFind (fun ch -> ch.Name.Value = nm.Value) with
                | Some ch -> ch
                | None    -> error nm.Location "Invalid child name '%s'" nm.Value

            let eqType = GetActualType child.Type r
            let! newValue = loopAsn1Value r f m eqType chv
            return ((nm,loc),newValue)
        }

    and loopConstraint (r:AstRoot) (f:Asn1File) (m:Asn1Module) (t:Asn1Type) (checContent:CheckContext) (c:Asn1Constraint) =
        let vtype =
            match checContent with
            | CheckSize         -> sizeIntegerType
            | CheckCharacter    -> stringType
            | CheckContent      -> t                 

        match c with
        | SingleValueContraint v        ->
            cont {
                let! actType = loopType r f m t
                let! newValue = loopAsn1Value r f m vtype v
                return singleValueContraintFunc r f m t checContent actType newValue
            }
        | RangeContraint(v1,v2,b1,b2)   -> 
            cont {
                let! actType = loopType r f m t
                let! newValue1 = loopAsn1Value r f m vtype v1
                let! newValue2 = loopAsn1Value r f m vtype v2
                return rangeContraintFunc r f m t checContent actType newValue1 newValue2 b1 b2
            }
        | RangeContraint_val_MAX (v,b)  ->
            cont {
                let! actType = loopType r f m t
                let! newValue = loopAsn1Value r f m vtype v
                return greaterThanContraintFunc r f m t checContent actType newValue  b
            }
        | RangeContraint_MIN_val (v,b)  ->
            cont {
                let! actType = loopType r f m t
                let! newValue = loopAsn1Value r f m vtype v
                return lessThanContraintFunc r f m t checContent actType newValue  b
            }
        | RangeContraint_MIN_MAX             -> 
            cont {
                let! actType = loopType r f m t
                return alwaysTtrueContraintFunc r f m t checContent actType 
            }
        | TypeInclusionConstraint (md,tas)  ->
            cont {
                let! actType = loopType r f m t
                return typeInclConstraintFunc r f m t actType (md,tas)
            }
        | UnionConstraint (c1,c2,v)      ->
            cont {
                let! actType = loopType r f m t
                let! nc1 = loopConstraint r f m t checContent c1
                let! nc2 = loopConstraint r f m t checContent c2
                return unionConstraintFunc r f m t actType nc1 nc2
            }
        | IntersectionConstraint(c1,c2)         ->
            cont {
                let! actType = loopType r f m t
                let! nc1 = loopConstraint r f m t checContent c1
                let! nc2 = loopConstraint r f m t checContent c2
                return intersectionConstraintFunc r f m t actType nc1 nc2
            }
        | AllExceptConstraint c ->
            cont {
                let! actType = loopType r f m t
                let! nc = loopConstraint r f m t checContent c
                return notConstraintFunc r f m t actType nc
            }
        | ExceptConstraint (c1,c2)  ->
            cont {
                let! actType = loopType r f m t
                let! nc1 = loopConstraint r f m t checContent c1
                let! nc2 = loopConstraint r f m t checContent c2
                return exceptConstraintFunc r f m t actType nc1 nc2
            }
        | RootConstraint c  ->
            cont {
                let! actType = loopType r f m t
                let! nc = loopConstraint r f m t checContent c
                return rootConstraintFunc r f m t actType nc 
            }
        | RootConstraint2 (c1,c2)  ->
            cont {
                let! actType = loopType r f m t
                let! nc1 = loopConstraint r f m t checContent c1
                let! nc2 = loopConstraint r f m t checContent c2
                return root2ConstraintFunc r f m t actType nc1 nc2
            }

        | SizeContraint(sc)         -> loopConstraint r f m t CheckSize sc

        | AlphabetContraint c       -> loopConstraint r f m t CheckCharacter c

        | WithComponentConstraint _          -> raise(BugErrorException "This constraint should have been removed")
        | WithComponentsConstraint _         -> raise(BugErrorException "This constraint should have been removed")
                

    loopAstRoot r id 
