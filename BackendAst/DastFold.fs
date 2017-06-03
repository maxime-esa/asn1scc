module DastFold

open System
open System.Numerics
open DAst

let foldMap = GenericFold2.foldMap

let foldAsn1Type
    (t:Asn1Type) 
    (us:'UserState) 
    integerFunc 
    intConstructor 
    realFunc
    realConstructor 
    ia5StringFunc
    ia5StringConstructor
    octetStringFunc
    octetStringConstructor
    nullTypeFunc
    nullTypeConstructor
    bitStringFunc
    bitStringConstructor
    booleanFunc
    booleanConstructor
    enumeratedFunc
    enumeratedConstructor
    seqOfTypeFunc
    seqOfTypeConstructor 
    seqChild
    seqTypeFunc
    seqTypeConstructor 
    chChild
    chTypeFunc
    chTypeConstructor
    =
    let rec loopType (t:Asn1Type) (us:'UserState) =
        let rec loopGenType (cnt:'Type)  geBaseTypeFunc func (us:'UserState) =
            match geBaseTypeFunc cnt with
            | Some baseCnt  ->
                let newBaseIntType, newState = loopGenType baseCnt  geBaseTypeFunc func us
                let newType, finalState = func cnt (Some newBaseIntType) newState
                newType, finalState
            | None  ->
                func cnt None us

        match t with
        | Integer           cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) integerFunc us
            intConstructor newType, newState
        | Real              cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) realFunc us
            realConstructor newType, newState
        | IA5String         cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) ia5StringFunc us
            ia5StringConstructor newType, newState
        | OctetString       cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) octetStringFunc us
            octetStringConstructor newType, newState
        | NullType          cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) nullTypeFunc us
            nullTypeConstructor newType, newState
        | BitString         cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) bitStringFunc us
            bitStringConstructor newType, newState
        | Boolean           cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) booleanFunc us
            booleanConstructor newType, newState
        | Enumerated        cnt -> 
            let newType, newState = loopGenType cnt (fun x -> x.baseType) enumeratedFunc us
            enumeratedConstructor newType, newState
        | SequenceOf        cnt -> 
            let newChildType, newState = loopType cnt.childType us
            let newType, newState = loopGenType cnt (fun x -> x.baseType) (seqOfTypeFunc newChildType) newState
            seqOfTypeConstructor newType, newState
        | Sequence          cnt -> 
            let newChildren, newState = 
                cnt.children |> 
                foldMap (fun curState ch -> 
                    let newChilType, newSate = loopType ch.chType  curState
                    seqChild ch newChilType newSate) us
            let newType, newState = loopGenType cnt (fun x -> x.baseType) (seqTypeFunc newChildren) newState
            seqTypeConstructor newType, newState
        | Choice            cnt -> 
            let newChildren, newState = 
                cnt.children |> 
                foldMap (fun curState ch -> 
                    let newChilType, newSate = loopType ch.chType  curState
                    chChild ch newChilType newSate) us
            let newType, newState = loopGenType cnt (fun x -> x.baseType) (chTypeFunc newChildren) newState
            chTypeConstructor newType, newState
    loopType t us

    

let foldAsn1Type2
    (t:Asn1Type) 
    (us:'UserState) 
    integerFunc 
    realFunc
    ia5StringFunc
    octetStringFunc
    nullTypeFunc
    bitStringFunc
    booleanFunc
    enumeratedFunc
    seqOfTypeFunc
    seqChild
    seqTypeFunc
    chChild
    chTypeFunc
    =
    foldAsn1Type 
        t
        us
        integerFunc 
        id 
        realFunc
        id
        ia5StringFunc
        id
        octetStringFunc
        id
        nullTypeFunc
        id
        bitStringFunc
        id
        booleanFunc
        id
        enumeratedFunc
        id
        seqOfTypeFunc
        id
        seqChild
        seqTypeFunc
        id
        chChild
        chTypeFunc
        id


