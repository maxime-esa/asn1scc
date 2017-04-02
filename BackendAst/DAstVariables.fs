module DAstVariables

open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst
open uPER2



let getValueByUperRange (r:uperRange<'T>) (z:'T) = 
    match r with
    | Concrete (a,b)    -> if a <= z && z <= b then z else a
    | NegInf  b         -> if z <= b then z else b              //(-inf, b]
    | PosInf a          -> if a <= z then z else a               //[a, +inf)
    | Full              -> z

let getDefaultValueByType  (t:Asn1Type)  =
    DastFold.foldAsn1Type2
        t
        false
        (fun o newBase us -> 
            let v = getValueByUperRange o.uperRange 0I
            IntegerValue ({IntegerValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = v; }), true)

        (fun o newBase us -> 
            let v = getValueByUperRange o.uperRange 0.0
            RealValue ({RealValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = v; }), true)

        (fun o newBase us -> 
            let ch = 
                match o.charSet |> Seq.exists((=) ' ') with
                | true  -> ' '
                | false -> o.charSet |> Seq.find(fun c -> not (Char.IsControl c))
            let v = System.String(ch, o.minSize)
            StringValue ({StringValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = v; }), true)

        (fun o newBase us -> 
            let v = [1 .. o.minSize] |> List.map(fun i -> 0uy)
            OctetStringValue ({OctetStringValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = v; }), true)
        
        (fun o newBase us -> 
            NullValue ({NullValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = (); }), true)
        
        (fun o newBase us -> 
            let v = System.String('0', o.minSize)
            BitStringValue ({BitStringValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = v; }), true)
        
        (fun o newBase us -> BooleanValue ({BooleanValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = false; }), true)

        (fun o newBase us -> EnumValue ({EnumValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = o.items.Head.name; }), true)

        (fun childType o newBase us -> 
            let v = [1 .. o.minSize] |> List.map(fun i -> childType)
            SeqOfValue ({SeqOfValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = v; }), true)

        //sequence
        (fun o newChild us -> {NamedValue.name = o.name; Value=newChild}, us)
        (fun children o newBase us -> SeqValue ({SeqValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = children; }), true)

        //Choice
        (fun o newChild us -> {NamedValue.name = o.name; Value=newChild}, us)
        (fun children o newBase us -> ChValue ({ChValue.id = (ReferenceToValue (o.id.ToScopeNodeList, [GenericFold2.IMG 0])); litOrRef=Literal; childValue = us; refToType = o.id; Value = children.Head; }), true)
    |> fst

let rec printValue (r:DAst.AstRoot) (l:ProgrammingLanguage) (pu:ProgramUnit) (gv:Asn1GenericValue) =
    match l with
    | C ->
        match gv with
        | IntegerValue      v -> variables_c.PrintIntValue v.Value
        | RealValue         v -> variables_c.PrintRealValue v.Value
        | StringValue       v -> variables_c.PrintStringValue v.Value
        | BooleanValue      v -> variables_c.PrintBooleanValue v.Value
        | BitStringValue    v -> 
            let bytes = bitStringValueToByteArray (StringLoc.ByValue v.Value)
            match DAst.getValueType r gv with
            | OctetString os    -> variables_c.PrintBitOrOctetStringValue (os.minSize = os.maxSize) bytes (BigInteger bytes.Length)
            | BitString   bs    -> variables_c.PrintBitOrOctetStringValue (bs.minSize = bs.maxSize) bytes (BigInteger bytes.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | OctetStringValue  v -> 
            match DAst.getValueType r gv with
            | OctetString os    -> variables_c.PrintBitOrOctetStringValue (os.minSize = os.maxSize) v.Value (BigInteger v.Value.Length)
            | BitString   bs    -> variables_c.PrintBitOrOctetStringValue (bs.minSize = bs.maxSize) v.Value (BigInteger v.Value.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | EnumValue         v -> 
            match DAst.getValueType r gv with
            | Enumerated enm    -> 
                let itm = enm.items |> Seq.find(fun x -> x.name = v.Value)
                variables_c.PrintEnumValue (itm.getBackendName l)
            | _         -> raise(BugErrorException "unexpected type")
        | NullValue         v -> variables_c.PrintNullValue ()
        | SeqOfValue        v -> 
            match DAst.getValueType r gv with
            | SequenceOf so -> 
                let childVals = v.Value |> List.map (printValue r l pu)
                variables_c.PrintSequenceOfValue (so.minSize = so.maxSize) childVals
            | _         -> raise(BugErrorException "unexpected type")
        | SeqValue          v -> 
            match DAst.getValueType r gv with
            | Sequence s -> 
                let optChildren = 
                    s.children |>
                    List.filter(fun x -> x.optionality.IsSome) |>
                    List.map(fun x ->
                        match v.Value |> Seq.tryFind(fun chv -> chv.name = x.name) with
                        | Some _    -> variables_c.PrintSequenceValue_child_exists x.c_name "1"
                        | None      -> variables_c.PrintSequenceValue_child_exists x.c_name "0")
                let arrChildren = 
                    s.children |>
                    List.filter(fun x -> not x.acnInsertetField) |>
                    List.choose(fun x -> 
                        match v.Value |> Seq.tryFind(fun chv -> chv.name = x.name) with
                        | Some v    -> Some (variables_c.PrintSequenceValueChild x.c_name (printValue r l pu v.Value))
                        | None      -> 
                            match x.optionality with
                            | Some(CAst.Optional opt)    -> 
                                match opt.defaultValue with
                                | Some v    -> Some (variables_c.PrintSequenceValueChild x.c_name (printValue r l pu v))                    
                                | None      -> None
                            | _             -> None)
                variables_c.PrintSequenceValue arrChildren optChildren
            | _         -> raise(BugErrorException "unexpected type")

        | ChValue           v -> 
            match DAst.getValueType r gv with
            | Choice s -> 
                s.children |>
                List.filter(fun x -> x.name = v.Value.name)  |>
                List.map(fun x -> variables_c.PrintChoiceValue x.presentWhenName x.c_name (printValue r l pu v.Value.Value)) |>
                List.head
            | _         -> raise(BugErrorException "unexpected type")

    | Ada ->
        match gv with
        | IntegerValue      v -> variables_a.PrintIntValue v.Value
        | RealValue         v -> variables_a.PrintRealValue v.Value
        | StringValue       v -> 
            match DAst.getValueType r gv with
            | IA5String st  ->
                let arrNuls = [0 .. (st.maxSize- v.Value.Length)]|>Seq.map(fun x -> variables_a.PrintStringValueNull())
                variables_a.PrintStringValue (v.Value.Replace("\"","\"\"")) arrNuls
            | _             -> raise(BugErrorException "unexpected type")
        | BooleanValue      v -> variables_a.PrintBooleanValue v.Value
        | BitStringValue    v -> 
            match DAst.getValueType r gv with
            | OctetString os    -> 
                let typeDefName  = if gv.childValue then os.typeDefinition.typeDefinitionBodyWithinSeq else os.typeDefinition.name
                let bytes = bitStringValueToByteArray (StringLoc.ByValue v.Value)
                variables_a.PrintOctetStringValue typeDefName (os.minSize = os.maxSize) bytes (BigInteger bytes.Length)
            | BitString   bs    -> 
                let typeDefName  = if gv.childValue then bs.typeDefinition.typeDefinitionBodyWithinSeq else bs.typeDefinition.name
                let arBits = v.Value.ToCharArray() |> Array.map(fun x -> x.ToString())
                variables_a.PrintBitStringValue typeDefName (bs.minSize = bs.maxSize) arBits (BigInteger arBits.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | OctetStringValue  v -> 
            match DAst.getValueType r gv with
            | OctetString os    -> 
                let typeDefName  = if gv.childValue then os.typeDefinition.typeDefinitionBodyWithinSeq else os.typeDefinition.name
                variables_a.PrintOctetStringValue typeDefName (os.minSize = os.maxSize) v.Value (BigInteger v.Value.Length)
            | BitString   bs    -> 
                let typeDefName  = if gv.childValue then bs.typeDefinition.typeDefinitionBodyWithinSeq else bs.typeDefinition.name
                let bittring = byteArrayToBitStringValue v.Value
                let arBits = bittring.ToCharArray() |> Array.map(fun x -> x.ToString()) 
                let maxLen = if (arBits.Length > bs.maxSize) then (bs.maxSize-1) else (arBits.Length-1)
                let arBits = arBits.[0..maxLen]
                variables_a.PrintBitStringValue typeDefName (bs.minSize = bs.maxSize) arBits (BigInteger arBits.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | EnumValue         v -> 
            match DAst.getValueType r gv with
            | Enumerated enm    -> 
                let itm = enm.items |> Seq.find(fun x -> x.name = v.Value)
                variables_a.PrintEnumValue (itm.getBackendName l)
            | _         -> raise(BugErrorException "unexpected type")
        | NullValue         v -> variables_a.PrintNullValue ()
        | SeqOfValue        v -> 
            match DAst.getValueType r gv with
            | SequenceOf so -> 
                let typeDefName  = if gv.childValue then so.typeDefinition.typeDefinitionBodyWithinSeq else so.typeDefinition.name
                let childVals = v.Value |> List.map (printValue r l pu)
                let sDefValue = printValue r l pu (getDefaultValueByType so.childType)
                variables_a.PrintSequenceOfValue typeDefName (so.minSize = so.maxSize) (BigInteger v.Value.Length) childVals sDefValue
            | _         -> raise(BugErrorException "unexpected type")

        | SeqValue          v -> 
            match DAst.getValueType r gv with
            | Sequence s -> 
                let typeDefName  = if gv.childValue then s.typeDefinition.typeDefinitionBodyWithinSeq else s.typeDefinition.name
                let optChildren = 
                    s.children |>
                    List.filter(fun x -> x.optionality.IsSome) |>
                    List.map(fun x ->
                        match v.Value |> Seq.tryFind(fun chv -> chv.name = x.name) with
                        | Some _    -> variables_a.PrintSequenceValue_child_exists x.c_name "1"
                        | None      -> variables_a.PrintSequenceValue_child_exists x.c_name "0")
                let arrChildren = 
                    s.children |>
                    List.filter(fun x -> not x.acnInsertetField) |>
                    List.map(fun x -> 
                        match v.Value |> Seq.tryFind(fun chv -> chv.name = x.name) with
                        | Some v    -> variables_a.PrintSequenceValueChild x.c_name (printValue r l pu v.Value)
                        | None      -> 
                            let chV = 
                                match x.optionality with
                                | Some(CAst.Optional opt)    -> 
                                    match opt.defaultValue with
                                    | Some v    -> v
                                    | None      -> getDefaultValueByType x.chType
                                | _             -> getDefaultValueByType x.chType
                            variables_a.PrintSequenceValueChild x.c_name (printValue r l pu chV) )
                let allChildren = match Seq.isEmpty optChildren with
                                  | true     -> arrChildren
                                  | false    -> arrChildren @ [variables_a.PrintSequenceValue_Exists typeDefName optChildren]
                variables_a.PrintSequenceValue typeDefName allChildren
            | _         -> raise(BugErrorException "unexpected type")
        | ChValue           v -> 
            match DAst.getValueType r gv with
            | Choice s -> 
                let typeDefName  = if gv.childValue then s.typeDefinition.typeDefinitionBodyWithinSeq else s.typeDefinition.name
                s.children |>
                List.filter(fun x -> x.name = v.Value.name)  |>
                List.map(fun x -> variables_a.PrintChoiceValue typeDefName x.c_name (printValue r l pu v.Value.Value) x.presentWhenName) |>
                List.head
            | _         -> raise(BugErrorException "unexpected type")

