module DAstVariables

open System
open System.Numerics
open System.IO

open FsUtils
open CommonTypes
open DAst
open DAstUtilFunctions



let getDefaultValueByType  (t:Asn1Type)  =  t.initialValue

let rec printValue (r:DAst.AstRoot) (l:ProgrammingLanguage) (pu:ProgramUnit) (t:Asn1Type) (parentValue:Asn1GenericValue option) (gv:Asn1GenericValue) =
    match l with
    | C ->
        match gv with
        | IntegerValue      v -> variables_c.PrintIntValue v
        | RealValue         v -> variables_c.PrintRealValue v
        | StringValue       v -> variables_c.PrintStringValue v
        | BooleanValue      v -> variables_c.PrintBooleanValue v
        | BitStringValue    v -> 
            let bytes = bitStringValueToByteArray (StringLoc.ByValue v)
            match t.ActualType.Kind with
            | OctetString os    -> variables_c.PrintBitOrOctetStringValue (os.baseInfo.minSize = os.baseInfo.maxSize) bytes (BigInteger bytes.Length)
            | BitString   bs    -> variables_c.PrintBitOrOctetStringValue (bs.baseInfo.minSize = bs.baseInfo.maxSize) bytes (BigInteger bytes.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | OctetStringValue  v -> 
            match t.ActualType.Kind with
            | OctetString os    -> variables_c.PrintBitOrOctetStringValue (os.baseInfo.minSize = os.baseInfo.maxSize) v (BigInteger v.Length)
            | BitString   bs    -> variables_c.PrintBitOrOctetStringValue (bs.baseInfo.minSize = bs.baseInfo.maxSize) v (BigInteger v.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | EnumValue         v -> 
            match t.ActualType.Kind with
            | Enumerated enm    -> 
                let itm = enm.baseInfo.items |> Seq.find(fun x -> x.Name.Value = v)
                variables_c.PrintEnumValue (itm.getBackendName l)
            | _         -> raise(BugErrorException "unexpected type")
        | NullValue         v -> variables_c.PrintNullValue ()
        | SeqOfValue        v -> 
            match t.ActualType.Kind with
            | SequenceOf so -> 
                let childVals = v |> List.map (printValue r l pu so.childType (Some gv))
                variables_c.PrintSequenceOfValue (so.baseInfo.minSize = so.baseInfo.maxSize) childVals
            | _         -> raise(BugErrorException "unexpected type")
        | SeqValue          v -> 
            match t.ActualType.Kind with
            | Sequence s -> 
                let optChildren = 
                    s.children |>
                    List.choose(fun ch -> match ch with Asn1Child a -> Some a | AcnChild _ -> None) |>
                    List.filter(fun ch -> ch.Optionality.IsSome) |>
                    List.map(fun x ->
                        match v |> Seq.tryFind(fun chv -> chv.name.Value = x.Name.Value) with
                        | Some _    -> variables_c.PrintSequenceValue_child_exists x.c_name "1"
                        | None      -> variables_c.PrintSequenceValue_child_exists x.c_name "0")
                let arrChildren = 
                    s.children |>
                    List.choose(fun ch -> match ch with Asn1Child a -> Some a | AcnChild _ -> None) |>
                    List.choose(fun cht -> 
                        match v |> Seq.tryFind(fun chv -> chv.name.Value = cht.Name.Value) with
                        | Some v    -> Some (variables_c.PrintSequenceValueChild cht.c_name (printValue r l pu cht.Type (Some gv) v.Value))
                        | None      -> 
                            match cht.Optionality with
                            | Some(Asn1AcnAst.Optional opt)    -> 
                                match opt.defaultValue with
                                | Some v    -> Some (variables_c.PrintSequenceValueChild cht.c_name (printValue r l pu cht.Type (Some gv) (mapValue v)))                    
                                | None      -> None
                            | _             -> None)
                variables_c.PrintSequenceValue arrChildren optChildren
            | _         -> raise(BugErrorException "unexpected type")

        | ChValue           v -> 
            match t.ActualType.Kind with
            | Choice s -> 
                s.children |>
                List.filter(fun x -> x.Name.Value = v.name.Value)  |>
                List.map(fun x -> variables_c.PrintChoiceValue x.presentWhenName x.c_name (printValue r l pu x.chType (Some gv) v.Value)) |>
                List.head
            | _         -> raise(BugErrorException "unexpected type")
        | RefValue ((md,vs),v)         ->
            let vas = r.getValueAssignmentByName md.Value vs.Value
            vas.c_name
    | Ada ->
        match gv with
        | IntegerValue      v -> variables_a.PrintIntValue v
        | RealValue         v -> variables_a.PrintRealValue v
        | StringValue       v -> 
            match t.ActualType.Kind with
            | IA5String st  ->
                let arrNuls = [0 .. (st.baseInfo.maxSize- v.Length)]|>Seq.map(fun x -> variables_a.PrintStringValueNull())
                variables_a.PrintStringValue (v.Replace("\"","\"\"")) arrNuls
            | _             -> raise(BugErrorException "unexpected type")
        | BooleanValue      v -> variables_a.PrintBooleanValue v
        | BitStringValue    v -> 
            match t.ActualType.Kind with
            | OctetString os    -> 
                let typeDefName  = if parentValue.IsSome then os.typeDefinition.typeDefinitionBodyWithinSeq else os.typeDefinition.name
                let bytes = bitStringValueToByteArray (StringLoc.ByValue v)
                variables_a.PrintOctetStringValue typeDefName (os.baseInfo.minSize = os.baseInfo.maxSize) bytes (BigInteger bytes.Length)
            | BitString   bs    -> 
                let typeDefName  = if parentValue.IsSome then bs.typeDefinition.typeDefinitionBodyWithinSeq else bs.typeDefinition.name
                let arBits = v.ToCharArray() |> Array.map(fun x -> x.ToString())
                variables_a.PrintBitStringValue typeDefName (bs.baseInfo.minSize = bs.baseInfo.maxSize) arBits (BigInteger arBits.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | OctetStringValue  v -> 
            match t.ActualType.Kind with
            | OctetString os    -> 
                let typeDefName  = if parentValue.IsSome then os.typeDefinition.typeDefinitionBodyWithinSeq else os.typeDefinition.name
                variables_a.PrintOctetStringValue typeDefName (os.baseInfo.minSize = os.baseInfo.maxSize) v (BigInteger v.Length)
            | BitString   bs    -> 
                let typeDefName  = if parentValue.IsSome then bs.typeDefinition.typeDefinitionBodyWithinSeq else bs.typeDefinition.name
                let bittring = byteArrayToBitStringValue v
                let arBits = bittring.ToCharArray() |> Array.map(fun x -> x.ToString()) 
                let maxLen = if (arBits.Length > bs.baseInfo.maxSize) then (bs.baseInfo.maxSize-1) else (arBits.Length-1)
                let arBits = arBits.[0..maxLen]
                variables_a.PrintBitStringValue typeDefName (bs.baseInfo.minSize = bs.baseInfo.maxSize) arBits (BigInteger arBits.Length)
            | _         -> raise(BugErrorException "unexpected type")
        | EnumValue         v -> 
            match t.ActualType.Kind with
            | Enumerated enm    -> 
                let itm = enm.baseInfo.items |> Seq.find(fun x -> x.Name.Value = v)
                variables_a.PrintEnumValue (itm.getBackendName l)
            | _         -> raise(BugErrorException "unexpected type")
        | NullValue         v -> variables_a.PrintNullValue ()
        | SeqOfValue        v -> 
            match t.ActualType.Kind with
            | SequenceOf so -> 
                let typeDefName  = if parentValue.IsSome then so.typeDefinition.typeDefinitionBodyWithinSeq else so.typeDefinition.name
                let childVals = v |> List.map (printValue r l pu so.childType (Some gv))
                let sDefValue = printValue r l pu t None (getDefaultValueByType so.childType)
                variables_a.PrintSequenceOfValue typeDefName (so.baseInfo.minSize = so.baseInfo.maxSize) (BigInteger v.Length) childVals sDefValue
            | _         -> raise(BugErrorException "unexpected type")

        | SeqValue          v -> 
            match t.ActualType.Kind with
            | Sequence s -> 
                let typeDefName  = if parentValue.IsSome then s.typeDefinition.typeDefinitionBodyWithinSeq else s.typeDefinition.name
                let optChildren = 
                    s.children |>
                    List.choose(fun ch -> match ch with Asn1Child a -> Some a | AcnChild _ -> None) |>
                    List.filter(fun ch -> ch.Optionality.IsSome) |>
                    List.map(fun x ->
                        match v |> Seq.tryFind(fun chv -> chv.name.Value = x.Name.Value) with
                        | Some _    -> variables_a.PrintSequenceValue_child_exists x.c_name "1"
                        | None      -> variables_a.PrintSequenceValue_child_exists x.c_name "0")
                let arrChildren = 
                    s.children |>
                    List.choose(fun ch -> match ch with Asn1Child a -> Some a | AcnChild _ -> None) |>
                    List.map(fun x -> 
                        match v |> Seq.tryFind(fun chv -> chv.name.Value = x.Name.Value) with
                        | Some v    -> variables_a.PrintSequenceValueChild x.c_name (printValue r l pu x.Type (Some gv) v.Value)
                        | None      -> 
                            let chV = 
                                match x.Optionality with
                                | Some(Asn1AcnAst.Optional opt)    -> 
                                    match opt.defaultValue with
                                    | Some v    -> mapValue v
                                    | None      -> getDefaultValueByType x.Type
                                | _             -> getDefaultValueByType x.Type
                            variables_a.PrintSequenceValueChild x.c_name (printValue r l pu x.Type None chV) )
                let allChildren = match Seq.isEmpty optChildren with
                                  | true     -> arrChildren
                                  | false    -> arrChildren @ [variables_a.PrintSequenceValue_Exists typeDefName optChildren]
                variables_a.PrintSequenceValue typeDefName allChildren
            | _         -> raise(BugErrorException "unexpected type")
        | ChValue           v -> 
            match t.ActualType.Kind with
            | Choice s -> 
                let typeDefName  = if parentValue.IsSome then s.typeDefinition.typeDefinitionBodyWithinSeq else s.typeDefinition.name
                s.children |>
                List.filter(fun x -> x.Name.Value = v.name.Value)  |>
                List.map(fun x -> variables_a.PrintChoiceValue typeDefName x.c_name (printValue r l pu  x.chType (Some gv) v.Value) x.presentWhenName) |>
                List.head
            | _         -> raise(BugErrorException "unexpected type")

        | RefValue ((md,vs),v)         ->
            let vas = r.getValueAssignmentByName md.Value vs.Value
            vas.ada_name
