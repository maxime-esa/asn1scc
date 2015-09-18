module c_variables


open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open Asn1Values





let GetTasNameByKind kind (m:Asn1Module) (r:AstRoot) = 
    match kind with
    |Integer                            -> ch.Declare_Integer()
    |ReferenceType(modName, tasName,_)  -> Ast.GetTasCName tasName.Value r.TypePrefix
    |Boolean                            -> ch.Declare_Boolean()
    |Real                               -> ch.Declare_Real()
    |NullType                           -> ch.Declare_NullType()
    |_          -> raise(BugErrorException (sprintf "%A tt cannot appear inline" kind))


//let bitStringValueToByteArray (s:StringLoc) =
//    let s1 = s.Value.ToCharArray() |> Seq.map(fun x -> if x='0' then 0uy else 1uy) |> Seq.toList
//    let BitsToNibbles l:list<byte> =
//        let rec BitsToNibblesAux l acc :list<byte> =
//            match l with
//            | []                   -> List.rev acc
//            | i1::[]               -> BitsToNibblesAux [] (i1*8uy::acc)
//            | i1::i2::[]           -> BitsToNibblesAux [] ((i1*8uy+i2*4uy)::acc)
//            | i1::i2::i3::[]       -> BitsToNibblesAux [] ((i1*8uy+i2*4uy+i3*2uy)::acc)
//            | i1::i2::i3::i4::tail -> 
//                let newAcc = (i1*8uy+i2*4uy+i3*2uy+i4)::acc
//                BitsToNibblesAux tail newAcc
//        BitsToNibblesAux l []
//    let NibblesToBytes l:list<byte> =
//        let rec NibblesToBytesAux l acc:list<byte> =
//            match l with
//            | []                    -> List.rev acc
//            | i1::[]                -> NibblesToBytesAux [] ((i1*16uy)::acc)
//            | i1::i2::tail          -> NibblesToBytesAux tail ((i1*16uy+i2)::acc)
//        NibblesToBytesAux l []
//    NibblesToBytes (BitsToNibbles s1) |> List.toArray


let rec PrintAsn1Value (v:Asn1Value) (t:Asn1Type) (bInGlobalsScope:bool) (tasName:string, dummy:int) (m:Asn1Module) (r:AstRoot) = 
    let sTasName = tasName 
    let printRealValue vl =
        match System.Double.IsInfinity vl with
        | true  -> if vl < 0.0 then "-INFINITY" else "INFINITY"
        | false -> c_var.PrintRealValue vl


    match v.Kind, t.Kind with
    |_,ReferenceType(modName,tsName, _)           ->
        let baseType = Ast.GetBaseTypeConsIncluded t r
        let newTasName = match modName.Value = m.Name.Value with
                         | true -> Ast.GetTasCName tsName.Value r.TypePrefix
                         | false -> (ToC modName.Value) + "." + Ast.GetTasCName tsName.Value r.TypePrefix
        PrintAsn1Value v  baseType bInGlobalsScope (newTasName,0)  m r
    |IntegerValue(a), Integer                   -> c_var.PrintIntValue a.Value
    |IntegerValue(a), Real                      -> printRealValue (double a.Value)
    |RealValue(a), Real                         -> printRealValue a.Value
    |RefValue(modName,vasName), Enumerated(items)   -> 
        let enmItem = items |> Seq.find(fun x -> x.Name.Value = vasName.Value)
        c_var.PrintEnumValue (enmItem.CEnumName r C)
    |RefValue(modName,vasName), _               -> 
        match bInGlobalsScope with
        | false ->
            let vas = (r.GetModuleByName modName).ValueAssignments |> Seq.find(fun x -> x.Name.Value = vasName.Value)
            match modName.Value = m.Name.Value with
            | true      -> c_var.PrintRefValue1 vas.c_name
            | false     -> c_var.PrintRefValue2 (ToC modName.Value) vas.c_name
        | true  ->
            let actValue = Ast.GetActualValue modName vasName r
            PrintAsn1Value actValue t bInGlobalsScope (tasName, dummy) m r
    |StringValue(a), IA5String
    |StringValue(a), NumericString              -> 
        c_var.PrintStringValue (a.Value.Replace("\"","\"\"")) 
    |BooleanValue(a), Boolean                   -> c_var.PrintBooleanValue a.Value
    |OctetStringValue(bytes), BitString         -> PrintAsn1Value (Ast.ConvertOctetStringValue_to_BitStringValue v)  t bInGlobalsScope (tasName,dummy) m r
    |OctetStringValue(bytes), OctetString       ->
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let arBytes = bytes |> Seq.map(fun a -> a.Value) 
        c_var.PrintBitOrOctetStringValue (min=max) arBytes (BigInteger bytes.Length)
    | BitStringValue(bitVal), BitString -> 
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let arBytes = bitStringValueToByteArray bitVal
        c_var.PrintBitOrOctetStringValue (min=max) arBytes (BigInteger bitVal.Value.Length)
    | BitStringValue(bitVal), OctetString ->    PrintAsn1Value (Ast.ConvertBitStringValue_to_OctetStringValue v)  t bInGlobalsScope (tasName,dummy) m r
    | SeqOfValue(childValues), SequenceOf(childType)    -> 
        let min,max = uPER.GetSizebaleMinMax t.Kind t.Constraints r
        let childTasName = GetTasNameByKind childType.Kind m r
        let arrChVals = childValues |> Seq.map(fun x-> PrintAsn1Value x  childType bInGlobalsScope (childTasName,0) m r )    
//        let defValue = GetDefaultValueByType childType m r
//        let sDefValue = PrintAsn1Value defValue  childType (childTasName,0) m r
        c_var.PrintSequenceOfValue (min=max)  arrChVals 
    | SeqValue(childVals), Sequence(children)   ->
        let PrintChild (ch:ChildInfo) (chv:Asn1Value) = 
            c_var.PrintSequenceValueChild (ch.CName ProgrammingLanguage.C) (PrintAsn1Value chv ch.Type bInGlobalsScope (GetTasNameByKind ch.Type.Kind m r, 0) m r)


        let optChildren = seq {
            for ch in children |> Seq.filter(fun c -> c.Optionality.IsSome) do
                match ch.Optionality, childVals |> Seq.tryFind(fun (chName, _)  -> chName.Value = ch.Name.Value) with
                | _,Some(_)             -> yield c_var.PrintSequenceValue_child_exists (ch.CName ProgrammingLanguage.C) "1"
                //| Some(Default(_)),_    -> yield sv.PrintSequenceValue_child_exists (ch.CName ProgrammingLanguage.C) "1"
                | _,None                -> yield c_var.PrintSequenceValue_child_exists (ch.CName ProgrammingLanguage.C) "0"  } 
        let arrChildren = 
            seq {
                for ch in children  do
                    match childVals |> Seq.tryFind(fun (chName, _)  -> chName.Value = ch.Name.Value) with
                    | Some(chName, chVal)       -> yield c_var.PrintSequenceValueChild (ch.CName ProgrammingLanguage.C) (PrintAsn1Value chVal ch.Type bInGlobalsScope (GetTasNameByKind ch.Type.Kind m r, 0) m r)
                    | None                      -> 
                        match ch.Optionality with
                        |Some(Default(defVal))  ->  yield c_var.PrintSequenceValueChild (ch.CName ProgrammingLanguage.C) (PrintAsn1Value defVal ch.Type bInGlobalsScope (GetTasNameByKind ch.Type.Kind m r, 0) m r)
                        |Some(Optional)         ->  
                            let initVal = GetDefaultValueByType ch.Type m r 
                            yield c_var.PrintSequenceValueChild (ch.CName ProgrammingLanguage.C) (PrintAsn1Value initVal  ch.Type bInGlobalsScope (GetTasNameByKind ch.Type.Kind m r, 0) m r)
                        |_                      -> () 
            } |> Seq.toList
        c_var.PrintSequenceValue arrChildren optChildren
    | ChValue(altName,altVal), Choice(children)     -> 
        let ch = children |> Seq.find(fun c -> c.Name.Value = altName.Value)
        let chVal = PrintAsn1Value altVal ch.Type bInGlobalsScope (GetTasNameByKind ch.Type.Kind m r, 0) m r
        c_var.PrintChoiceValue  (ch.CName_Present C) (ch.CName ProgrammingLanguage.C) chVal
    | NullValue, NullType                           -> "0"
    | _                                         -> raise(BugErrorException "Invalid Combination")




let rec PrintValue (v:Asn1Value) (t:ConstraintType) (tasName:string) (m:Asn1Module)  (r:AstRoot)=
    let tActual = Ast.GetActualTypeAllConsIncluded t.Type r
    match t with
    | Same(_) -> PrintAsn1Value v t.Type false (tasName,1) m r
    | LengthOf(_) -> 
        match v.Kind with
        |IntegerValue(a)               -> c_var.PrintIntValue a.Value
        |RefValue(modName,vasName)     -> (ToC vasName.Value)
        | _                            -> raise(BugErrorException "Invalid combination type/value")
    | AlphabetOf(_) ->
        match v.Kind with
        | StringValue(a)               -> 
            match a.Value.Length with
            | 1  -> c_var.PrintCharValue a.Value.[0]
            | _  -> c_var.PrintStringValue (a.Value.Replace("\"","\"\"")) 
        | RefValue(modName,vasName)     -> PrintValue (Ast.GetActualValue modName vasName r)  t tasName m r
        | _                             -> raise(BugErrorException "Invalid combination type/value")
