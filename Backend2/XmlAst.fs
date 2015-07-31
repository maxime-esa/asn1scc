module XmlAst
open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils

let GetMinMax uperRange = 
    match uperRange with
    | Concrete(min, max)      -> min.ToString(), max.ToString()
    | PosInf(a)               -> a.ToString(), "MAX"
    | NegInf(max)             -> "MIN", max.ToString()
    | Full                    -> "MIN", "MAX"
    | Empty                   -> raise(BugErrorException "")
let handTypeWithMinMax name uperRange func =
    let sMin, sMax = GetMinMax uperRange
    func name sMin sMax (sMin=sMax)

let rec PrintType (t:Asn1Type) modName (r:AstRoot) =
    let PrintTypeAux (t:Asn1Type) =
        match t.Kind with
        | Integer               -> handTypeWithMinMax "IntegerType"     (GetTypeUperRange t.Kind t.Constraints r) xml.MinMaxType
        | BitString             -> handTypeWithMinMax "BitStringType"   (GetTypeUperRange t.Kind t.Constraints r) xml.MinMaxType2
        | OctetString           -> handTypeWithMinMax "OctetStringType" (GetTypeUperRange t.Kind t.Constraints r) xml.MinMaxType2
        | Real                  -> handTypeWithMinMax "RealType"        (GetTypeRange_real t.Kind t.Constraints r) xml.MinMaxType
        | IA5String             -> handTypeWithMinMax "IA5StringType"   (GetTypeUperRange t.Kind t.Constraints r) xml.MinMaxType2
        | NumericString         -> handTypeWithMinMax "NumericStringType" (GetTypeUperRange t.Kind t.Constraints r) xml.MinMaxType2
        | Boolean               -> xml.BooleanType ()
        | NullType              -> xml.NullType ()
        | Choice(children)      -> 
            let emitChild (c:ChildInfo) =
                xml.ChoiceChild c.Name.Value (BigInteger c.Name.Location.srcLine) (BigInteger c.Name.Location.charPos) (PrintType c.Type modName r) (c.CName_Present C)
            xml.ChoiceType (children |> Seq.map emitChild)
        | Sequence(children)    -> 
            let emitChild (c:ChildInfo) =
                match c.Optionality with
                | Some(Default(vl)) -> xml.SequenceChild c.Name.Value true (PrintAsn1.PrintAsn1Value vl) (BigInteger c.Name.Location.srcLine) (BigInteger c.Name.Location.charPos) (PrintType c.Type modName r)
                | _                 -> xml.SequenceChild c.Name.Value c.Optionality.IsSome null (BigInteger c.Name.Location.srcLine) (BigInteger c.Name.Location.charPos) (PrintType c.Type modName r)
            xml.SequenceType (children |> Seq.map emitChild)
        | Enumerated(items)     -> 
            let emitItem (idx: int) (it : Ast.NamedItem) =
                match it._value with
                | Some(vl)  -> xml.EnumItem it.Name.Value (Ast.GetValueAsInt vl r) (BigInteger it.Name.Location.srcLine) (BigInteger it.Name.Location.charPos) (it.CEnumName r C)
                | None      -> xml.EnumItem it.Name.Value (BigInteger idx) (BigInteger it.Name.Location.srcLine) (BigInteger it.Name.Location.charPos) (it.CEnumName r C)
            xml.EnumType (items |> Seq.mapi emitItem)
        | SequenceOf(child)     -> 
            let sMin, sMax = GetMinMax (GetTypeUperRange t.Kind t.Constraints r) 
            xml.SequenceOfType sMin sMax  (PrintType child modName r)
        | ReferenceType(md,ts, _) ->  
            let uperRange = 
                match (Ast.GetActualType t r).Kind with
                | Integer | BitString | OctetString | IA5String | NumericString | SequenceOf(_)         -> Some (GetMinMax (GetTypeUperRange t.Kind t.Constraints r) )
                | Real                                                                                  -> Some (GetMinMax (GetTypeRange_real t.Kind t.Constraints r))
                | Boolean | NullType | Choice(_) | Enumerated(_) | Sequence(_) | ReferenceType(_)       -> None
            let sModName = if md.Value=modName then null else md.Value
            match uperRange with
            | Some(sMin, sMax)  -> xml.RefTypeMinMax sMin sMax ts.Value sModName
            | None              -> xml.RefType ts.Value sModName

    xml.TypeGeneric (BigInteger t.Location.srcLine) (BigInteger t.Location.charPos) (PrintTypeAux t)


let DoWork (r:AstRoot) =
    let AllExported (m: Asn1Module) =
        match m.Exports with
        | All -> true
        | _ -> false        
    let PrintVas (vas: Ast.ValueAssignment) modName =
        xml.VasXml vas.Name.Value (BigInteger vas.Name.Location.srcLine) (BigInteger vas.Name.Location.charPos) (PrintType vas.Type modName r) (PrintAsn1.PrintAsn1Value vas.Value)
    let PrintTas (tas:Ast.TypeAssignment) modName =
        xml.TasXml tas.Name.Value (BigInteger tas.Name.Location.srcLine) (BigInteger tas.Name.Location.charPos) (PrintType tas.Type modName r)
    let PrintModule (m:Asn1Module) =
        let PrintImpModule (im:Ast.ImportedModule) =
            xml.ImportedMod im.Name.Value (im.Types |> Seq.map(fun x -> x.Value)) (im.Values |> Seq.map(fun x -> x.Value))
        xml.ModuleXml m.Name.Value (m.Imports |> Seq.map PrintImpModule) m.ExportedTypes m.ExportedVars (m.TypeAssignments |> Seq.map (fun t -> PrintTas t m.Name.Value)) (m.ValueAssignments |> Seq.map (fun t -> PrintVas t m.Name.Value)) (AllExported m)
    let PrintFile (f:Asn1File) =
        xml.FileXml f.FileName (f.Modules |> Seq.map PrintModule)
    let content = xml.RootXml (r.Files |> Seq.map PrintFile)
    File.WriteAllText(r.AstXmlAbsFileName, content.Replace("\r",""))



