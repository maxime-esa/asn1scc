module ExportToXml

open System
open System.Numerics
open System.IO
open System.Xml.Linq
open FsUtils
open Asn1AcnAst
open Asn1Fold

let private xname s = System.Xml.Linq.XName.Get(s)
let private xnameNs str ns = System.Xml.Linq.XName.Get(str, ns)

let private xsiUrl = "http://www.w3.org/2001/XMLSchema-instance"
let private xsi = XNamespace.Get xsiUrl
let private customWsSchemaLocation = "asn1sccAst.xsd"


let private printUInt (v:UInt32) = XElement(xname "IntegerValue", v)
let private printIntVal (v:BigInteger) = XElement(xname "IntegerValue", v)
let private printRealVal (v:double) = XElement(xname "RealValue", v)
let private printStringVal (v:String) = XElement(xname "StringValue", v)
let private printCharVal (v:char) = XElement(xname "StringValue", v)
let private printEnumVal (v:String) = XElement(xname "EnumValue", v)
let private printBoolVal (v:bool) = XElement(xname "BooleanValue", v)

let private printBitStringVal (v:BitStringValue) = XElement(xname "BitStringValue", v.Value)
let private printOctetStringVal (v:OctetStringValue) = XElement(xname "OctetStringValue", (v |> List.map(fun b -> b.Value)))

let rec private printSeqOfValue (v:SeqOfValue) = 
    XElement(xname "SequenceOfValue", (v |> List.map PrintAsn1GenericValue ))
and private printSeqValue(v:SeqValue) =
    XElement(xname "SequenceOfValue", 
        (v |> List.map(fun nv -> 
            XElement(xname "NamedValue", 
                XAttribute(xname "name", nv.name.Value),
                PrintAsn1GenericValue nv.Value                ))))
and private printChoiceValue (v:ChValue) =
    XElement(xname "ChoiceValue", 
                ([v] |> List.map(fun nv -> 
                    XElement(xname "NamedValue", 
                        XAttribute(xname "name", nv.name.Value),
                        PrintAsn1GenericValue nv.Value                ))))    
and private printRefValue ((md:StringLoc,ts:StringLoc), v:Asn1Value) =    
        XElement(xname "ReferenceValue", 
            XAttribute(xname "Module", md.Value),
            XAttribute(xname "Name", ts.Value),
            (PrintAsn1GenericValue v))
and private PrintAsn1GenericValue (v:Asn1Value) = 
    match v with
    |IntegerValue(v)         -> printIntVal v.Value
    |RealValue(v)            -> printRealVal v.Value
    |StringValue(v)          -> printStringVal v.Value
    |EnumValue(v)            -> printEnumVal v.Value
    |BooleanValue(v)         -> printBoolVal v.Value
    |BitStringValue(v)       -> printBitStringVal v
    |OctetStringValue(v)     -> printOctetStringVal v
    |SeqOfValue(v)           -> printSeqOfValue v
    |SeqValue(v)             -> printSeqValue v
    |ChValue(nv)             -> printChoiceValue nv
    |NullValue   _           -> XElement(xname "NullValue")
    |RefValue ((md,ts), v)   -> printRefValue ((md,ts), v)

let private printGenericConstraint printValue (c:GenericConstraint<'v>)  = 
    foldGenericConstraint
        (fun r1 r2 b s      -> XElement(xname "OR", r1, r2) , s)
        (fun r1 r2 s        -> XElement(xname "AND", r1, r2) , s)
        (fun r s            -> XElement(xname "ALL_EXCEPT", r), s)       
        (fun r1 r2 s        -> XElement(xname "EXCEPT", r1, r2), s)
        (fun r s            -> XElement(xname "ROOTC_CONSTRAINT", r), s)       
        (fun r1 r2 s        -> XElement(xname "ROOTC_CONSTRAINT_WITH_EXTENSION", r1, r2), s)
        (fun v  s           -> printValue v, s)
        c 
        0 |> fst

let private printRangeConstraint0 (printValue:'v1->XElement) printValue2  (c:RangeTypeConstraint<'v1,'v2>) = 
    foldRangeTypeConstraint
        (fun r1 r2 b s      -> XElement(xname "OR", r1, r2), s)
        (fun r1 r2 s        -> XElement(xname "AND", r1, r2) , s)
        (fun r s            -> XElement(xname "ALL_EXCEPT", r), s)       
        (fun r1 r2 s        -> XElement(xname "EXCEPT", r1, r2), s)
        (fun r s            -> XElement(xname "ROOTC_CONSTRAINT", r), s)       
        (fun r1 r2 s        -> XElement(xname "ROOTC_CONSTRAINT_WITH_EXTENSION", r1, r2), s)
        (fun v  s           -> printValue2 v,s)
        (fun v1 v2  b1 b2 s -> XElement(xname "Range", (XElement(xname "a", (printValue v1))), (XElement(xname "b", (printValue v2)))), s)
        (fun v1 b s         -> XElement(xname "GT", (XElement(xname "a", (printValue v1))) ),s )
        (fun v2 b s         -> XElement(xname "LT", (XElement(xname "b", (printValue v2))) ), s)
        c 
        0 |> fst

let private printRangeConstraint printValue (c:RangeTypeConstraint<'v1,'v1>)  = 
    printRangeConstraint0 printValue printValue c 


let private printSizableConstraint printValue (c:SizableTypeConstraint<'v>)  = 
    foldSizableTypeConstraint2
        (fun r1 r2 b s      -> XElement(xname "OR", r1, r2), s)
        (fun r1 r2 s        -> XElement(xname "AND", r1, r2) , s)
        (fun r s            -> XElement(xname "ALL_EXCEPT", r), s)       
        (fun r1 r2 s        -> XElement(xname "EXCEPT", r1, r2), s)
        (fun r s            -> XElement(xname "ROOTC_CONSTRAINT", r), s)       
        (fun r1 r2 s        -> XElement(xname "ROOTC_CONSTRAINT_WITH_EXTENSION", r1, r2), s)
        (fun v  s           -> printValue v,s)
        (fun sc s           -> 
            let sizeCon = printRangeConstraint0 printUInt printUInt sc 
            XElement(xname "SIZE", sizeCon), s)
        c 
        0 |> fst

let private printAlphaConstraint printValue (c:IA5StringConstraint)  = 
    foldStringTypeConstraint2
        (fun r1 r2 b s      -> XElement(xname "OR", r1, r2), s)
        (fun r1 r2 s        -> XElement(xname "AND", r1, r2) , s)
        (fun r s            -> XElement(xname "ALL_EXCEPT", r), s)       
        (fun r1 r2 s        -> XElement(xname "EXCEPT", r1, r2), s)
        (fun r s            -> XElement(xname "ROOTC_CONSTRAINT", r), s)       
        (fun r1 r2 s        -> XElement(xname "ROOTC_CONSTRAINT_WITH_EXTENSION", r1, r2), s)
        (fun v  s         -> (printValue v),s)
        (fun sc s           -> 
            let sizeCon = printRangeConstraint0 printUInt printUInt sc 
            XElement(xname "SIZE", sizeCon), s)
        (fun sc s           -> 
            let alphaCon = printRangeConstraint0 printCharVal printStringVal  sc 
            XElement(xname "ALPHA", alphaCon), s)
        c 
        0 |> fst



let private exportType (t:Asn1Type) = 
    Asn1Fold.foldType
        (fun ti us -> 
                    XElement(xname "INTEGER",
                        XElement(xname "CONS", ti.cons |> List.map (printRangeConstraint printIntVal) ),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printRangeConstraint printIntVal ))
                        ), us )
        (fun ti us -> XElement(xname "REAL",
                        XElement(xname "CONS", ti.cons |> List.map(printRangeConstraint printRealVal)),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printRangeConstraint printRealVal ))
                        ), us )
        (fun ti us -> XElement(xname "IA5String",
                        XElement(xname "CONS", ti.cons |> List.map(printAlphaConstraint printStringVal )),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printAlphaConstraint printStringVal ))
                        ), us )
        (fun ti us -> XElement(xname "NumericString",
                        XElement(xname "CONS", ti.cons |> List.map(printAlphaConstraint printStringVal )),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printAlphaConstraint printStringVal ))
                        ), us )
        (fun ti us -> XElement(xname "OCTET_STRING",
                        XElement(xname "CONS", ti.cons |> List.map(printSizableConstraint printOctetStringVal )),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printSizableConstraint printOctetStringVal ))
                        ), us )
        (fun ti us -> XElement(xname "NULL"), us )
        (fun ti us -> XElement(xname "BIT_STRING",
                        XElement(xname "CONS", ti.cons |> List.map(printSizableConstraint printBitStringVal )),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printSizableConstraint printBitStringVal ))
                        ), us )
        (fun ti us -> XElement(xname "BOOLEAN",
                        XElement(xname "CONS", ti.cons |> List.map(printGenericConstraint printBoolVal )),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printGenericConstraint printBoolVal ))
                        ), us )
        (fun ti us -> XElement(xname "Enumerated",
                        XElement(xname "Items", ti.items |> List.map(fun c ->  XElement(xname "Item", XAttribute(xname "name", c.Name.Value), XAttribute(xname "value", c.definitionValue))   )),
                        XElement(xname "CONS", ti.cons |> List.map(printGenericConstraint printEnumVal )),
                        XElement(xname "WITH_CONS", ti.withcons |> List.map(printGenericConstraint printEnumVal ))
                        ), us )
        (fun ti nc us -> XElement(xname "SEQUENCE_OF",
                            nc,
                            XElement(xname "CONS", ti.cons |> List.map(printSizableConstraint printSeqOfValue )),
                            XElement(xname "WITH_CONS", ti.withcons |> List.map(printSizableConstraint printSeqOfValue ))
                            ), us )
        (fun ti children us -> XElement(xname "SEQUENCE",
                                children,
                                XElement(xname "CONS", ti.cons |> List.map(printGenericConstraint printSeqValue )),
                                XElement(xname "WITH_CONS", ti.withcons |> List.map(printGenericConstraint printSeqValue ))
                                ), us )
        (fun ch nt us -> XElement(xname "SEQUENCE_COMPONENT",
                            XAttribute(xname "name", ch.Name.Value),
                            nt), us )
        (fun ch us -> XElement(xname "ACN_COMPONENT",
                            XAttribute(xname "name", ch.Name.Value)), us )
        (fun ti children us -> XElement(xname "CHOICE",
                                children,
                                XElement(xname "CONS", ti.cons |> List.map(printGenericConstraint printChoiceValue )),
                                XElement(xname "WITH_CONS", ti.withcons |> List.map(printGenericConstraint printChoiceValue ))
                                ), us )
        (fun ch nt us -> XElement(xname "CHOICE_ALTERNATIVE",
                            XAttribute(xname "name", ch.Name.Value),
                            nt), us )
        (fun ref nt us -> XElement(xname "REFERENCE_TYPE",
                            XAttribute(xname "Module", ref.modName.Value),
                            XAttribute(xname "TypeAssignment", ref.tasName.Value),
                            nt), us )
        (fun t nk us -> XElement(xname "Asn1Type",
                            nk), us )
        t
        0 |> fst



let private exportTas (tas:TypeAssignment) =
    XElement(xname "TypeAssignment",
        XAttribute(xname "Name", tas.Name.Value),
        (exportType tas.Type)
    )

let private exportVas (vas:ValueAssignment) =
    XElement(xname "ValueAssignment",
        XAttribute(xname "Name", vas.Name.Value),
        (exportType vas.Type),
        (PrintAsn1GenericValue vas.Value)
    )

let private exportModule (m:Asn1Module) =
    XElement(xname "Module",
        XAttribute(xname "Name", m.Name.Value),
        XElement(xname "TypeAssigments", m.TypeAssignments |> List.map  exportTas),
        XElement(xname "ValueAssigments",m.ValueAssignments |> List.map  exportVas)
    )

let exportFile (r:AstRoot) (fileName:string) =
    let wsRoot =
        XElement(xname "AstRoot",
            XAttribute(XNamespace.Xmlns + "xsi", xsi),
            XAttribute(xnameNs "noNamespaceSchemaLocation" xsiUrl, customWsSchemaLocation),
            r.Files |>
            List.map(fun f ->
                    XElement(xname "Asn1File",
                        XAttribute(xname "FileName", f.FileName),
                        XElement(xname "Modules",
                            f.Modules |> List.map  exportModule)
                    )))


    let dec = new XDeclaration("1.0", "utf-8", "true")
    let doc =new XDocument(dec)
    doc.AddFirst wsRoot
    doc.Save(fileName)
