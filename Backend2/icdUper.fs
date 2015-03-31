module icdUper

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils


let Kind2Name (t:Asn1Type) =
    match t.Kind with
    | ReferenceType(md,ts, _)   -> ts.Value
    | Integer                       -> "INTEGER"
    | BitString                     -> "BIT-STRING"
    | OctetString                   -> "OCTET-STRING"
    | Boolean                       -> "BOOLEAN"
    | Choice(_)                     -> "CHOICE"
    | Enumerated(_)                 -> "ENUMERATED"
    | IA5String                     -> "IA5String"
    | NumericString                 -> "NumericString"
    | NullType                      -> "NULL"
    | Real                          -> "REAL"
    | Sequence(_)                   -> "SEQUENCE"
    | SequenceOf(_)                 -> "SEQUENCE-OF"


let GetWhyExplanation (t:Ast.Asn1Type) (r:AstRoot) =
    match t.Kind with
    | Real      -> icd_uper.RealSizeExplained ()
    | Integer   ->
        match (uPER.GetTypeUperRange t.Kind t.Constraints r) with
        | Concrete(a,b)  when a=b       -> icd_uper.ZeroSizeExplained()
        | Full                          -> icd_uper.IntSizeExplained()
        | _                             -> ""
    | _         -> ""    

let rec printType (tas:Ast.TypeAssignment) (t:Ast.Asn1Type) (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  color =
    let uperSizeInBitsAsInt func (kind:Asn1TypeKind) (cons:list<Asn1Constraint>)  (ast:AstRoot) =
        match (func kind cons ast) with
        | Bounded(maxBits)        ->  
            let maxBytes = BigInteger(System.Math.Ceiling(double(maxBits)/8.0))
            maxBits.ToString(), maxBytes.ToString()
        | Infinite          -> icd_uper.Infinity (), icd_uper.Infinity ()

    
    let GetCommentLine (comments:string array) (t:Asn1Type) =
        let singleComment = comments |> Seq.StrJoin (icd_uper.NewLine ()) 
        let ret = 
            match (Ast.GetActualType t r).Kind with
            | Enumerated(items) ->
                let EmitItem (n:Ast.NamedItem) =
                    let comment =  n.Comments |> Seq.StrJoin "\n"
                    match comment.Trim() with
                    | ""        ->    icd_uper.EmitEnumItem n.Name.Value (GetItemValue items n r)
                    | _         ->    icd_uper.EmitEnumItemWithComment n.Name.Value (GetItemValue items n r) comment
                let itemsHtml = items |> Seq.map EmitItem
                let extraComment = icd_uper.EmitEnumInternalContents itemsHtml
                match singleComment.Trim() with
                | ""    -> extraComment
                | _     -> singleComment + (icd_uper.NewLine ()) + extraComment
            | _                 -> singleComment
        let ret = ret.Replace("/*","").Replace("*/","").Replace("--","")
        if ret.Trim() = "" then null else ret  
    match t.Kind with
    | Integer    
    | Real    
    | Boolean   
    | NullType
    | Enumerated(_) ->
        let sTasName = tas.Name.Value
        let sKind = Kind2Name  t
        let sMaxBits, sMaxBytes = uperSizeInBitsAsInt uperGetMaxSizeInBits t.Kind t.Constraints r
        let sMinBits, sMinBytes = uperSizeInBitsAsInt uperGetMinSizeInBits t.Kind t.Constraints r
        let sMaxBitsExplained =  GetWhyExplanation t r
        let sCommentLine = GetCommentLine tas.Comments t
        let sAsn1Constraints = t.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin ""

        icd_uper.EmitPrimitiveType color sTasName (ToC sTasName) sKind sMinBytes sMaxBytes sMaxBitsExplained sCommentLine ( if sAsn1Constraints.Trim() ="" then "N.A." else sAsn1Constraints) sMinBits sMaxBits
        
    |ReferenceType(_) ->
        let baseTypeWithCons = Ast.GetActualTypeAllConsIncluded t r
        printType tas baseTypeWithCons r acn color
    |Sequence(children) -> 
        let EmitChild (i:int) (ch:ChildInfo) =
            let sClass = if i % 2 = 0 then icd_uper.EvenRow() else icd_uper.OddRow()
            let nIndex = BigInteger i
            let sComment = GetCommentLine ch.Comments ch.Type
            let sOptionality = match ch.Optionality with
                               | None       -> "No"
                               | Some(Default(_))   -> "Def"
                               | Some(_)            -> "Yes"
            let sType = match ch.Type.Kind with
                        | ReferenceType(md,ts,_)  -> icd_uper.EmmitSeqChild_RefType ts.Value (ToC ts.Value)
                        | _                           -> Kind2Name ch.Type
            let sAsn1Constraints = 
                let ret = ch.Type.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin ""
                ( if ret.Trim() ="" then "N.A." else ret)
            let sMaxBits, sMaxBytes = uperSizeInBitsAsInt uperGetMaxSizeInBits  ch.Type.Kind ch.Type.Constraints r
            let sMinBits, sMinBytes = uperSizeInBitsAsInt uperGetMinSizeInBits  ch.Type.Kind ch.Type.Constraints r
            let sMaxBitsExplained =  GetWhyExplanation ch.Type r
            icd_uper.EmmitSequenceChild sClass nIndex ch.Name.Value sComment  sOptionality  sType sAsn1Constraints sMinBits (sMaxBits+sMaxBitsExplained)
        
        let SeqPreamble =
            let optChild = children |> Seq.filter (fun x -> x.Optionality.IsSome) |> Seq.mapi(fun i c -> icd_uper.EmmitSequencePreambleSingleComment (BigInteger (i+1)) c.Name.Value)
            let nLen = optChild |> Seq.length
            if  nLen > 0 then
                let sComment = icd_uper.EmmitSequencePreambleComment optChild
                let ret = icd_uper.EmmitSequenceChild (icd_uper.OddRow()) (BigInteger 1) "Preamble" sComment  "No"  "Bit mask" "N.A." (nLen.ToString()) (nLen.ToString())
                Some ret
            else
                None

        let sTasName = tas.Name.Value
        let sMaxBits, sMaxBytes = uperSizeInBitsAsInt uperGetMaxSizeInBits t.Kind t.Constraints r
        let sMinBits, sMinBytes = uperSizeInBitsAsInt uperGetMinSizeInBits t.Kind t.Constraints r
        let sMaxBitsExplained = ""
        let sCommentLine = GetCommentLine tas.Comments t
        
        let arChildren idx = children |> Seq.mapi(fun i ch -> EmitChild (idx + i) ch) |> Seq.toList
        let arRows =
            match SeqPreamble with 
            | None          -> arChildren 1
            | Some(prm)     -> prm::(arChildren 2)

        icd_uper.EmitSequence color sTasName (ToC sTasName) sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arRows

    |Choice(children)   -> 
        let EmitChild (i:int) (ch:ChildInfo) =
            let sClass = if i % 2 = 0 then icd_uper.EvenRow() else icd_uper.OddRow()
            let nIndex = BigInteger 2
            let sComment = GetCommentLine ch.Comments ch.Type
            let sType = match ch.Type.Kind with
                        | ReferenceType(md,ts,_)   -> icd_uper.EmmitSeqChild_RefType ts.Value (ToC ts.Value)
                        | _                        -> Kind2Name ch.Type
            let sAsn1Constraints = 
                let ret = ch.Type.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin ""
                ( if ret.Trim() ="" then "N.A." else ret)
            let sMaxBits, sMaxBytes = uperSizeInBitsAsInt uperGetMaxSizeInBits ch.Type.Kind ch.Type.Constraints r
            let sMinBits, sMinBytes = uperSizeInBitsAsInt uperGetMinSizeInBits ch.Type.Kind ch.Type.Constraints r
            let sMaxBitsExplained =  GetWhyExplanation ch.Type r
            icd_uper.EmmitChoiceChild sClass nIndex ch.Name.Value sComment  sType sAsn1Constraints sMinBits (sMaxBits+sMaxBitsExplained)
        let ChIndex =
            let optChild = children |> Seq.mapi(fun i c -> icd_uper.EmmitChoiceIndexSingleComment (BigInteger (i+1)) c.Name.Value)
            let sComment = icd_uper.EmmitChoiceIndexComment optChild
            let indexSize = (GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children))).ToString()
            icd_uper.EmmitChoiceChild (icd_uper.OddRow()) (BigInteger 1) "ChoiceIndex" sComment    "unsigned int" "N.A." indexSize indexSize

        let sTasName = tas.Name.Value
        let sMaxBits, sMaxBytes = uperSizeInBitsAsInt uperGetMaxSizeInBits t.Kind t.Constraints r
        let sMinBits, sMinBytes = uperSizeInBitsAsInt uperGetMinSizeInBits t.Kind t.Constraints r
        let sMaxBitsExplained = ""
        let sCommentLine = GetCommentLine tas.Comments t
        
        let arChildren = children |> Seq.mapi(fun i ch -> EmitChild (2 + i) ch) |> Seq.toList
        let arRows = ChIndex::arChildren

        icd_uper.EmitChoice color sTasName (ToC sTasName) sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arRows

    | OctetString   
    | NumericString   
    | IA5String   
    | BitString   
    |SequenceOf(_)  -> 
        let getCharSize () =
            let charSet = GetTypeUperRangeFrom(t.Kind, t.Constraints, r)
            let charSize = GetNumberOfBitsForNonNegativeInteger (BigInteger (charSet.Length-1))
            charSize.ToString()
        let ChildRow (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_uper.EvenRow() else icd_uper.OddRow()
            let nIndex = i
            let sFieldName = sprintf "Item #%A" i
            let sComment = ""
            let sType, sAsn1Constraints, sMinBits, sMaxBits = 
                match t.Kind with
                | SequenceOf(child) ->
                    let ret = child.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin "" 
                    let ret = ( if ret.Trim() ="" then "N.A." else ret)
                    let sMaxBits, _ = uperSizeInBitsAsInt uperGetMaxSizeInBits child.Kind child.Constraints r
                    let sMinBits, _ = uperSizeInBitsAsInt uperGetMinSizeInBits child.Kind child.Constraints r
                    let sMaxBitsExplained =  GetWhyExplanation child r
                    match child.Kind with
                    | ReferenceType(md,ts,_)   -> icd_uper.EmmitSeqChild_RefType ts.Value (ToC ts.Value), ret, sMinBits, (sMaxBits+sMaxBitsExplained)
                    | _                        -> Kind2Name child, ret, sMinBits, (sMaxBits+sMaxBitsExplained)
                | IA5String                    -> "ASCII CHARACTER", "", getCharSize (), getCharSize ()
                | NumericString                -> "NUMERIC CHARACTER", "", getCharSize (), getCharSize ()
                | OctetString                  -> "OCTET", "", "8", "8"
                | BitString                    -> "BIT", "", "1","1"
                | _                            -> raise(BugErrorException "")
            icd_uper.EmmitChoiceChild sClass nIndex sFieldName sComment  sType sAsn1Constraints sMinBits sMaxBits
            
        let LengthRow =
            let nMin, nLengthSize = 
                match (GetTypeUperRange t.Kind t.Constraints  r) with
                | Concrete(a,b)  when a=b       -> 0I, 0I
                | Concrete(a,b)                 -> (GetNumberOfBitsForNonNegativeInteger(b-a)), (GetNumberOfBitsForNonNegativeInteger(b-a))
                | NegInf(_)                     -> raise(BugErrorException "")
                | PosInf(b)                     ->  8I, 16I
                | Empty                         -> raise(BugErrorException "")
                | Full                          -> 8I, 16I
            let comment = "Special field used by PER to indicate the number of items present in the array."
            let ret = t.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin "" 
            let sCon = ( if ret.Trim() ="" then "N.A." else ret)

            icd_uper.EmmitChoiceChild (icd_uper.OddRow()) (BigInteger 1) "Length" comment    "unsigned int" sCon (nMin.ToString()) (nLengthSize.ToString())

        let sTasName = tas.Name.Value
        let sMaxBits, sMaxBytes = uperSizeInBitsAsInt uperGetMaxSizeInBits t.Kind t.Constraints r
        let sMinBits, sMinBytes = uperSizeInBitsAsInt uperGetMinSizeInBits t.Kind t.Constraints r
        let sMaxBitsExplained = ""
        
        let sFixedLengthComment (nMax: BigInteger) =
            sprintf "Length is fixed to %A elements (no length determinant is needed)." nMax

        let arRows, sExtraComment = 
            match (GetTypeUperRange t.Kind t.Constraints  r) with
            | Concrete(a,b)  when a=b && b<2I     -> [ChildRow 1I], "The array contains a single element."
            | Concrete(a,b)  when a=b && b=2I    -> (ChildRow 1I)::(ChildRow 2I)::[], (sFixedLengthComment b)
            | Concrete(a,b)  when a=b && b>2I    -> (ChildRow 1I)::(icd_uper.EmitRowWith3Dots())::(ChildRow b)::[], (sFixedLengthComment b)
            | Concrete(a,b)  when a<>b && b<2I    -> LengthRow::(ChildRow 2I)::[],""
            | Concrete(a,b)                       -> LengthRow::(ChildRow 2I)::(icd_uper.EmitRowWith3Dots())::(ChildRow (b+1I))::[], ""
            | PosInf(_)                            
            | Full                                -> LengthRow::(ChildRow 2I)::(icd_uper.EmitRowWith3Dots())::(ChildRow 65535I)::[], ""
            | NegInf(_)                           -> raise(BugErrorException "")
            | Empty                               -> [], ""
        
        let sCommentLine = match GetCommentLine tas.Comments t with
                           | null | ""  -> sExtraComment
                           | _          -> sprintf "%s%s%s" (GetCommentLine tas.Comments t) (icd_uper.NewLine()) sExtraComment


        icd_uper.EmitSizeable color sTasName  (ToC sTasName) (Kind2Name t) sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arRows


let PrintTas (tas:Ast.TypeAssignment) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) blueTasses =
    let tasColor =
        match blueTasses |> Seq.exists (fun x -> x = tas.Name.Value) with
        |true   -> icd_uper.Blue ()
        |false  -> icd_uper.Orange ()
    icd_uper.EmmitTass (printType tas tas.Type r acn tasColor) 


let getModuleBlueTasses (m:Asn1Module) =
        m.TypeAssignments |> 
        Seq.collect(fun x -> Ast.GetMySelfAndChildren x.Type) |>
        Seq.choose(fun x -> match x.Kind with ReferenceType(md,nm,true) -> Some (md.Value,nm.Value) |_ -> None) |> Seq.toList


let PrintModule (m:Asn1Module) (f:Asn1File) (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  =
    let blueTasses = getModuleBlueTasses m |> Seq.map snd
    let tases = m.TypeAssignments |> Seq.map (fun x -> PrintTas x r acn blueTasses)
    let comments = []
    icd_uper.EmmitModule m.Name.Value comments tases

let PrintFile1 (f:Asn1File)  (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  =
    let modules = f.Modules |> Seq.map (fun  m -> PrintModule m f r acn )  
    icd_uper.EmmitFile (Path.GetFileName f.FileName) modules 

let PrintFile2 (f:Asn1File) = 
    let tasNames = f.Modules |> Seq.collect(fun x -> x.TypeAssignments) |> Seq.map(fun x -> x.Name.Value) |> Seq.toArray
    let blueTasses = f.Modules |> Seq.collect(fun m -> getModuleBlueTasses m)
    let blueTassesWithLoc = 
              f.TypeAssignments |> 
              Seq.map(fun x -> x.Type) |> 
              Seq.collect(fun x -> Ast.GetMySelfAndChildren x) |>
              Seq.choose(fun x -> match x.Kind with
                                  |ReferenceType(md,ts,true)    -> 
                                    let tas = f.TypeAssignments |> Seq.find(fun y -> y.Name.Value = ts.Value)
                                    Some(ts.Value, tas.Type.Location.srcLine, tas.Type.Location.charPos)
                                  | _                           -> None ) |> Seq.toArray
    let asn1Content = Antlr.Html.getAsn1InHtml(f.Tokens, tasNames, blueTassesWithLoc)
    icd_uper.EmmitFilePart2  (Path.GetFileName f.FileName ) asn1Content

let DoWork (r:AstRoot) (acn:AcnTypes.AcnAstResolved) outDir =
    let files1 = r.Files |> Seq.map (fun f -> PrintFile1 f r acn) 
    let files2 = r.Files |> Seq.map PrintFile2
    let allTypes = r.Files |> List.collect(fun x -> x.TypeAssignments) |> List.map(fun x -> x.Type) |> Seq.collect(fun x -> Ast.GetMySelfAndChildren x )
    let bIntegerSizeMustBeExplained = allTypes |> Seq.exists(fun x -> match x.Kind with 
                                                                      | Integer -> match GetTypeUperRange x.Kind x.Constraints r with 
                                                                                   | Full | PosInf(_) |  NegInf(_)  -> true 
                                                                                   |_                               ->false 
                                                                      | _ -> false)
    let bRealSizeMustBeExplained = allTypes |> Seq.exists(fun x -> match x.Kind with Real ->true | _ -> false)
    let bLengthSizeMustBeExplained = false
    let bWithComponentMustBeExplained = false
    let bZeroBitsMustBeExplained = allTypes |> Seq.exists(fun x -> match x.Kind with 
                                                                   | Integer -> match uperGetMaxSizeInBits x.Kind x.Constraints r with Bounded(a) when a = 0I -> true |_->false 
                                                                   | _ -> false)
    let content = icd_uper.RootHtml files1 files2 bIntegerSizeMustBeExplained bRealSizeMustBeExplained bLengthSizeMustBeExplained bWithComponentMustBeExplained bZeroBitsMustBeExplained
    File.WriteAllText(Path.Combine(outDir,r.IcdUperHtmlFileName), content.Replace("\r",""))

