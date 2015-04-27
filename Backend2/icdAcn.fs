module icdAcn

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open CloneTree
open spark_utils
open Antlr.Runtime
open Antlr.Acn


let printPoint (p:AcnTypes.Point) =
    match p with
    | AcnTypes.TypePoint(pth)
    | AcnTypes.TempPoint(pth)        -> pth |> Seq.StrJoin "."
    | AcnTypes.ParamPoint(pth)       -> pth.Tail.Tail |> Seq.StrJoin "."


let makeEmptyNull (s:string) =
    match s with
    | null  -> null
    | _     -> match s.Trim() with "" -> null | _ -> s


let printParamType = function
    | AcnTypes.Integer       -> "INTEGER"
    | AcnTypes.Boolean       -> "BOOLEAN"
    | AcnTypes.NullType      -> "NULL"
    | AcnTypes.RefTypeCon(_,ts)  -> ts.Value


let getAcnMax (t:Ast.Asn1Type) path (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let (bits, bytes) = Acn.RequiredBitsForAcnEncodingInt t path r acn
    bits.ToString(), bytes.ToString()


let getAcnMin (t:Ast.Asn1Type) path (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let (bits, bytes) = Acn.RequiredMinBitsForAcnEncodingInt t path r acn
    bits.ToString(), bytes.ToString()


let rec printType (tas:Ast.TypeAssignment) (t:Ast.Asn1Type) path (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  color =

    let sTasName = tas.Name.Value
    let sKind = icdUper.Kind2Name  t
    let sMaxBits, sMaxBytes = getAcnMax t path r acn
    let sMinBits, sMinBytes = getAcnMin t path r acn
    let sMaxBitsExplained =  ""
    let sAsn1Constraints = t.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin ""
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
        ret.Trim()

    let sCommentLine = GetCommentLine tas.Comments t


    let EmitSeqOrChoiceChild (i:int) (ch:ChildInfo) (optionalLikeUperChildren:ChildInfo list) getPresence =
        let sClass = if i % 2 = 0 then icd_uper.EvenRow() else icd_uper.OddRow()
        let nIndex = BigInteger i
        let sComment = GetCommentLine ch.Comments ch.Type

        let sPresentWhen = getPresence ch

        let sType = match ch.Type.Kind with
                    | ReferenceType(md,ts,_)  -> icd_uper.EmmitSeqChild_RefType ts.Value (ToC ts.Value)
                    | _                       -> icdUper.Kind2Name ch.Type
        let sAsn1Constraints = 
            let ret = ch.Type.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin ""
            ( if ret.Trim() ="" then "N.A." else ret)
        let sMaxBits, sMaxBytes = getAcnMax ch.Type (path@[ch.Name.Value]) r acn
        let sMinBits, sMinBytes = getAcnMin ch.Type (path@[ch.Name.Value]) r acn

        icd_acn.EmmitSeqOrChoiceRow sClass nIndex ch.Name.Value sComment  sPresentWhen  sType sAsn1Constraints sMinBits sMaxBits


    let myParams colSpan= 
        acn.Parameters |> List.filter(fun p -> p.TasName=tas.Name.Value && p.ModName=m.Name.Value) |>
        List.mapi(fun i x -> 
            let sType = match x.Asn1Type with
                            | AcnTypes.Integer              -> "INTEGER"
                            | AcnTypes.Boolean              -> "BOOLEAN"
                            | AcnTypes.NullType             -> "NULL"
                            | AcnTypes.RefTypeCon(_,ts)     -> icd_uper.EmmitSeqChild_RefType ts.Value (ToC ts.Value)

            icd_acn.PrintParam (i+1).AsBigInt x.Name sType colSpan
            )


    let hasAcnDef = acn.Files |> Seq.collect snd |> Seq.exists(fun x -> x.Text = tas.Name.Value)


    match t.Kind with
    | Integer      
    | Real    
    | Boolean   
    | NullType
    | Enumerated(_) ->
        icd_acn.EmitPrimitiveType color sTasName (ToC sTasName) hasAcnDef sKind sMinBytes sMaxBytes sMaxBitsExplained sCommentLine ( if sAsn1Constraints.Trim() ="" then "N.A." else sAsn1Constraints) sMinBits sMaxBits (myParams 2I) (sCommentLine.Split [|'\n'|])

    |ReferenceType(modl,tsName,_) ->
        let baseTypeWithCons = Ast.GetActualTypeAllConsIncluded t r
        printType tas baseTypeWithCons [modl.Value; tsName.Value] m r acn color
    |Sequence(children) -> 
        let optionalLikeUperChildren = children |> 
                                       List.filter(fun x -> match Acn.GetPresenseEncodingClass path x acn with Some(Acn.LikeUPER) -> true |_ -> false)
        let SeqPreamble =
            match optionalLikeUperChildren with
            | []    -> None
            | _     ->
                let nLen = optionalLikeUperChildren |> Seq.length
                let ret = icd_acn.EmmitSeqOrChoiceRow (icd_uper.OddRow()) 1I "Preamble" (icd_acn.EmmitSequencePreambleComment ())  "always"  "Bit mask" "N.A." (nLen.ToString()) (nLen.ToString())
                Some ret
        let getPresence (ch:ChildInfo) =
            match Acn.GetPresenseEncodingClass path ch acn with
            | None                      -> "always"
            | Some(Acn.LikeUPER)        -> 
                let aux1 = function
                    | 1 -> "st"
                    | 2 -> "nd"
                    | 3 -> "rd"
                    | _ -> "th"
                let nBit =  optionalLikeUperChildren |> Seq.findIndex(fun x -> x.Name.Value = ch.Name.Value) |> (+) 1
                sprintf "when the %d%s bit of the bit mask is set" nBit (aux1 nBit)
            | Some(Acn.PresBool(pnt))   -> sprintf "when %s is true" (printPoint pnt)
            | Some(Acn.PresInt(pnt, v)) -> sprintf "when %s is %A" (printPoint pnt) v
            | Some(Acn.PresStr(pnt, v)) -> sprintf "when %s is %A" (printPoint pnt) v

        let arChildren idx = children |> Seq.mapi(fun i ch -> EmitSeqOrChoiceChild (idx + i) ch optionalLikeUperChildren (fun x-> "always")) |> Seq.toList
        let arRows =
            match SeqPreamble with 
            | None          -> arChildren 1
            | Some(prm)     -> prm::(arChildren 2)

        icd_acn.EmitSequenceOrChoice color sTasName (ToC sTasName) hasAcnDef "SEQUENCE" sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arRows (myParams 6I) (sCommentLine.Split [|'\n'|])

    |Choice(children)   -> 
        let Choice_like_uPER() =
            let ChIndex =
                let sComment = icd_acn.EmmitChoiceIndexComment ()
                let indexSize = GetNumberOfBitsForNonNegativeInteger(BigInteger(Seq.length children)) |> toString
                icd_acn.EmmitSeqOrChoiceRow (icd_uper.OddRow()) 1I "ChoiceIndex" sComment  "always"  "unsigned int" "N.A." indexSize indexSize
            let getPresenceWhenNone_uper (ch:ChildInfo) =
                let index = children |> Seq.findIndex ((=) ch) 
                sprintf "ChoiceIndex = %d" index
            let EmitChild (i:int) (ch:ChildInfo) = EmitSeqOrChoiceChild i ch [] getPresenceWhenNone_uper
            let arChildren = children |> Seq.mapi(fun i ch -> EmitChild (2 + i) ch) |> Seq.toList
            ChIndex::arChildren
        let Choice_enm extFld = 
            let getPresence (ch:ChildInfo) =
                sprintf "%s = %s" (printPoint extFld) ch.Name.Value
            let EmitChild (i:int) (ch:ChildInfo) = EmitSeqOrChoiceChild i ch [] getPresence
            children |> Seq.mapi(fun i ch -> EmitChild (1 + i) ch) |> Seq.toList
        let Choice_presWhen() = 
            let getPresence (ch:ChildInfo) =
                let conds = Acn.GetPresenseConditions path ch acn
                let getPresenceSingle = function
                    | Acn.LikeUPER        -> ""
                    | Acn.PresBool(pnt)   -> sprintf "%s=true" (printPoint pnt)
                    | Acn.PresInt(pnt, v) -> sprintf "%s=%A" (printPoint pnt) v
                    | Acn.PresStr(pnt, v) -> sprintf "%s=%A" (printPoint pnt) v
                conds |> Seq.map getPresenceSingle |> Seq.StrJoin " AND " 
            let EmitChild (i:int) (ch:ChildInfo) = EmitSeqOrChoiceChild i ch [] getPresence
            children |> Seq.mapi(fun i ch -> EmitChild (1 + i) ch) |> Seq.toList
        let arrRows = 
            match Acn.GetChoiceEncodingClass path children acn with
            | Some(Acn.EnumDeterminant(extFld))  -> Choice_enm extFld
            | Some(Acn.PresentWhenOnChildren)   -> Choice_presWhen()
            | None                              -> Choice_like_uPER()
        icd_acn.EmitSequenceOrChoice color sTasName (ToC sTasName) hasAcnDef "CHOICE" sMinBytes sMaxBytes sMaxBitsExplained sCommentLine arrRows (myParams 6I) (sCommentLine.Split [|'\n'|])

    | OctetString   
    | NumericString   
    | IA5String   
    | BitString   
    | SequenceOf(_)  -> 
        let ChildRow (lineFrom:BigInteger) (i:BigInteger) =
            let sClass = if i % 2I = 0I then icd_uper.EvenRow() else icd_uper.OddRow()
            let nIndex = lineFrom + i
            let sFieldName = icd_acn.ItemNumber(i)
            let sComment = ""
            let sType, sAsn1Constraints, sMinBits, sMaxBits = 
                match t.Kind with
                | SequenceOf(child) ->
                    let ret = child.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin "" 
                    let ret = ( if ret.Trim() ="" then "N.A." else ret)
                    let sMaxBits, sMaxBytes = getAcnMax child (path@["#"]) r acn
                    let sMinBits, sMinBytes = getAcnMin child (path@["#"]) r acn
                    match child.Kind with
                    | ReferenceType(md,ts,_)   -> icd_uper.EmmitSeqChild_RefType ts.Value (ToC ts.Value), ret, sMinBits, sMaxBits
                    | _                        -> icdUper.Kind2Name child, ret, sMinBits, (sMaxBits+sMaxBitsExplained)
                | IA5String                    -> "ASCII CHARACTER", "", "8","8"
                | NumericString                -> "NUMERIC CHARACTER", "", "8","8"
                | OctetString                  -> "OCTET", "", "8", "8"
                | BitString                    -> "BIT", "", "1","1"
                | _                            -> raise(BugErrorException "")
            icd_uper.EmmitChoiceChild sClass nIndex sFieldName sComment  sType sAsn1Constraints sMinBits sMaxBits

        let nMax =
            match (uPER.GetTypeUperRange t.Kind t.Constraints  r) with
            | Concrete(_,b)                        -> b
            | PosInf(_)   | Full                   -> raise(BugErrorException "")
            | Empty                                -> 0I
            | NegInf(_)                            -> raise(BugErrorException "")
        let sFixedLengthComment = sprintf "Length is Fixed equal to %A, so no length determinant is encoded." nMax
        let arRows, sExtraComment =
            match Acn.GetSizeableEncodingClass t path r acn emptyLocation,  nMax>=2I with
            | Acn.FixedSize(nSize), true      -> (ChildRow 0I 1I)::(icd_uper.EmitRowWith3Dots())::(ChildRow 0I nMax)::[], sFixedLengthComment
            | Acn.FixedSize(nSize), false     -> (ChildRow 0I 1I)::[], sFixedLengthComment
            | Acn.AutoSize ,_                 ->
                let nLengthSize = match (uPER.GetTypeUperRange t.Kind t.Constraints  r) with
                                  | Concrete(a,b)                           -> (GetNumberOfBitsForNonNegativeInteger(b-a)) 
                                  | NegInf(_)  | PosInf(_) | Empty | Full   -> raise(BugErrorException "")
                let comment = "Special field used by ACN indicating the number of items."
                let ret = t.Constraints |> Seq.map PrintAsn1.PrintConstraint |> Seq.StrJoin "" 
                let sCon = ( if ret.Trim() ="" then "N.A." else ret)

                let lengthLine = icd_uper.EmmitChoiceChild (icd_uper.OddRow()) 1I "Length" comment    "unsigned int" sCon (nLengthSize.ToString()) (nLengthSize.ToString())
                match nLengthSize>0I,nMax>=2I with
                | true,true  -> lengthLine::(ChildRow 1I 1I)::(icd_uper.EmitRowWith3Dots())::(ChildRow 1I nMax)::[], ""
                | true,false -> lengthLine::(ChildRow 1I 1I)::[], ""
                | false, true-> (ChildRow 0I 1I)::(icd_uper.EmitRowWith3Dots())::(ChildRow 0I nMax)::[], sFixedLengthComment
                | false, false->(ChildRow 0I 1I)::[], sFixedLengthComment
            | Acn.ExternalField(fld), true    -> (ChildRow 0I 1I)::(icd_uper.EmitRowWith3Dots())::(ChildRow 0I nMax)::[], sprintf "Length determined by external field %s" (printPoint fld)
            | Acn.ExternalField(fld), false   -> (ChildRow 0I 1I)::[], sprintf "Length is determined by the external field: %s" (printPoint fld)

            | Acn.NullTerminated,_        -> [],""

        let sCommentLine = match sCommentLine with
                           | null | ""  -> sExtraComment
                           | _          -> sprintf "%s%s%s" sCommentLine (icd_uper.NewLine()) sExtraComment

        icd_acn.EmitSizeable color sTasName  (ToC sTasName) hasAcnDef (icdUper.Kind2Name t) sMinBytes sMaxBytes sMaxBitsExplained (makeEmptyNull sCommentLine) arRows (myParams 5I) (sCommentLine.Split [|'\n'|])




let PrintTas (tas:Ast.TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) blueTasses =
    let tasColor =
        match blueTasses |> Seq.exists (fun x -> x = tas.Name.Value) with
        |true   -> icd_uper.Blue ()
        |false  -> icd_uper.Orange ()
    icd_uper.EmmitTass (printType tas tas.Type [m.Name.Value; tas.Name.Value] m r acn tasColor) 


let PrintModule (m:Asn1Module) (f:Asn1File) (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  =
    let blueTasses = icdUper.getModuleBlueTasses m |> Seq.map snd
    let sortedTas = spark_spec.SortTypeAssigments m r acn
    let tases = sortedTas |> Seq.map (fun x -> PrintTas x m r acn blueTasses)
    let comments = []
    icd_uper.EmmitModule m.Name.Value comments tases

let PrintFile1 (f:Asn1File)  (r:AstRoot) (acn:AcnTypes.AcnAstResolved)  =
    let modules = f.Modules |> Seq.map (fun  m -> PrintModule m f r acn )  
    icd_uper.EmmitFile (Path.GetFileName f.FileName) modules 


// Generate a formatted version of the ACN grammar given as input,
// using the stringtemplate layouts.
let PrintFile3 (r:AstRoot) (acn:AcnTypes.AcnAstResolved) =
    let acnTokens = [|
            "endianness"; "big"; "little"; "encoding"; "pos-int"; "twos-complement"; "BCD"; "ASCII";
            "IEEE754-1985-32"; "IEEE754-1985-64"; "size"; "null-terminated"; "align-to-next"; "byte";
            "word"; "dword"; "encode-values"; "true-value"; "false-value"; "pattern"; "present-when";
            "determinant"; "DEFINITIONS"; "BEGIN"; "END"; "CONSTANT"; "NOT"; "INTEGER"; "BOOLEAN"; "NULL"|]
    let colorize (t: IToken, tasses: string array) =
            let lt = icd_acn.LeftDiple ()
            let gt = icd_acn.RightDiple ()
            let containedIn = Array.exists (fun elem -> elem = t.Text) 
            let isAcnKeyword = containedIn acnTokens //Antlr.Keywords.m_acnKeywords
            let isType = containedIn tasses
            let safeText = t.Text.Replace("<",lt).Replace(">",gt)
            let uid =
                match isType with
                |true -> icd_acn.TasName safeText (ToC safeText)
                |false -> safeText
            let colored =
                match t.Type with
                |acnLexer.StringLiteral
                |acnLexer.BitStringLiteral -> icd_acn.StringLiteral(safeText)
                |acnLexer.UID -> uid
                |acnLexer.COMMENT
                |acnLexer.COMMENT2 -> icd_acn.Comment safeText
                |_ -> safeText
            match isAcnKeyword with
                |true -> icd_acn.AcnKeyword(safeText)
                |false -> colored

    acn.Files |>
    Seq.map(fun (fName, tokens) -> 
            let f = r.Files |> Seq.find(fun x -> Path.GetFileNameWithoutExtension(x.FileName) = Path.GetFileNameWithoutExtension(fName))
            let tasNames = f.Modules |> Seq.collect(fun x -> x.TypeAssignments) |> Seq.map(fun x -> x.Name.Value) |> Seq.toArray
            let content = tokens |> Seq.map(fun token -> colorize(token,tasNames))
            icd_uper.EmmitFilePart2  (Path.GetFileName fName) (content |> Seq.StrJoin "")
    )


let DoWork (r:AstRoot) (acn:AcnTypes.AcnAstResolved) outDir =
    let files1 = r.Files |> Seq.map (fun f -> PrintFile1 f r acn) 
    let files2 = r.Files |> Seq.map icdUper.PrintFile2
    let files3 = PrintFile3 r acn
    let content = icd_acn.RootHtml files1 files2 (acn.Parameters |> Seq.exists(fun x->true)) files3
    File.WriteAllText(Path.Combine(outDir,r.IcdAcnHtmlFileName), content.Replace("\r",""))


