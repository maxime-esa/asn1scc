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

module AcnCreateFromAntlr

open System.Linq
open System.Numerics
open Antlr.Acn
open Antlr.Runtime.Tree
open Antlr.Runtime

open FsUtils


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ACN PRIVATE TYPES (NOT EXPOSED TO OTHER MODULES) /////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


type private GenericAcnPresentWhenCondition =
    | GP_PresenceBool  of Asn1AcnAst.RelativePath                         
    | GP_PresenceInt   of Asn1AcnAst.RelativePath*IntLoc
    | GP_PresenceStr   of Asn1AcnAst.RelativePath*StringLoc          
    
type private GenAcnEncodingProp =
    | GP_PosInt
    | GP_TwosComplement
    | GP_Ascii
    | GP_BCD
    | GP_IEEE754_32
    | GP_IEEE754_64

type private GenSizeProperty = 
    | GP_Fixed                 of IntLoc
    | GP_NullTerminated        
    | GP_SizeDeterminant       of Asn1AcnAst.RelativePath



type private GenericAcnProperty = 
    | ENCODING          of GenAcnEncodingProp
    | SIZE              of GenSizeProperty
    | ALIGNTONEXT       of Asn1AcnAst.AcnAligment
    | ENCODE_VALUES   
    | PRESENT_WHEN      of GenericAcnPresentWhenCondition list
    | TRUE_VALUE        of StringLoc
    | FALSE_VALUE       of StringLoc
    | PATTERN           of StringLoc
    | CHOICE_DETERMINANT of Asn1AcnAst.RelativePath
    | ENDIANNES         of Asn1AcnAst.AcnEndianness
    | ENUM_SET_VALUE    of IntLoc
    | TERMINATION_PATTERN of byte
    | MAPPING_FUNCTION  of StringLoc



type private AcnTypeEncodingSpec = {
    acnProperties   : GenericAcnProperty list
    children        : ChildSpec list
    loc             : SrcLoc
}

and private ChildSpec = {
    name            : StringLoc
    childEncodingSpec : AcnTypeEncodingSpec
    asn1Type        : Asn1AcnAst.AcnParamType option    // if present then it indicates an ACN inserted type
    argumentList    : Asn1AcnAst.RelativePath list
}

type private AcnTypeAssignment = {
    name            : StringLoc
    acnParameters   : Asn1AcnAst.AcnParameter list
    typeEncodingSpec: AcnTypeEncodingSpec
}

type private AcnModule = {
    name            : StringLoc
    typeAssignments : AcnTypeAssignment list
}


type private AcnFile = {
    antlrResult : ParameterizedAsn1Ast.AntlrParserResult
    modules     : AcnModule list
}

type private AcnAst = {
    files : AcnFile list
    acnConstants : Map<string, BigInteger>
}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// ACN CONSTANTS DEFINITION /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

type private AcnIntExpr =
    | IntegerExpr       of AcnIntegerConstant
    | SumExpr           of AcnIntExpr*AcnIntExpr
    | MinExpr           of AcnIntExpr*AcnIntExpr
    | MulExpr           of AcnIntExpr*AcnIntExpr
    | DivExpr           of AcnIntExpr*AcnIntExpr
    | ModExpr           of AcnIntExpr*AcnIntExpr
    | PowExpr           of AcnIntExpr*AcnIntExpr
    | UnMinExp          of AcnIntExpr

and private AcnIntegerConstant =
    | IntConst of IntLoc
    | RefConst of StringLoc       //reference to other constant

type private AcnConstant = {
    Name  : StringLoc
    Value : AcnIntExpr
}

let rec private EvaluateConstant (constants:AcnConstant list) intConstant =
    match intConstant with
    | IntConst(a)   -> a.Value
    | RefConst(consLookUp)  ->
        match constants |> Seq.tryFind(fun c-> c.Name.Value = consLookUp.Value) with
        |None       -> raise(SemanticError(consLookUp.Location, (sprintf "Unknown symbol '%s'" consLookUp.Value)))
        |Some(cn)   -> EvaluateAcnIntExpression constants cn.Value

and private  EvaluateAcnIntExpression (constants:AcnConstant list) acnExpr = 
    match  acnExpr with
    | IntegerExpr(consta)   -> EvaluateConstant constants consta
    | SumExpr(exp1,exp2)    -> (EvaluateAcnIntExpression constants exp1) + (EvaluateAcnIntExpression constants exp2)
    | MinExpr(exp1,exp2)    -> (EvaluateAcnIntExpression constants exp1) - (EvaluateAcnIntExpression constants exp2)
    | MulExpr(exp1,exp2)    -> (EvaluateAcnIntExpression constants exp1) * (EvaluateAcnIntExpression constants exp2)
    | DivExpr(exp1,exp2)    -> (EvaluateAcnIntExpression constants exp1) / (EvaluateAcnIntExpression constants exp2)
    | ModExpr(exp1,exp2)    -> (EvaluateAcnIntExpression constants exp1) % (EvaluateAcnIntExpression constants exp2)
    | PowExpr(exp1,exp2)    -> 
        System.Numerics.BigInteger.Pow(EvaluateAcnIntExpression constants exp1, int (EvaluateAcnIntExpression constants exp2))
    | UnMinExp(exp1)        -> -(EvaluateAcnIntExpression constants exp1) 


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// CONVERT ACN ANTL TO ACN PRIVATE TYPEA ////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



let private CreateLongField(t:ITree) = t.Children |> List.map(fun x -> x.Text) |> Asn1AcnAst.RelativePath

let private CreateAcnParamType (t:ITree) =
    match t.Type with
    | acnParser.INTEGER         -> Asn1AcnAst.AcnParamType.AcnPrmInteger t.Location
    | acnParser.BOOLEAN         -> Asn1AcnAst.AcnParamType.AcnPrmBoolean t.Location
    | acnParser.NULL            -> Asn1AcnAst.AcnParamType.AcnPrmNullType t.Location
    | acnParser.REFERENCED_TYPE -> 
        let mdName, tsName = 
            match t.Children with
            | first::[]             -> first.GetAncestor(acnParser.MODULE_DEF).GetChild(0).TextL,first.TextL
            | first::sec::[]        -> first.TextL,sec.TextL
            | _                     -> raise(BugErrorException("AcnCreateFromAntlr::CreateAcnAsn1Type 1"))
        Asn1AcnAst.AcnParamType.AcnPrmRefType(mdName, tsName)
    | _                         -> raise(BugErrorException("AcnCreateFromAntlr::CreateAcnAsn1Type 2"))



//Search in the antlr acn AST for a specific module, typeassigment and
//return the ACN parameters as a string list
let private GetParams (files:ParameterizedAsn1Ast.AntlrParserResult list) modName tasName  =
    let GetParamsAux (asn1File:ITree) =
        match  asn1File.Children |> Seq.tryFind(fun x -> x.GetChild(0).Text = modName)   with
        | None      -> []
        | Some(md)  ->
            match md.GetChildrenByType(acnParser.TYPE_ENCODING) |> Seq.tryFind(fun x -> x.GetChild(0).Text = tasName)   with
            | None  -> []
            | Some(tas) ->
                match tas.GetOptChild(acnParser.PARAM_LIST) with
                | None          -> []
                | Some(prmLst)  -> prmLst.Children |> List.map(fun p -> p.GetChild(1).Text)
    files |>  List.map (fun pr -> GetParamsAux pr.rootItem) |> List.collect(fun x -> x)


let private CreateNamedExpression (t:ITree) : AcnConstant= 
    let CreateAcnIntegerConstant  (t:ITree) = 
        match t.Type with
        | acnParser.INT                 -> IntConst(t.BigIntL)
        | acnParser.UID                 -> RefConst(t.TextL)
        | _                             -> raise(BugErrorException("AcnCreateFromAntlr::CreateAcnIntegerConstant"))
    let rec CreateExpression  (t:ITree) = 
        match t.Type with
        | acnParser.INT | acnParser.UID -> IntegerExpr(CreateAcnIntegerConstant  t)
        | acnParser.PLUS                -> SumExpr(CreateExpression  (t.GetChild(0)), CreateExpression  (t.GetChild(1)))
        | acnParser.MINUS               -> MinExpr(CreateExpression  (t.GetChild(0)), CreateExpression  (t.GetChild(1)))
        | acnParser.MULTIPLICATION      -> MulExpr(CreateExpression  (t.GetChild(0)), CreateExpression  (t.GetChild(1)))
        | acnParser.DIVISION            -> DivExpr(CreateExpression  (t.GetChild(0)), CreateExpression  (t.GetChild(1)))
        | acnParser.MODULO              -> ModExpr(CreateExpression  (t.GetChild(0)), CreateExpression  (t.GetChild(1)))
        | acnParser.POWER_SYMBOL        -> PowExpr(CreateExpression  (t.GetChild(0)), CreateExpression  (t.GetChild(1)))
        | acnParser.UNARY_MINUS         -> UnMinExp(CreateExpression (t.GetChild(0)))
        | _                             -> raise( BugErrorException("AcnCreateFromAntlr::CreateExpression Unsupported operator"))
    {AcnConstant.Name = t.GetChild(0).TextL;  Value = CreateExpression  (t.GetChild(1)) }


let private CheckCircularDependenciesInAcnConstants (constants : List<ITree>) =
    let HandleConstant (t:ITree) =
        let rec GetNamesFromExpr (t:ITree) =
            seq {
                match t.Type with
                | acnParser.INT                 -> ()
                | acnParser.UID                 -> yield t.TextL
                | acnParser.PLUS |acnParser.MINUS | acnParser.MULTIPLICATION | acnParser.DIVISION | acnParser.MODULO | acnParser.POWER_SYMBOL        -> 
                    yield! GetNamesFromExpr (t.GetChild(0))
                    yield! GetNamesFromExpr (t.GetChild(1))
                | acnParser.UNARY_MINUS         -> yield! GetNamesFromExpr (t.GetChild(0)) 
                | _                             -> raise(BugErrorException("CheckCircularDependenciesInAcnConstants.HandleConstant.GetNamesFromExpr Unsupported operator"))
                } |> Seq.toList
        (t.GetChild(0).TextL, GetNamesFromExpr (t.GetChild(1)))
    let constantsExpanded = constants |> List.map HandleConstant
    let independentConstants = constantsExpanded |> List.filter(fun (nm, lst) -> lst.IsEmpty ) |> List.map fst
    let dependentConstansts = constantsExpanded |> List.filter(fun (nm, lst) -> not (lst.IsEmpty) )
    let comparer (s1:StringLoc) (s2:StringLoc) = s1.Value = s2.Value
    let ExToThrow (cyclicDepds:List<StringLoc*List<StringLoc>>) = 
        match cyclicDepds with
        | []        -> raise(BugErrorException(""))
        | (x,_)::xs -> 
            let names = cyclicDepds |> Seq.map (fun (n,_) -> n.Value) |> Seq.StrJoin ", "
            SemanticError(x.Location, sprintf "Cyclic dependencies in ACN constants: %s" names)
    DoTopologicalSort2 independentConstants dependentConstansts comparer ExToThrow |> ignore


let private creareAcnProperty (acnConstants : Map<string, BigInteger>) (t:ITree) =
    let CreateAcnIntegerConstant  (t:ITree) = 
        match t.Type with
        | acnParser.INT                 -> t.BigIntL
        | acnParser.UID                 -> 
            match acnConstants.TryFind t.Text with
            | Some ret -> {IntLoc.Location = t.Location; Value=ret}
            | None     -> raise (SemanticError(t.Location, (sprintf "No ACN constant is defined with name '%s'" t.Text)))
        | _                             -> raise(BugErrorException("AcnCreateFromAntlr::CreateAcnIntegerConstant"))
    let GetActualString (str:string) = 
        let strVal = str.Substring(1)
        strVal.Remove(strVal.Length-2).Replace("\r", "").Replace("\n", "").Replace("\t", "").Replace(" ", "")

    match t.Type with
    | acnParser.ENCODING    ->
        match t.GetChild(0).Type with
        | acnParser.POS_INT             -> ENCODING GP_PosInt
        | acnParser.TWOSCOMPLEMENT      -> ENCODING GP_TwosComplement
        | acnParser.BCD                 -> ENCODING GP_Ascii
        | acnParser.ASCII               -> ENCODING GP_BCD
        | acnParser.IEEE754_1985_32     -> ENCODING GP_IEEE754_32
        | acnParser.IEEE754_1985_64     -> ENCODING GP_IEEE754_64
        | _                             -> raise(BugErrorException("creareAcnProperty_ENCODING"))
    | acnParser.SIZE    ->
        match t.GetChild(0).Type with
        | acnParser.NULL_TERMINATED     -> SIZE GP_NullTerminated
        | acnParser.INT                 
        | acnParser.UID                 -> SIZE (GP_Fixed (CreateAcnIntegerConstant (t.GetChild 0)))    
        | acnParser.LONG_FIELD          -> SIZE (GP_SizeDeterminant (CreateLongField (t.GetChild 0)))
        | _                             -> raise(BugErrorException("creareAcnProperty_SIZE"))
    | acnParser.ALIGNTONEXT ->
        match t.GetChild(0).Type with 
        | acnParser.BYTE                -> ALIGNTONEXT Asn1AcnAst.NextByte
        | acnParser.WORD                -> ALIGNTONEXT Asn1AcnAst.NextWord
        | acnParser.DWORD               -> ALIGNTONEXT Asn1AcnAst.NextDWord
        | _                             -> raise(BugErrorException("creareAcnProperty_ALIGNTONEXT"))
    | acnParser.ENCODE_VALUES           -> ENCODE_VALUES
    | acnParser.PRESENT_WHEN            -> 
        let CreateAcnPresenseCondition(t:ITree) = 
            match t.Type with
            | acnParser.LONG_FIELD  -> GP_PresenceBool(CreateLongField t)
            | acnParser.EQUAL       -> GP_PresenceInt ((CreateLongField(t.GetChild 0)), CreateAcnIntegerConstant (t.GetChild 1))
            | acnParser.PRESENT_WHEN_STR_EQUAL -> GP_PresenceStr ((CreateLongField(t.GetChild 0)), (t.GetChild 1).TextL )
            | _                     -> raise(BugErrorException("creareAcnProperty_PRESENT_WHEN"))
        PRESENT_WHEN (t.Children |> List.map CreateAcnPresenseCondition )

    | acnParser.TRUE_VALUE              -> 
        let v = { StringLoc.Value = GetActualString(t.GetChild(0).Text); Location = t.GetChild(0).Location}
        TRUE_VALUE v
    | acnParser.FALSE_VALUE             -> 
        let v = { StringLoc.Value = GetActualString(t.GetChild(0).Text); Location = t.GetChild(0).Location}
        FALSE_VALUE v
    | acnParser.PATTERN                 -> 
        let v = { StringLoc.Value = GetActualString(t.GetChild(0).Text); Location = t.GetChild(0).Location}
        PATTERN v
    | acnParser.DETERMINANT             -> CHOICE_DETERMINANT (CreateLongField(t.GetChild 0))
    | acnParser.ENDIANNES               -> 
        match t.GetChild(0).Type with 
        | acnParser.BIG                 -> ENDIANNES Asn1AcnAst.BigEndianness
        | acnParser.LITTLE              -> ENDIANNES Asn1AcnAst.LittleEndianness
        | _                             -> raise(BugErrorException("creareAcnProperty_ENDIANNES"))
    | acnParser.MAPPING_FUNCTION        -> MAPPING_FUNCTION (t.GetChild(0).TextL)
    | acnParser.INT                     -> ENUM_SET_VALUE t.BigIntL
    | acnParser.TERMINATION_PATTERN     -> 
        let tp = t
        let bitPattern = GetActualString (tp.GetChild(0).Text)
        match tp.GetChild(0).Type with
        | acnParser.BitStringLiteral    ->
            match bitPattern.Length <> 8 with
            | true  -> raise(SemanticError(tp.Location, sprintf "ternination-patern value must be a byte"  ))
            | false ->
                let byteVal = 
                    bitPattern.ToCharArray() |> 
                    Seq.fold(fun (p,cs) c -> if c='0' then (p/2,cs) else (p/2,p+cs) ) (128, 0) 
                    |> snd |> byte
                TERMINATION_PATTERN byteVal
        | acnParser.OctectStringLiteral ->
            match bitPattern.Length <> 2 with
            | true  -> raise(SemanticError(tp.Location, sprintf "ternination-patern value must be a byte"  ))
            | false ->
                TERMINATION_PATTERN (System.Byte.Parse(bitPattern, System.Globalization.NumberStyles.AllowHexSpecifier))
        | _     ->  raise(BugErrorException("creareAcnProperty_TERMINATION_PATTERN"))
    | _                             -> raise(BugErrorException("creareAcnProperty"))

let rec  private createTypeEncodingSpec (allAcnFiles: ParameterizedAsn1Ast.AntlrParserResult list) (acnConstants : Map<string, BigInteger>) (thisAcnFile: ParameterizedAsn1Ast.AntlrParserResult)  (encSpecITree:ITree) : AcnTypeEncodingSpec =
    let acnProperties = 
        match encSpecITree.GetOptChild(acnParser.ENCODING_PROPERTIES) with
        | None              -> []
        | Some(propList)    -> propList.Children |> List.map (creareAcnProperty acnConstants)
    
    let children = 
        match encSpecITree.GetOptChild(acnParser.CHILDREN_ENC_SPEC) with
        | None              -> []
        | Some childrenList ->
            let createChild (t:ITree) =
                let name  = 
                    match t.GetOptChild(acnParser.LID) with
                    | None          -> StringLoc.ByValue "#"
                    | Some(lid)     -> lid.TextL
                let argumentList    =
                        match t.GetOptChild(acnParser.ARGUMENTS) with
                        | None            -> []
                        | Some(argList)   -> argList.Children |> List.map CreateLongField
                let childEncodingSpec = createTypeEncodingSpec allAcnFiles acnConstants thisAcnFile (t.GetChildByType acnParser.ENCODING_SPEC) 
                let asn1Type  =
                    match t.Type with
                    | acnParser.CHILD       -> None
                    | acnParser.CHILD_NEW   -> Some (CreateAcnParamType (t.GetChild 1) ) 
                    | _     ->  raise(BugErrorException("createTypeEncodingSpec_CHILD"))

                {ChildSpec.name = name; childEncodingSpec= childEncodingSpec; asn1Type=asn1Type; argumentList=argumentList}
            childrenList.Children |> List.map createChild
    {AcnTypeEncodingSpec.acnProperties = acnProperties; children = children; loc = encSpecITree.Location}

let private CreateTypeAssignment (allAcnFiles: ParameterizedAsn1Ast.AntlrParserResult list) (acnConstants : Map<string, BigInteger>) (thisAcnFile: ParameterizedAsn1Ast.AntlrParserResult)  (tasTree:ITree) : AcnTypeAssignment =
    let tasNameL = tasTree.GetChildByType(acnParser.UID).TextL

    let encSpecITree = tasTree.GetChildByType(acnParser.ENCODING_SPEC)
    let prms = 
        match tasTree.GetOptChild(acnParser.PARAM_LIST) with
        | None -> []
        | Some(paramList) -> 
            let CreateParam (x:ITree) =
                let prmName = x.GetChild(1).Text
                let loc = x.GetChild(1).Location
                //check that all parameters are used
                let refs = encSpecITree.AllChildren |> List.filter(fun x -> x.Type = acnParser.LONG_FIELD && x.ChildCount=1) |> List.map(fun x -> x.GetChild(0).Text)
                match refs |> Seq.tryFind(fun x -> x = prmName) with
                | Some(_)   -> {Asn1AcnAst.AcnParameter.name = prmName; Asn1AcnAst.AcnParameter.asn1Type=CreateAcnParamType (x.GetChild(0)) ; Asn1AcnAst.AcnParameter.loc = loc}
                | None      -> raise(SemanticError(loc, sprintf "unreferenced parameter '%s'" prmName))
            paramList.Children |> List.map CreateParam

    let typeEncodingSpec = createTypeEncodingSpec allAcnFiles acnConstants thisAcnFile encSpecITree
    {AcnTypeAssignment.name = tasNameL; acnParameters = prms; typeEncodingSpec = typeEncodingSpec}


let private CreateModule (allAcnFiles: ParameterizedAsn1Ast.AntlrParserResult list) (acnConstants : Map<string, BigInteger>) (thisAcnFile: ParameterizedAsn1Ast.AntlrParserResult)   (modTree : ITree) : AcnModule =
    let modNameL = modTree.GetChildByType(acnParser.UID).TextL

    let tasITreeList = modTree.GetChildrenByType(acnParser.TYPE_ENCODING)
    
    //check for duplicate type assignments in the ACN module
    tasITreeList |> List.map(fun x -> x.GetChildByType(acnParser.UID).TextL) |> CheckForDuplicates

    let newTasses = tasITreeList |> List.map(fun tasTree -> CreateTypeAssignment allAcnFiles acnConstants thisAcnFile tasTree) 
    
    {AcnModule.name = modNameL; typeAssignments = newTasses}


let private LoadAcnFile (allAcnFiles: ParameterizedAsn1Ast.AntlrParserResult list) (acnConstants : Map<string, BigInteger>) (thisAcnFile: ParameterizedAsn1Ast.AntlrParserResult)   : AcnFile = 
    let modules = thisAcnFile.rootItem.Children |> List.map (CreateModule allAcnFiles acnConstants thisAcnFile)
    {AcnFile.antlrResult = thisAcnFile; modules = modules}

let private CreateAcnAst (allAcnFiles: ParameterizedAsn1Ast.AntlrParserResult list) : AcnAst =  
    ITree.RegisterFiles(allAcnFiles|> Seq.map(fun pr -> (pr.rootItem, pr.fileName)))
    let constants = seq {
        for acnFile in allAcnFiles do
            for m in acnFile.rootItem.Children do
                for c in m.GetChildrenByType(acnParser.CONSTANT) do
                    yield c } |> Seq.toList

    let constantNames = constants |> List.map(fun c -> c.GetChild(0).TextL)

    // check that all constant names are unique
    constantNames |> CheckForDuplicates 

    CheckCircularDependenciesInAcnConstants constants

    let constantValues = constants |> List.map CreateNamedExpression  
    let acnConstantsMap = constantValues |> List.map(fun c -> c.Name.Value, EvaluateAcnIntExpression constantValues c.Value) |> Map.ofList

    let acnFiles = allAcnFiles |> List.map (LoadAcnFile allAcnFiles acnConstantsMap)
    {AcnAst.files = acnFiles; acnConstants = acnConstantsMap}


let private tryFindAcnTypeByName modName tasName (r:AcnAst) =
    match r.files |> List.collect (fun f -> f.modules) |> Seq.tryFind(fun m -> m.name = modName) with
    | None  -> None
    | Some m-> m.typeAssignments |> Seq.tryFind (fun t -> t.name = tasName)


open Asn1AcnAst

let private tryGetProp (props:GenericAcnProperty list) fnPropKind = 
    match props |> List.choose fnPropKind  with
    | e::_  -> Some e
    | _     -> None

let private  getEndianessProperty (props:GenericAcnProperty list) = 
    tryGetProp props (fun x -> match x with ENDIANNES e -> Some e | _ -> None)  


let private getIntSizeProperty errLoc (props:GenericAcnProperty list) = 
    match tryGetProp props (fun x -> match x with SIZE e -> Some e | _ -> None) with
    | None  -> None
    | Some (GP_Fixed           v)   -> Some(Fixed v)
    | Some (GP_NullTerminated   )   -> 
        match tryGetProp props (fun x -> match x with TERMINATION_PATTERN e -> Some e | _ -> None) with
        | Some b    -> Some(IntNullTerminated b)
        | None      -> Some(IntNullTerminated (byte 0))
    | Some (GP_SizeDeterminant _)   -> raise(SemanticError(errLoc ,"The size property was expected to be a fixed integer or null-terminated"))

let private getStringSizeProperty errLoc (props:GenericAcnProperty list) = 
    match tryGetProp props (fun x -> match x with SIZE e -> Some e | _ -> None) with
    | None  -> None
    | Some (GP_Fixed           v)   -> raise(SemanticError(errLoc ,"The size property was expected to be a fixed integer or null-terminated"))
    | Some (GP_NullTerminated   )   -> 
        match tryGetProp props (fun x -> match x with TERMINATION_PATTERN e -> Some e | _ -> None) with
        | Some b    -> Some(StrNullTerminated b)
        | None      -> Some(StrNullTerminated (byte 0))
    | Some (GP_SizeDeterminant fld)   -> (Some (StrExternalField fld))

let private getSizeableSizeProperty errLoc (props:GenericAcnProperty list) = 
    match tryGetProp props (fun x -> match x with SIZE e -> Some e | _ -> None) with
    | None  -> None
    | Some (GP_Fixed           _)   
    | Some (GP_NullTerminated   )   -> raise(SemanticError(errLoc ,"The size property was expected to be a fixed integer or null-terminated"))
    | Some (GP_SizeDeterminant fld)   -> (Some fld)

let private getIntEncodingProperty errLoc (props:GenericAcnProperty list) = 
    match tryGetProp props (fun x -> match x with ENCODING e -> Some e | _ -> None) with
    | None  -> None
    | Some (GP_PosInt         ) ->  Some (PosInt)
    | Some (GP_TwosComplement ) ->  Some (TwosComplement)
    | Some (GP_Ascii          ) ->  Some (IntAscii)
    | Some (GP_BCD            ) ->  Some (BCD)        
    | Some (GP_IEEE754_32     ) 
    | Some (GP_IEEE754_64     ) ->   raise(SemanticError(errLoc ,"The encoding property was expected to be one of 'pos-int','twos-complement','BCD' or 'ASCII' "))

let private getRealEncodingProperty errLoc (props:GenericAcnProperty list) = 
    match tryGetProp props (fun x -> match x with ENCODING e -> Some e | _ -> None) with
    | None  -> None
    | Some (GP_PosInt         ) 
    | Some (GP_TwosComplement ) 
    | Some (GP_Ascii          ) 
    | Some (GP_BCD            ) ->  raise(SemanticError(errLoc ,"The encoding property was expected to be one of 'pos-int','twos-complement','BCD' or 'ASCII' "))
    | Some (GP_IEEE754_32     ) ->  Some (IEEE754_32)
    | Some (GP_IEEE754_64     ) ->  Some (IEEE754_64) 

let private getStringEncodingProperty errLoc (props:GenericAcnProperty list) = 
    match tryGetProp props (fun x -> match x with ENCODING e -> Some e | _ -> None) with
    | None  -> None
    | Some (GP_PosInt         ) 
    | Some (GP_TwosComplement ) 
    | Some (GP_IEEE754_32     ) 
    | Some (GP_IEEE754_64     ) 
    | Some (GP_BCD            ) ->  raise(SemanticError(errLoc ,"The encoding property was expected to be 'ASCII' or empty"))
    | Some (GP_Ascii          ) -> Some (StrAscii)

let private mergeInteger (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints=
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    ->
            {
                IntegerAcnProperties.encodingProp    = getIntEncodingProperty acnErrLoc props
                sizeProp                             = getIntSizeProperty acnErrLoc props
                endiannessProp                       = getEndianessProperty props
            }
        | None  -> {IntegerAcnProperties.encodingProp = None; sizeProp = None; endiannessProp = None }
    {Integer.acnProperties = acnProperties; constraints = constraints}

let private mergeReal (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints=
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    ->
            {
                RealAcnProperties.encodingProp    = getRealEncodingProperty acnErrLoc props
                endiannessProp                    = getEndianessProperty props
            }
        | None  -> {RealAcnProperties.encodingProp = None; endiannessProp = None }
    {Real.acnProperties = acnProperties; constraints = constraints}

let private mergeStringType (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints=
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    ->
            {
                StringAcnProperties.encodingProp    = getStringEncodingProperty acnErrLoc props
                sizeProp                            = getStringSizeProperty acnErrLoc props
            }
        | None  -> {StringAcnProperties.encodingProp = None; sizeProp = None }
    {StringType.acnProperties = acnProperties; constraints = constraints}

let private mergeOctetStringType (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints =
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    -> { SizeableAcnProperties.sizeProp  = getSizeableSizeProperty acnErrLoc props}
        | None              -> {SizeableAcnProperties.sizeProp = None }
    {OctetString.acnProperties = acnProperties; constraints = constraints}

let private mergeBitStringType (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints =
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    -> { SizeableAcnProperties.sizeProp  = getSizeableSizeProperty acnErrLoc props}
        | None              -> {SizeableAcnProperties.sizeProp = None }
    {BitString.acnProperties = acnProperties; constraints = constraints}

let private mergeNullType (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints =
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    -> { NullTypeAcnProperties.encodingPattern  = tryGetProp props (fun x -> match x with PATTERN e -> Some e | _ -> None)}
        | None              -> {NullTypeAcnProperties.encodingPattern = None }
    {NullType.acnProperties = acnProperties; constraints = constraints}

let private mergeBooleanType (acnErrLoc: SrcLoc option) (props:GenericAcnProperty list) constraints =
    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    -> 
            match tryGetProp props (fun x -> match x with TRUE_VALUE e -> Some e | _ -> None) with
            | Some tv   ->  {BooleanAcnProperties.encodingPattern  = Some (TrueValue tv)}
            | None      ->
                match tryGetProp props (fun x -> match x with FALSE_VALUE e -> Some e | _ -> None) with
                | Some tv   ->  {BooleanAcnProperties.encodingPattern  = Some (FalseValue tv)}
                | None      ->  {BooleanAcnProperties.encodingPattern  = None}
        | None              -> {BooleanAcnProperties.encodingPattern = None }
    {Boolean.acnProperties = acnProperties; constraints = constraints}




let private mergeEnumerated (asn1:Asn1Ast.AstRoot) (items: Asn1Ast.NamedItem list) (acnErrLoc: SrcLoc option) (acnType:AcnTypeEncodingSpec option) (props:GenericAcnProperty list) constraints =
    let allocatedValuesToAllEnumItems (namedItems:Asn1Ast.NamedItem list) (ast:Asn1Ast.AstRoot) = 
        let createAsn1ValueByBigInt biVal = {Asn1Ast.Asn1Value.Kind = Asn1Ast.IntegerValue (IntLoc.ByValue biVal); Asn1Ast.Location = emptyLocation}
        let allocated   = namedItems |> List.filter(fun x -> x._value.IsSome)
        let unallocated = namedItems |> List.filter(fun x -> x._value.IsNone)
        let rec allocateItems (unallocated:Asn1Ast.NamedItem list) (allocated:Asn1Ast.NamedItem list) potentialValue: Asn1Ast.NamedItem list =
            match unallocated with
            | []    -> allocated
            |x::xs  -> 
                let rec getValue (allocated:Asn1Ast.NamedItem list) (vl:BigInteger) =
                    match allocated |> Seq.exists(fun ni -> match ni._value with Some value -> vl = (Asn1Ast.GetValueAsInt value ast) | None -> false) with
                    | false -> vl
                    | true  -> getValue allocated (vl + 1I)
                let vl = getValue allocated potentialValue
                let newAllocatedItems = allocated@[{x with _value = Some (createAsn1ValueByBigInt vl)} ]
                allocateItems xs newAllocatedItems (vl + 1I)
        let newItems = allocateItems unallocated allocated 0I |> List.sortBy(fun ni -> namedItems |> Seq.findIndex(fun x -> x.Name.Value = ni.Name.Value) )
        newItems
    let mapItem (i:int) (itm:Asn1Ast.NamedItem) =
        let definitionValue = Asn1Ast.GetValueAsInt itm._value.Value asn1
        match acnType with
        | None  ->
            let acnEncodeValue = (BigInteger i)
            {NamedItem.Name = itm.Name; Comments = itm.Comments; c_name = itm.c_name; ada_name = itm.ada_name; definitionValue = definitionValue; acnEncodeValue = acnEncodeValue}        
        | Some acnType ->
            let acnEncodeValue = 
                match tryGetProp props (fun x -> match x with ENCODE_VALUES -> Some true | _ -> None) with
                | Some _    -> (BigInteger i)
                | None      -> definitionValue
            {NamedItem.Name = itm.Name; Comments = itm.Comments; c_name = itm.c_name; ada_name = itm.ada_name; definitionValue = definitionValue; acnEncodeValue = acnEncodeValue}        

    let acnProperties = 
        match acnErrLoc with
        | Some acnErrLoc    ->
            {
                IntegerAcnProperties.encodingProp    = getIntEncodingProperty acnErrLoc props
                sizeProp                             = getIntSizeProperty acnErrLoc props
                endiannessProp                       = getEndianessProperty props
            }
        | None  -> {IntegerAcnProperties.encodingProp = None; sizeProp = None; endiannessProp = None }
    {Enumerated.acnProperties = acnProperties; items=items|> List.mapi mapItem; constraints = constraints}

let rec private mergeAcnEncodingSpecs (thisType:AcnTypeEncodingSpec option) (baseType:AcnTypeEncodingSpec option) =
    match thisType, baseType with
    | None, None    -> None
    | None, Some x -> Some x
    | Some x, None -> Some x
    | Some thisType, Some baseType ->
        let mergedProperties = thisType.acnProperties@baseType.acnProperties
        let mergedChildren =
            let thisTypeNames = thisType.children |> List.map(fun x -> x.name)
            let baseTypeNames = baseType.children |> List.map(fun x -> x.name)
            let combinedNames = thisTypeNames@baseTypeNames |> Seq.distinctBy(fun x -> x.Value) |> Seq.toList
            combinedNames |> 
                List.choose(fun nm ->
                    let e1 = thisType.children |> Seq.tryFind(fun x -> x.name = nm)
                    let e2 = baseType.children |> Seq.tryFind(fun x -> x.name = nm)
                    match e1, e2 with
                    | None, None    -> None
                    | None, Some x  -> Some x
                    | Some x, None  -> Some x
                    | Some thisChild, Some baseChild    ->
                        match mergeAcnEncodingSpecs (Some thisChild.childEncodingSpec) (Some baseChild.childEncodingSpec) with
                        | Some combinedEncoingSpec  ->
                            Some ({name = nm; childEncodingSpec = combinedEncoingSpec; asn1Type = thisChild.asn1Type; argumentList = thisChild.argumentList})
                        | None                      -> None)

        Some {AcnTypeEncodingSpec.acnProperties = mergedProperties; children = mergedChildren; loc = thisType.loc}        

(*
    match asn1Type with
    | AcnTypes.Integer   -> {Asn1Type.Kind = Ast.Integer; Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
    | AcnTypes.Boolean   -> {Asn1Type.Kind = Ast.Boolean; Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
    | AcnTypes.NullType  -> {Asn1Type.Kind = Ast.NullType; Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}
    | AcnTypes.RefTypeCon(md,ts)  -> {Asn1Type.Kind = Ast.ReferenceType(md,ts, false); Constraints=[]; Location=emptyLocation; AcnProperties=acnChild.Properties}

*)

let rec private mapAcnParamTypeToAcnAcnInsertedType (asn1:Asn1Ast.AstRoot) (acn:AcnAst) (p:AcnParamType) (props:GenericAcnProperty list) =
    let  acnAligment     = tryGetProp props (fun x -> match x with ALIGNTONEXT e -> Some e | _ -> None)
    match p with
    | AcnPrmInteger acnErrLoc -> 
        let acnProperties = {IntegerAcnProperties.encodingProp = getIntEncodingProperty acnErrLoc props; sizeProp = getIntSizeProperty acnErrLoc props; endiannessProp = getEndianessProperty props}
        AcnInteger (acnProperties, acnAligment)
    | AcnPrmBoolean  acnErrLoc ->
        let acnProperties = 
            match tryGetProp props (fun x -> match x with TRUE_VALUE e -> Some e | _ -> None) with
            | Some tv   ->  {BooleanAcnProperties.encodingPattern  = Some (TrueValue tv)}
            | None      ->
                match tryGetProp props (fun x -> match x with FALSE_VALUE e -> Some e | _ -> None) with
                | Some tv   ->  {BooleanAcnProperties.encodingPattern  = Some (FalseValue tv)}
                | None      ->  {BooleanAcnProperties.encodingPattern  = None}
        AcnBoolean (acnProperties, acnAligment)
    | AcnPrmNullType acnErrLoc ->
        let acnProperties = { NullTypeAcnProperties.encodingPattern  = tryGetProp props (fun x -> match x with PATTERN e -> Some e | _ -> None)}
        AcnNullType (acnProperties, acnAligment)
    | AcnPrmRefType (md,ts)->
        let newParma  = 
            match (Asn1Ast.GetBaseTypeByName md ts asn1).Kind with
            | Asn1Ast.Integer           -> AcnPrmInteger ts.Location
            | Asn1Ast.NullType          -> AcnPrmNullType ts.Location
            | Asn1Ast.Boolean           -> AcnPrmBoolean ts.Location
            | Asn1Ast.ReferenceType rf  -> AcnPrmRefType (rf.modName, rf.tasName)
            | _                         -> raise(SemanticError(ts.Location, "Invalid type for ACN inserted type"))
        let baseTypeAcnProps =
            match tryFindAcnTypeByName md ts acn with
            | None      -> []
            | Some x    -> x.typeEncodingSpec.acnProperties
        mapAcnParamTypeToAcnAcnInsertedType asn1 acn newParma (props@baseTypeAcnProps)

let rec private mergeType (asn1:Asn1Ast.AstRoot) (acn:AcnAst) (m:Asn1Ast.Asn1Module) (t:Asn1Ast.Asn1Type) 
                           (acnType:AcnTypeEncodingSpec option) 
                           (extraCons:Asn1Ast.Asn1Constraint list)      // constraints from reference types, with components etc
                           (acnArgs : Asn1AcnAst.RelativePath list): Asn1Type=
    let acnProps =
        match acnType with
        | None      -> []
        | Some x    -> x.acnProperties
    let acnErrLoc = acnType |> Option.map(fun x -> x.loc)
    let combinedProperties = acnProps
    //let withCompCons = (t.Constraints@witchCompsCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentConstraint _ -> Some c| Asn1Ast.WithComponentsConstraint _ -> Some c | _ -> None)

    let asn1Kind =
        match t.Kind with
        | Asn1Ast.Integer                  -> 
            let constraints = []
            Integer (mergeInteger acnErrLoc combinedProperties constraints)
        | Asn1Ast.Real                     -> 
            let constraints = []
            Real (mergeReal acnErrLoc combinedProperties constraints)
        | Asn1Ast.IA5String                ->  
            let constraints = []
            IA5String (mergeStringType acnErrLoc combinedProperties constraints)
        | Asn1Ast.NumericString            ->  
            let constraints = []
            NumericString (mergeStringType acnErrLoc combinedProperties constraints)
        | Asn1Ast.OctetString              ->  
            let constraints = []
            OctetString(mergeOctetStringType acnErrLoc combinedProperties constraints)
        | Asn1Ast.BitString                ->  
            let constraints = []
            BitString(mergeBitStringType acnErrLoc combinedProperties constraints)
        | Asn1Ast.NullType                 ->  
            let constraints = []
            NullType(mergeNullType acnErrLoc combinedProperties constraints)
        | Asn1Ast.Boolean                  ->  
            let constraints = []
            Boolean(mergeBooleanType acnErrLoc combinedProperties constraints)
        | Asn1Ast.Enumerated  items        ->  
            let constraints = []
            Enumerated (mergeEnumerated asn1 items acnErrLoc acnType combinedProperties constraints)
        | Asn1Ast.SequenceOf  chType       -> 
            let withCompCons = (t.Constraints@extraCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentConstraint w -> Some w| _ -> None)
            let noWithCompCons = (t.Constraints@extraCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentConstraint _ -> None | _ -> Some c)
            let constraints = []
            let childEncSpec, acnArgs = 
                match acnType with
                | None          -> None, []
                | Some acnType  -> 
                    match acnType.children with
                    | []    -> None, []
                    | c1::_ -> Some c1.childEncodingSpec, c1.argumentList
            let newChType = mergeType asn1 acn m chType childEncSpec withCompCons acnArgs
            let acnProperties = 
                match acnErrLoc with
                | Some acnErrLoc    -> { SizeableAcnProperties.sizeProp  = getSizeableSizeProperty acnErrLoc combinedProperties}
                | None              -> {SizeableAcnProperties.sizeProp = None }

            let newKind = {SequenceOf.child=newChType; acnProperties   = acnProperties; constraints = constraints}
            SequenceOf newKind
        | Asn1Ast.Sequence    children     -> 
            let nameConstraints = (t.Constraints@extraCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentsConstraint w -> Some w| _ -> None) |> List.collect id
            let noWithCompCons = (t.Constraints@extraCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentsConstraint _ -> None | _ -> Some c)

            let mergeChild (cc:ChildSpec option) (c:Asn1Ast.ChildInfo)  =
                let childNamedConstraints = nameConstraints |> List.filter(fun x -> x.Name = c.Name)
                let withCompCons = childNamedConstraints |> List.choose(fun nc -> nc.Contraint)
                let aa = 
                    childNamedConstraints |> 
                    List.choose(fun nc -> 
                        match nc.Mark with
                        | Asn1Ast.NoMark            -> None
                        | Asn1Ast.MarkPresent       -> Some Asn1Ast.AlwaysAbsent
                        | Asn1Ast.MarkAbsent        -> Some Asn1Ast.AlwaysAbsent
                        | Asn1Ast.MarkOptional      -> Some Asn1Ast.Optional)
                let acnPresentWhenConditions = 
                    match cc with
                    | None      -> []
                    | Some cc   -> 
                        match tryGetProp cc.childEncodingSpec.acnProperties (fun x -> match x with PRESENT_WHEN e -> Some e | _ -> None) with
                        | None      -> []
                        | Some lst  -> lst |> List.choose(fun gp -> match gp with GP_PresenceBool l -> Some (PresenceBool l) | _ -> None)
                match cc with
                | None      ->  
                    let newChild = mergeType asn1 acn m c.Type None withCompCons []
                    Asn1Child ({Asn1Child.Name = c.Name; c_name = c.c_name; ada_name = c.ada_name; Type  = newChild; Optionality = c.Optionality;acnPresentWhenConditions = acnPresentWhenConditions; Comments = c.Comments})
                | Some cc   ->
                    match cc.asn1Type with
                    | None  -> 
                        let newChild = mergeType asn1 acn m c.Type (Some cc.childEncodingSpec) withCompCons cc.argumentList
                        Asn1Child ({Asn1Child.Name = c.Name; c_name = c.c_name; ada_name = c.ada_name; Type  = newChild; Optionality = c.Optionality;acnPresentWhenConditions = acnPresentWhenConditions; Comments = c.Comments})
                    | Some xx  ->
                        AcnChild({AcnChild.Name = c.Name; Type = mapAcnParamTypeToAcnAcnInsertedType asn1 acn xx cc.childEncodingSpec.acnProperties})

            let mergedChildren = 
                match acnType with
                | None            -> children |> List.map (mergeChild None)
                | Some acnEncSpec ->
                    match acnEncSpec.children with
                    | []            -> children |> List.map (mergeChild None)
                    | acnChildren   ->
                        // MAKE SURE ACN CHILDREN ARE SUPERSET OF ASN1 CHILDREN !!!!!
                        acnChildren |>
                        List.map(fun acnChild ->
                            match children |> Seq.tryFind (fun a -> a.Name = acnChild.name) with
                            | Some x -> mergeChild (Some acnChild) x
                            | None   -> raise(SemanticError(acnChild.name.Location, (sprintf "invalid name %s" acnChild.name.Value))))
            Sequence ({Sequence.children = mergedChildren;    constraints = []})
        | Asn1Ast.Choice      children     -> 
            let nameConstraints = (t.Constraints@extraCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentsConstraint w -> Some w| _ -> None) |> List.collect id
            let noWithCompCons = (t.Constraints@extraCons) |> List.choose(fun c -> match c with Asn1Ast.WithComponentsConstraint _ -> None | _ -> Some c)
            
            let mergeChild (cc:ChildSpec option) (c:Asn1Ast.ChildInfo)  =
                let childNamedConstraints = nameConstraints |> List.filter(fun x -> x.Name = c.Name)
                let withCompCons = childNamedConstraints |> List.choose(fun nc -> nc.Contraint)
                let acnPresentWhenConditions = 
                    match cc with
                    | None      -> []
                    | Some cc   -> 
                        match tryGetProp cc.childEncodingSpec.acnProperties (fun x -> match x with PRESENT_WHEN e -> Some e | _ -> None) with
                        | None      -> []
                        | Some lst  -> 
                            lst |> 
                            List.choose(fun gp -> 
                                match gp with 
                                | GP_PresenceInt (p,v) -> Some (PresenceInt (p,v)) 
                                | GP_PresenceStr (p,v) -> Some (PresenceStr (p,v)) 
                                | _ -> None)
                match cc with
                | None      ->  
                    let newChild = mergeType asn1 acn m c.Type None withCompCons []
                    {ChChildInfo.Name = c.Name; c_name = c.c_name; ada_name = c.ada_name; Type  = newChild; acnPresentWhenConditions = acnPresentWhenConditions; Comments = c.Comments;present_when_name = c.present_when_name}
                | Some cc   ->
                    let newChild = mergeType asn1 acn m c.Type (Some cc.childEncodingSpec) withCompCons cc.argumentList
                    {ChChildInfo.Name = c.Name; c_name = c.c_name; ada_name = c.ada_name; Type  = newChild; acnPresentWhenConditions = acnPresentWhenConditions; Comments = c.Comments; present_when_name = c.present_when_name}
            let mergedChildren = 
                match acnType with
                | None            -> children |> List.map (mergeChild None)
                | Some acnEncSpec ->
                    match acnEncSpec.children with
                    | []            -> children |> List.map (mergeChild None)
                    | acnChildren   ->
                        // MAKE SURE ACN CHILDREN ARE THE SAME OF ASN1 CHILDREN !!!!!
                        acnChildren |>
                        List.map(fun acnChild ->
                            match children |> Seq.tryFind (fun a -> a.Name = acnChild.name) with
                            | Some x -> mergeChild (Some acnChild) x
                            | None   -> raise(SemanticError(acnChild.name.Location, (sprintf "invalid name %s" acnChild.name.Value))))
            let acnProperties = 
                {ChoiceAcnProperties.enumDeterminant = tryGetProp combinedProperties (fun x -> match x with CHOICE_DETERMINANT e -> Some e | _ -> None)}
            Choice ({Choice.children = mergedChildren; acnProperties = acnProperties;   constraints = []})
        | Asn1Ast.ReferenceType rf    -> 
            let acnArguments = acnArgs
            let oldBaseType  = Asn1Ast.GetBaseTypeByName rf.modName rf.tasName asn1
            let baseTypeAcnEncSpec =
                match tryFindAcnTypeByName rf.modName rf.tasName acn with
                | None      -> None
                | Some x    -> Some x.typeEncodingSpec
            let mergedAcnEncSpec = mergeAcnEncodingSpecs acnType baseTypeAcnEncSpec
            let newCons      = t.Constraints@extraCons
            let baseType     = mergeType asn1 acn m oldBaseType mergedAcnEncSpec newCons acnArgs
            let newRef       = {ReferenceType.modName = rf.modName; tasName = rf.tasName; tabularized = rf.tabularized; acnArguments = acnArguments; baseType=baseType}
            ReferenceType newRef
    {
        Asn1Type.Kind   = asn1Kind
        acnAligment     = tryGetProp combinedProperties (fun x -> match x with ALIGNTONEXT e -> Some e | _ -> None)
        Location        = t.Location
    }

let private mergeTAS (asn1:Asn1Ast.AstRoot) (acn:AcnAst) (m:Asn1Ast.Asn1Module) (am:AcnModule option)  (tas:Asn1Ast.TypeAssignment) : TypeAssignment =
    let acnTas = 
        match am with
        | None  -> None
        | Some x -> x.typeAssignments |> Seq.tryFind(fun z -> z.name = tas.Name)
    {
        TypeAssignment.Name = tas.Name
        c_name = tas.c_name
        ada_name = tas.ada_name
        Type = mergeType asn1 acn m tas.Type (acnTas |> Option.map(fun x -> x.typeEncodingSpec)) [] []
        Comments = tas.Comments
        acnParameters  = 
            match acnTas with 
            | None -> [] 
            | Some acnTas -> acnTas.acnParameters
    }

let private mergeModule (asn1:Asn1Ast.AstRoot) (acn:AcnAst) (m:Asn1Ast.Asn1Module) : Asn1Module =
    let acnModule = acn.files |> Seq.collect(fun f -> f.modules)  |> Seq.tryFind (fun x -> x.name = m.Name)
    {
        Asn1Module.Name = m.Name
        TypeAssignments = m.TypeAssignments |> List.map (mergeTAS asn1 acn m acnModule)
        ValueAssignments = m.ValueAssignments
        Imports  =  m.Imports
        Exports = m.Exports
        Comments = m.Comments
    }

let private mergeFile (asn1:Asn1Ast.AstRoot) (acn:AcnAst) (f:Asn1Ast.Asn1File) : Asn1File =
    {
        Asn1File.FileName = f.FileName
        Tokens = f.Tokens
        Modules =  f.Modules |> List.map (mergeModule asn1 acn)
    }

let mergeAsn1WithAcnAst (asn1:Asn1Ast.AstRoot) (acnParseResults:ParameterizedAsn1Ast.AntlrParserResult list) : AstRoot=
    let acn = CreateAcnAst acnParseResults
    let files = asn1.Files |> List.map (mergeFile asn1 acn)
    {AstRoot.Files = files; args = asn1.args; acnConstants = acn.acnConstants}
