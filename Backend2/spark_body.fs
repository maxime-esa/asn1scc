module spark_body

open System.Numerics
open FsUtils
open Ast
open System.IO
open VisitTree
open uPER
open CloneTree
open spark_utils
open spark_equal

type State = spark_init.State


let PrintTypeAss (t:TypeAssignment) (m:Asn1Module) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) (state:State) = 
    let initContent, s1 =  spark_init.PrintTypeAss t m r state
    let valContent, s2 =   match (HasValidateFunc t.Type r) with
                           | true   ->  spark_validate.EmitTypeAss t m r s1
                           | false  -> "", s1
    let equalContent = if r.GenerateEqualFunctions then spark_equal.PrintTypeAssEqual2 t m r else ""
    let EncFunc = function
        | UPER  -> [spark_uper.EmitTypeAss t m r Encode; spark_uper.EmitTypeAss t m r Decode]
        | ACN   -> [ spark_acn.EmitUpdate_param_functions t m r acn;
                     spark_acn.EmitTypeAss t m r acn Encode; 
                     spark_acn.EmitTypeAss t m r acn Decode]
        | BER   -> []
        | XER   -> []
    let encFunctions = r.Encodings |> List.map EncFunc |> List.collect(fun x -> x)
    let content = [initContent;valContent; equalContent] @ encFunctions |> List.filter(fun s -> s<>"")
    content.StrJoin("\n\n"), s2

let PrintValueAss (v:ValueAssignment) (m:Asn1Module) (r:AstRoot) (state:State)=  
    let sName = ToC v.Name.Value 
    let sTypeDecl, _ = spark_spec.PrintType v.Type [m.Name.Value; v.Name.Value] None (ValueAssignment v,m,r) {spark_spec.State.nErrorCode = 0}
    let sValue = spark_variables.PrintAsn1Value v.Value true true v.Type (sTypeDecl,0) m r 
    match (IsOrContainsChoice v.Type r) with
    |false  -> raise(BugErrorException "")
    |true   -> ss.PrintValueAssignment_Choice_body sName sTypeDecl sValue, state

let CollectNegativeReals (m:Asn1Module) (r:AstRoot)  =
    let OnValue (v:Asn1Value) (t:Asn1Type) m r s  =
        let actType = Ast.GetActualType t r
        match v.Kind, actType.Kind with
        | RealValue(a),    Real  when a.Value <0.0  -> Set.add a.Value s
        | IntegerValue(d), Real  when d.Value <0I   -> Set.add (double d.Value) s
        | RealValue(a),    Real     -> s
        | IntegerValue(d), Real     -> s
        | _                         -> s
    let negReals = VisitModule m r {DefaultVisitors with visitValue=OnValue}  (Set.ofList [])
    negReals |> Set.toList |> Seq.map(fun d -> (spark_variables.PrintRealValueAux d, d))

let PrintModule (m:Asn1Module) (f:Asn1File) (r:AstRoot) (acn:AcnTypes.AcnAstResolved) outDir fileExt (state:State) =
    let includedPackages = ss.rtlModuleName()::(m.Imports |> List.map (fun im -> ToC im.Name.Value))
    let acnBoolPatterns = spark_acn.CollectBoolPatterns m r
    let negRealConstants = CollectNegativeReals m r |> Seq.map(fun (nm, dv) -> ss.PrintNegativeRealConstant nm dv)
    let tases, s1 = (spark_spec.SortTypeAssigments m) |> foldMap(fun s tas -> PrintTypeAss tas m r acn s) state
    let vases, s2 = m.ValueAssignments|>List.filter(fun v ->IsOrContainsChoice v.Type r) |> foldMap(fun s vas -> PrintValueAss vas m r s) s1
    let content = ss.PrintPackageBody (ToC m.Name.Value) includedPackages negRealConstants acnBoolPatterns tases vases
    let fileName = Path.Combine(outDir, ((ToC m.Name.Value)+fileExt).ToLower())
    File.WriteAllText(fileName, content.Replace("\r",""))
    s2

let PrintFile (f:Asn1File) outDir newFileExt (r:AstRoot) (acn:AcnTypes.AcnAstResolved) (state:State) =
    f.Modules |> Seq.filter(fun x -> (ModuleHasAdaBody x r)) |> Seq.fold (fun s m -> PrintModule m f r acn outDir newFileExt s) state


let GetRTLName () = ss.rtlModuleName()

let DoWork (r:AstRoot) (acn:AcnTypes.AcnAstResolved) outDir  =
    let r = spark_utils.MoveChoiceVasToPrivateModule r
    spark_spec.DoWork r acn outDir ".ads" |> ignore
    r.Files |> Seq.fold(fun s f -> PrintFile f outDir ".adb" r acn s)  {State.nErrorCode = 1000} |> ignore


