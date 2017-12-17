module DAstTypeDefinition2

open System
open System.Numerics
open FsUtils
open Asn1AcnAstUtilFunctions
open Asn1AcnAst
open CommonTypes
open DAst
open DAstUtilFunctions

(*

typedef_name 			: the type definition name.
completedFintion		: the complete defintion of the type // optional
requires_definition		: true or false

	examples
	  A ::= INTEGER				-> typedef_name = "A", requires_definition = true, completedFintion = Some ("SUBTYPE A is adaasn1rtl.Asn1UInt")
	  
	  C ::= SEQUENCE  {			-> typedef_name = "C", requires_definition = true							completedFintion = Some ("TYPE C is RECORD ... END RECORD")
			a1   INTEGER		-> typedef_name = "adaasn1rtl.Asn1Int", requires_definition = false			completedFintion = None
			a2	 A				-> typedef_name = "A", requires_definition = false							completedFintion = None
			a3	 A(1..20)		-> typedef_name = "C_a3", requires_definition = true						completedFintion = Some ("SUBTYPE C_a3 is A range 0..15")
		}
		
		
let getTypeDefinitionName (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (id : ReferenceToType) =
    let longName = id.AcnAbsPath.Tail |> Seq.StrJoin "_"
    ToC2(r.args.TypePrefix + longName.Replace("#","elem"))
	  

*)


let getTypedefName (r:Asn1AcnAst.AstRoot) (pi : Asn1Fold.ParentInfo<ParentInfoData> option) (t:Asn1AcnAst.Asn1Type)   =
    match t.typeAssignmentInfo with
    | Some tasInfo      ->  ToC2(r.args.TypePrefix + tasInfo.tasName)
    | None              ->
        // I am the subtype of a reference type
        // If the reference type defines no extra constraints
        //      then there is not need to define a new type
        // otherwise
        //      define a new type that extends tasInfo
        match t.inheritInfo with
        | Some tasInfo    when not tasInfo.hasAdditionalConstraints  ->  ToC2(r.args.TypePrefix + tasInfo.tasName)
        | Some tasInfo      -> ToC2(r.args.TypePrefix + tasInfo.tasName)
        | None              -> 
            match pi with
            | Some parentInfo   ->
                match parentInfo.name with
                | Some nm -> ToC2(parentInfo.parentData.typedefName + "_" + nm)
                | None    -> ToC2(parentInfo.parentData.typedefName + "_" + "elem")
            | None              ->
                raise(BugErrorException "type has no typeAssignmentInfo and No parent!!!")
                
    
    

let getPotentialTypedefName (r:AstRoot) (t:Asn1Type)  (potentialTypedefName:string)   =
    t.newTypeDefName        


let getTypeCompleteDefinition l  typeDefinitionBody typeDefinitionName (arraySize: int option)  =
    match l with
    | C ->  
        header_c.Define_Type typeDefinitionBody typeDefinitionName (arraySize |> Option.map(fun x -> BigInteger x)) []
    | Ada   ->
        let typeOrSubsType = "subtype" 
        header_a.Define_Type typeOrSubsType typeDefinitionName typeDefinitionBody  []



let createTypeGeneric (r:Asn1AcnAst.AstRoot)  (l) (pi : Asn1Fold.ParentInfo<ParentInfoData> option) (t:Asn1AcnAst.Asn1Type)   (defineNewType)   =
    let defineSubType = match l with C -> header_c.Define_SubType | Ada -> header_a.Define_SubType
    let programUnit = ToC t.id.ModName
    match t.typeAssignmentInfo with
    | Some tasInfo      ->  
        match t.inheritInfo with
        | Some inheritInfo  -> 
            let typedefName = (ToC2(r.args.TypePrefix + tasInfo.tasName))
            let otherOptherProgrmaUnit = if  inheritInfo.modName = tasInfo.modName then None else Some (ToC inheritInfo.modName)
            let typedefBody = defineSubType typedefName otherOptherProgrmaUnit (ToC2(r.args.TypePrefix + inheritInfo.tasName)) 
            NewTypeDefinition {NewTypeDefinition.programUnit = programUnit; typedefName=typedefName; typedefBody = fun () -> typedefBody}
        | None              -> defineNewType programUnit (ToC2(r.args.TypePrefix + tasInfo.tasName)) false
    | None              ->
        match t.inheritInfo with
        | Some inheritInfo  ->  
            ReferenceToExistingDefinition {ReferenceToExistingDefinition.programUnit = ToC inheritInfo.modName; typedefName=ToC2(r.args.TypePrefix + inheritInfo.tasName)}
        | None              -> 
            let compositeTypeDefName = 
                match pi with
                | Some parentInfo   ->
                    match parentInfo.name with
                    | Some nm -> ToC2(parentInfo.parentData.typedefName + "_" + nm)
                    | None    -> ToC2(parentInfo.parentData.typedefName + "_" + "elem")
                | None              ->
                    raise(BugErrorException "type has no typeAssignmentInfo and No parent!!!")
            defineNewType programUnit compositeTypeDefName true


let rtlModuleName  l                     = match l with C -> ""                                          | Ada -> header_a.rtlModuleName()
    
let createInteger (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (pi : Asn1Fold.ParentInfo<ParentInfoData> option) (t:Asn1AcnAst.Asn1Type)  (o:Asn1AcnAst.Integer)   (us:State) =
    let declare_Integer                 = match l with C -> header_c.Declare_Integer                    | Ada -> header_a.Declare_Integer
    let declare_IntegerNoRTL            = match l with C -> header_c.Declare_Integer                    | Ada -> header_a.Declare_IntegerNoRTL
    let declare_Integer_min_max         = match l with C -> (fun a b-> header_c.Declare_Integer ())     | Ada -> header_a.Declare_Integer_min_max
    let declare_Integer_negInf          = match l with C -> (fun a  -> header_c.Declare_Integer ())     | Ada -> header_a.Declare_Integer_negInf
    let declare_Integer_posInf          = match l with C -> (fun a  -> header_c.Declare_Integer ())     | Ada -> header_a.Declare_Integer_posInf
     
    let declare_PosInteger              = match l with C -> header_c.Declare_PosInteger                 | Ada -> header_a.Declare_PosInteger
    let declare_PosIntegerNoRTL         = match l with C -> header_c.Declare_PosInteger                 | Ada -> header_a.Declare_PosIntegerNoRTL
    let declare_PosInteger_min_max      = match l with C -> (fun a b-> header_c.Declare_PosInteger ())  | Ada -> header_a.Declare_PosInteger_min_max
    let declare_PosInteger_posInf       = match l with C -> (fun a  -> header_c.Declare_PosInteger ())  | Ada -> header_a.Declare_PosInteger_posInf
    
    let defineNewType (programUnit:string) (typedefName:string) (innerType:bool) =
        let bCreateRefType, typedefBody = 
            match o.uperRange with
            | Concrete(a,b)  when a>=0I   ->  false, declare_PosInteger_min_max a b
            | Concrete(a,b)               ->  false, declare_Integer_min_max a b
            | NegInf (a)                  ->  false, declare_Integer_negInf a
            | PosInf (a) when a=0I        ->  innerType, match innerType with true -> declare_PosIntegerNoRTL () | false -> declare_PosInteger()
            | PosInf (a) when a>0I        ->  false, declare_PosInteger_posInf a
            | PosInf (a)                  ->  false, declare_Integer_posInf a
            | Full                        ->  innerType, match innerType with true -> declare_IntegerNoRTL ()    | false -> declare_Integer ()
        match bCreateRefType with
        | true      -> 
            ReferenceToExistingDefinition {ReferenceToExistingDefinition.programUnit = rtlModuleName l; typedefName=typedefBody}         
        | false     ->
            let completeDefintion = getTypeCompleteDefinition l typedefBody typedefName None
            NewTypeDefinition {NewTypeDefinition.programUnit = programUnit; typedefName = typedefName; typedefBody = fun () -> completeDefintion}
    createTypeGeneric r l pi t defineNewType

let createBoolean (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (pi : Asn1Fold.ParentInfo<ParentInfoData> option) (t:Asn1AcnAst.Asn1Type)  (o:Asn1AcnAst.Boolean)   (us:State) =
    let defineNewType (programUnit:string) (typedefName:string) (innerType:bool) =
        let declare_Boolean             = match l with C -> header_c.Declare_Boolean                        | Ada -> header_a.Declare_BOOLEAN 
        let declare_BooleanNoRTL        = match l with C -> header_c.Declare_Boolean                        | Ada -> header_a.Declare_BOOLEANNoRTL 
        match innerType with
        | true      -> 
            let typedefBody = declare_BooleanNoRTL ()
            ReferenceToExistingDefinition {ReferenceToExistingDefinition.programUnit = rtlModuleName l; typedefName=typedefBody}         
        | false     ->
            let typedefBody = declare_Boolean ()
            let completeDefintion = getTypeCompleteDefinition l typedefBody typedefName None
            NewTypeDefinition {NewTypeDefinition.programUnit = programUnit; typedefName = typedefName; typedefBody = fun () -> completeDefintion}
    createTypeGeneric r l pi t defineNewType

let createReal (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (pi : Asn1Fold.ParentInfo<ParentInfoData> option) (t:Asn1AcnAst.Asn1Type)  (o:Asn1AcnAst.Real)   (us:State) =
    let defineNewType (programUnit:string) (typedefName:string) (innerType:bool) =
        let declare_Real             = match l with C -> header_c.Declare_Real                        | Ada -> header_a.Declare_REAL 
        let declare_RealNoRTL        = match l with C -> header_c.Declare_Real                        | Ada -> header_a.Declare_REALNoRTL 
        match innerType with
        | true      -> 
            let typedefBody = declare_RealNoRTL ()
            ReferenceToExistingDefinition {ReferenceToExistingDefinition.programUnit = rtlModuleName l; typedefName=typedefBody}         
        | false     ->
            let typedefBody = declare_Real ()
            let completeDefintion = getTypeCompleteDefinition l typedefBody typedefName None
            NewTypeDefinition {NewTypeDefinition.programUnit = programUnit; typedefName = typedefName; typedefBody = fun () -> completeDefintion}
    createTypeGeneric r l pi t defineNewType

let createNull (r:Asn1AcnAst.AstRoot) (l:ProgrammingLanguage) (pi : Asn1Fold.ParentInfo<ParentInfoData> option) (t:Asn1AcnAst.Asn1Type)  (o:Asn1AcnAst.NullType)   (us:State) =
    let defineNewType (programUnit:string) (typedefName:string) (innerType:bool) =
        let declare_NullType             = match l with C -> header_c.Declare_NullType                    | Ada -> header_a.Declare_NULL 
        let declare_NullTypeNoRTL        = match l with C -> header_c.Declare_NullType                    | Ada -> header_a.Declare_NULLNoRTL 
        match innerType with
        | true      -> 
            let typedefBody = declare_NullTypeNoRTL ()
            ReferenceToExistingDefinition {ReferenceToExistingDefinition.programUnit = rtlModuleName l; typedefName=typedefBody}         
        | false     ->
            let typedefBody = declare_NullType ()
            let completeDefintion = getTypeCompleteDefinition l typedefBody typedefName None
            NewTypeDefinition {NewTypeDefinition.programUnit = programUnit; typedefName = typedefName; typedefBody = fun () -> completeDefintion}
    createTypeGeneric r l pi t defineNewType
