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
		
		
	  

*)

let getPotentialTypedefName (r:AstRoot) (t:Asn1Type)  (potentialTypedefName:string)   =
    match t.typeAssignmentInfo with
    | Some tasInfo      ->  tasInfo.tasName
    | None              ->
        // I am the subtype of a reference type
        // If the reference type defines no extra constraints
        //      then there is not need to define a new type
        // otherwise
        //      define a new type that extends tasInfo
        match t.inheritInfo with
        | Some tasInfo  when not tasInfo.hasAdditionalConstraints    ->  tasInfo.tasName
        | _                 -> potentialTypedefName
            


