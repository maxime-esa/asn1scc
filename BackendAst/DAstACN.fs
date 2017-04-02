module DAstACN

open System
open System.Numerics
open System.IO

open FsUtils
open Constraints
open DAst

let getFuncName (r:CAst.AstRoot) (l:ProgrammingLanguage) (tasInfo:BAst.TypeAssignmentInfo option) (codec:Ast.Codec) =
    let suffix = if codec = Ast.Encode then "_Encode" else "_Decode"
    tasInfo |> Option.map (fun x -> ToC2(r.TypePrefix + x.tasName + "_ACN" + suffix))


let createIntegerFunction (r:CAst.AstRoot) (l:ProgrammingLanguage) (o:CAst.Integer) (typeDefinition:TypeDefinitionCommon) =
    let funcBody         = 
        match l with
        | C    ->
            match o.acnEncodingClass with
            |CAst.Integer_uPER                                       ->  (fun p codec -> acn_c.PositiveInteger_ConstSize p 0I None codec, [])
            |CAst.PositiveInteger_ConstSize_8                        ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_8 p None codec, [])
            |CAst.PositiveInteger_ConstSize_big_endian_16            ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_big_endian_16 p None codec, [])
            |CAst.PositiveInteger_ConstSize_little_endian_16         ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_little_endian_16 p None codec, [])
            |CAst.PositiveInteger_ConstSize_big_endian_32            ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_big_endian_32 p None codec, [])
            |CAst.PositiveInteger_ConstSize_little_endian_32         ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_little_endian_32 p None codec, [])
            |CAst.PositiveInteger_ConstSize_big_endian_64            ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_big_endian_64 p None codec, [])
            |CAst.PositiveInteger_ConstSize_little_endian_64         ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_little_endian_64 p None codec, [])
            |CAst.PositiveInteger_ConstSize bitSize                  ->  (fun p codec -> acn_c.PositiveInteger_ConstSize p (BigInteger bitSize) None codec, [])
            |CAst.TwosComplement_ConstSize_8                         ->  (fun p codec -> acn_c.TwosComplement_ConstSize_8 p None codec, [])
            |CAst.TwosComplement_ConstSize_big_endian_16             ->  (fun p codec -> acn_c.TwosComplement_ConstSize_big_endian_16 p None codec, [])
            |CAst.TwosComplement_ConstSize_little_endian_16          ->  (fun p codec -> acn_c.TwosComplement_ConstSize_little_endian_16 p None codec, [])
            |CAst.TwosComplement_ConstSize_big_endian_32             ->  (fun p codec -> acn_c.TwosComplement_ConstSize_big_endian_32 p None codec, [])
            |CAst.TwosComplement_ConstSize_little_endian_32          ->  (fun p codec -> acn_c.TwosComplement_ConstSize_little_endian_32 p None codec, [])
            |CAst.TwosComplement_ConstSize_big_endian_64             ->  (fun p codec -> acn_c.TwosComplement_ConstSize_big_endian_64 p None codec, [])
            |CAst.TwosComplement_ConstSize_little_endian_64          ->  (fun p codec -> acn_c.TwosComplement_ConstSize_little_endian_64 p None codec, [])
            |CAst.TwosComplement_ConstSize bitSize                   ->  (fun p codec -> acn_c.TwosComplement_ConstSize p (BigInteger bitSize) None codec, [])
            |CAst.ASCII_ConstSize size                               ->  (fun p codec -> acn_c.ASCII_ConstSize p ((BigInteger size)/8I) None codec, [])
            |CAst.ASCII_VarSize_NullTerminated nullByte              ->  (fun p codec -> acn_c.ASCII_VarSize_NullTerminated p None codec, [])
            |CAst.ASCII_UINT_ConstSize size                          ->  (fun p codec -> acn_c.ASCII_UINT_ConstSize p ((BigInteger size)/8I) None codec, [])
            |CAst.ASCII_UINT_VarSize_NullTerminated nullByte         ->  (fun p codec -> acn_c.ASCII_UINT_VarSize_NullTerminated p  None codec, [])
            |CAst.BCD_ConstSize size                                 ->  (fun p codec -> acn_c.BCD_ConstSize p ((BigInteger size)/4I) None codec, [])
            |CAst.BCD_VarSize_NullTerminated nullByte                ->  (fun p codec -> acn_c.BCD_VarSize_NullTerminated p None codec, [])
        | Ada    ->
            match o.acnEncodingClass with
            |CAst.Integer_uPER                                       ->  (fun p codec -> acn_c.PositiveInteger_ConstSize p 0I None codec, [])
            |CAst.PositiveInteger_ConstSize_8                        ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_8 p None codec, [])
            |CAst.PositiveInteger_ConstSize_big_endian_16            ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_big_endian_16 p None codec, [])
            |CAst.PositiveInteger_ConstSize_little_endian_16         ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_little_endian_16 p None codec, [])
            |CAst.PositiveInteger_ConstSize_big_endian_32            ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_big_endian_32 p None codec, [])
            |CAst.PositiveInteger_ConstSize_little_endian_32         ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_little_endian_32 p None codec, [])
            |CAst.PositiveInteger_ConstSize_big_endian_64            ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_big_endian_64 p None codec, [])
            |CAst.PositiveInteger_ConstSize_little_endian_64         ->  (fun p codec -> acn_c.PositiveInteger_ConstSize_little_endian_64 p None codec, [])
            |CAst.PositiveInteger_ConstSize bitSize                  ->  (fun p codec -> acn_c.PositiveInteger_ConstSize p (BigInteger bitSize) None codec, [])
            |CAst.TwosComplement_ConstSize_8                         ->  (fun p codec -> acn_c.TwosComplement_ConstSize_8 p None codec, [])
            |CAst.TwosComplement_ConstSize_big_endian_16             ->  (fun p codec -> acn_c.TwosComplement_ConstSize_big_endian_16 p None codec, [])
            |CAst.TwosComplement_ConstSize_little_endian_16          ->  (fun p codec -> acn_c.TwosComplement_ConstSize_little_endian_16 p None codec, [])
            |CAst.TwosComplement_ConstSize_big_endian_32             ->  (fun p codec -> acn_c.TwosComplement_ConstSize_big_endian_32 p None codec, [])
            |CAst.TwosComplement_ConstSize_little_endian_32          ->  (fun p codec -> acn_c.TwosComplement_ConstSize_little_endian_32 p None codec, [])
            |CAst.TwosComplement_ConstSize_big_endian_64             ->  (fun p codec -> acn_c.TwosComplement_ConstSize_big_endian_64 p None codec, [])
            |CAst.TwosComplement_ConstSize_little_endian_64          ->  (fun p codec -> acn_c.TwosComplement_ConstSize_little_endian_64 p None codec, [])
            |CAst.TwosComplement_ConstSize bitSize                   ->  (fun p codec -> acn_c.TwosComplement_ConstSize p (BigInteger bitSize) None codec, [])
            |CAst.ASCII_ConstSize size                               ->  (fun p codec -> acn_c.ASCII_ConstSize p ((BigInteger size)/8I) None codec, [])
            |CAst.ASCII_VarSize_NullTerminated nullByte              ->  (fun p codec -> acn_c.ASCII_VarSize_NullTerminated p None codec, [])
            |CAst.ASCII_UINT_ConstSize size                          ->  (fun p codec -> acn_c.ASCII_UINT_ConstSize p ((BigInteger size)/8I) None codec, [])
            |CAst.ASCII_UINT_VarSize_NullTerminated nullByte         ->  (fun p codec -> acn_c.ASCII_UINT_VarSize_NullTerminated p  None codec, [])
            |CAst.BCD_ConstSize size                                 ->  (fun p codec -> acn_c.BCD_ConstSize p ((BigInteger size)/4I) None codec, [])
            |CAst.BCD_VarSize_NullTerminated nullByte                ->  (fun p codec -> acn_c.BCD_VarSize_NullTerminated p None codec, [])
    
    let funcName        = getFuncName r l o.tasInfo
    let  func codec = 
            match funcName codec with
            | None              -> None
            | Some funcName     -> 
                let p = if codec = Ast.Encode then "val1" else "pVal1"
                let (statement, _) = funcBody p codec 
                match l with
                |C     -> Some(acn_c.TasPrimitive funcName  typeDefinition.name [] statement [] codec)
                |Ada   -> Some(acn_c.TasPrimitive funcName  typeDefinition.name [] statement [] codec)
    let  funcDef codec = 
            match funcName codec with
            | None              -> None
            | Some funcName     -> 
                match l with
                |C     ->  Some(acn_c.TasPrimitiveDefinition funcName  typeDefinition.name [] codec)
                |Ada   ->  Some(acn_c.TasPrimitiveDefinition funcName  typeDefinition.name [] codec)
    {
        AcnFunction.funcName        = funcName
        func                        = func
        funcDef                     = funcDef
        funcBody                    = (fun p codec -> [funcBody p codec])
    }    


