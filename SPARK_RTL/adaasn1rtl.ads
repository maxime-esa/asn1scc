WITH Ada.Characters.Latin_1;
WITH Interfaces;
use Interfaces;
use type Interfaces.Integer_64;


--    inherit Ada.Characters.Latin_1,
--            Interfaces;


PACKAGE adaasn1rtl with SPARK_Mode
IS
   SUBTYPE RANGE_1_2 is Natural range 1..2;
   SUBTYPE RANGE_1_4 is Natural range 1..4;
   SUBTYPE RANGE_1_8 is Natural range 1..8;
   SUBTYPE RANGE_1_100 is Natural range 1..100;

   TYPE BIT IS mod 2**1;
   TYPE BitArray IS ARRAY (Natural  RANGE <>) OF BIT;
   for BitArray'Component_Size use 1;
   pragma Pack(BitArray);

   SUBTYPE Asn1Byte IS Interfaces.Unsigned_8;
   TYPE OctetBuffer IS ARRAY (Natural  RANGE <>) OF Asn1Byte;

   SUBTYPE Asn1Int IS Interfaces.Integer_64;
   SUBTYPE Asn1UInt IS Interfaces.Unsigned_64;
   SUBTYPE Asn1Real IS  Standard.Long_Float;

   SUBTYPE Asn1Boolean IS Boolean;
   SUBTYPE OctetBuffer_8 IS OctetBuffer(RANGE_1_8);
   SUBTYPE Asn1NullType IS Interfaces.Unsigned_8;

   SUBTYPE OctetArray2 IS  OctetBuffer(RANGE_1_2);
   SUBTYPE OctetArray4 IS  OctetBuffer(RANGE_1_4);
   SUBTYPE OctetArray8 IS  OctetBuffer(RANGE_1_8);
   SUBTYPE OctetArray100 IS  OctetBuffer(RANGE_1_100);

   FUNCTION PLUS_INFINITY return Asn1Real;
   FUNCTION MINUS_INFINITY return Asn1Real;

   FUNCTION GetExponent(V:Asn1Real) return Asn1Int;
   FUNCTION GetMantissa(V:Asn1Real) return Asn1UInt;
   FUNCTION RequiresReverse(dummy:BOOLEAN) return BOOLEAN;


   FUNCTION Asn1Real_Equal(Left, Right: in Asn1Real) RETURN Boolean;
   FUNCTION Asn1Boolean_Equal(Left, Right: in Asn1Boolean) RETURN Boolean;
   FUNCTION Asn1Int_Equal(Left, Right: in Asn1Int) RETURN Boolean;
   FUNCTION Asn1NullType_Equal(Left, Right: in Asn1NullType) RETURN Boolean;

   FUNCTION UInt16_to_OctetArray2(x:Interfaces.Unsigned_16) RETURN OctetArray2;
   FUNCTION OctetArray2_to_UInt16(x:OctetArray2) RETURN Interfaces.Unsigned_16;

   FUNCTION UInt32_to_OctetArray4(x:Interfaces.Unsigned_32) RETURN OctetArray4;
   FUNCTION OctetArray4_to_UInt32(x:OctetArray4) RETURN Interfaces.Unsigned_32;

   FUNCTION Asn1UInt_to_OctetArray8(x:Asn1UInt) RETURN OctetArray8;
   FUNCTION OctetArray8_to_Asn1UInt(x:OctetArray8) RETURN Asn1UInt;

   FUNCTION Int16_to_OctetArray2(x:Interfaces.Integer_16) RETURN OctetArray2;
   FUNCTION OctetArray2_to_Int16(x:OctetArray2) RETURN Interfaces.Integer_16;

   FUNCTION Int32_to_OctetArray4(x:Interfaces.Integer_32) RETURN OctetArray4;
   FUNCTION OctetArray4_to_Int32(x:OctetArray4) RETURN Interfaces.Integer_32;

   FUNCTION Asn1Int_to_OctetArray8(x:Asn1Int) RETURN OctetArray8;
   FUNCTION OctetArray8_to_Asn1Int(x:OctetArray8) RETURN Asn1Int;



   FUNCTION Float_to_OctetArray4(x:Float) RETURN OctetArray4;
   FUNCTION Long_Float_to_OctetArray8(x:Asn1Real) RETURN OctetArray8;
   FUNCTION OctetArray4_to_Float(x:OctetArray4) RETURN Float;
   FUNCTION OctetArray8_to_Long_Float(x:OctetArray8) RETURN Asn1Real;


   NUL:CONSTANT Standard.Character:=Ada.Characters.Latin_1.NUL;

   ERR_INCORRECT_DATA             : CONSTANT INTEGER := 105;
   ERR_INSUFFICIENT_DATA          : CONSTANT INTEGER := 101;
   ERR_INCORRECT_PER_STREAM       : CONSTANT INTEGER := 102;
   ERR_INVALID_CHOICE_ALTERNATIVE : CONSTANT INTEGER := 103;
   ERR_INCORRECT_STREAM		  : CONSTANT INTEGER := 104;
   ERR_INVALID_BER_FILE		  : CONSTANT INTEGER := 201;
   ERR_BER_LENGTH_MISMATCH	  : CONSTANT INTEGER := 202;
   ERR_BER_TAG_MISMATCH	  	  : CONSTANT INTEGER := 203;


    TYPE DECODE_PARAMS IS RECORD
        K	: Natural;
        DataLen	: Natural;
    END RECORD;


    TYPE ASN1_RESULT IS RECORD
         Success   : Boolean;
         ErrorCode : INTEGER;
    END RECORD;


    TYPE TEST_CASE_STEP IS (TC_VALIDATE, TC_ENCODE, TC_DECODE, TC_VALIDATE_DECODED, TC_EQUAL);

    TYPE TEST_CASE_RESULT IS RECORD
    	Step : TEST_CASE_STEP;
        Success   : Boolean;
        ErrorCode : INTEGER;
    END RECORD;






    FUNCTION getStringSize(str:String) RETURN Integer
      with
      pre => STR'First=1 AND STR'Last>=STR'First AND STR'Last<=INTEGER'LAST-1,
      post => (getStringSize'Result>=0 AND getStringSize'Result <= STR'Last);

   FUNCTION stringContainsChar(str:String; ch:Character) RETURN Boolean
   with pre => STR'Last<=INTEGER'LAST-1;

    FUNCTION GetZeroBasedCharIndex (CharToSearch : Character; AllowedCharSet : IN String) RETURN Integer
    with
	  pre => AllowedCharSet'Last>=AllowedCharSet'First AND AllowedCharSet'Last<=INTEGER'LAST-1,
      post => (GetZeroBasedCharIndex'Result>=0 AND GetZeroBasedCharIndex'Result<=AllowedCharSet'Last-AllowedCharSet'First);

    FUNCTION CharacterPos(C : Character) RETURN Integer
	with
      post => (CharacterPos'Result>=0 AND CharacterPos'Result<=127);


    PROCEDURE BitStream_AppendBit(S : in out BitArray; I : in out Natural; BitVal:IN BIT)
    with depends => ( I => I ,
                      S => (S,BitVal,I)),
    pre => I >= S'First -1 and I <= S'Last - 1,
    post => I = I'Old + 1;

    PROCEDURE BitStream_ReadBit(S : in BitArray; P : in out DECODE_PARAMS; BitVal:OUT BIT; result:OUT BOOLEAN)
    with depends => ( BitVal => (P, S) ,
                P      => P ,
                result =>( P)),
    pre => P.K >= S'First -1 and P.K <= S'Last - 1 ,
    post => P.K = P'Old.K + 1;

    PROCEDURE BitStream_AppendByte(S : in out BitArray; K : in out Natural; ByteValue:IN Asn1Byte; Negate:IN Boolean)
    with depends => ( K => K ,
                S => (S, ByteValue, K, Negate)),
    pre => K +1 >= S'First and K +8 <= S'Last,
    post => K = K'Old + 8;


    PROCEDURE BitStream_DecodeByte(S : in  BitArray; P : in out DECODE_PARAMS; ByteValue:OUT Asn1Byte; success: OUT Boolean)
    with depends => ( P => P , ByteValue => (S,P) , success =>( P)),
    pre => P.K +1 >= S'First and P.K+8 <= S'Last,
    post => P.K = P'Old.K +8;

    PROCEDURE BitStream_ReadNibble(S : in  BitArray; P : in out DECODE_PARAMS; ByteValue:OUT Asn1Byte; success: OUT Boolean)
    with depends => ( P =>( P ), ByteValue =>( S,P ), success =>( P)),
    pre => P.K +1 >= S'First and P.K+4 <= S'Last,
    post => P.K = P'Old.K +4;

    PROCEDURE BitStream_AppendPartialByte (S : in out BitArray; K : in out Natural; ByteValue:IN Asn1Byte; NBits:IN INTEGER; Negate:IN Boolean)
    with depends => ( K => (K, NBits) ,
                      S => (S, ByteValue, K, NBits, Negate)),
    pre => NBits >= 1 and NBits <= 7 and K + 1 >= S'First and K + NBits <= S'Last and S'First + nBits - 1 <= S'Last,
    post => K = K'Old + NBits;

    PROCEDURE BitStream_Encode_Non_Negative_Integer (S : in out BitArray; K : in out Natural;
                                                 IntValue : IN     Asn1UInt;
                                                  nBitsRange : IN Integer)
    with depends => ( K =>( K, nBitsRange ),
                S =>( S, IntValue, K, nBitsRange)),
    pre => 	nBitsRange >= 0 and nBitsRange <= 64 and
                K+1>= S'First and K + nBitsRange <= S'Last,
    post => K = K'Old + nBitsRange;




    PROCEDURE UPER_Enc_SemiConstraintWholeNumber(S : in out BitArray;
                                                K : in out Natural;
                                                IntVal:IN Asn1Int;
                                                MinVal:IN Asn1Int)
      with depends => (
                        (K) =>( IntVal, K, MinVal),
                        (S) =>( S, IntVal, K, MinVal)
                       ),
    pre => IntVal - MinVal >= 0  and
            K+1>= S'First and  K + 72 <= S'Last,
    post => K >= K'Old +16 and K <=K'Old+72;

   PROCEDURE UPER_Dec_SemiConstraintWholeNumber (
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
				            IntVal :    OUT Asn1Int;
         				    MinVal : IN     Asn1Int;
                                             Result : OUT Boolean)
    with depends => ( (IntVal,Result) =>( K,      MinVal,      S ),
                K      => (K,      S)),
    pre =>  K.K+1>= S'First and K.K + 72 <= S'Last,
    post => K.K >= K'Old.K +8 and K.K <= K'Old.K + 72 and
             IntVal>= MinVal;


    PROCEDURE UPER_Enc_SemiConstraintPosWholeNumber(S : in out BitArray;
                                                K : in out Natural;
                                                IntVal:IN Asn1UInt;
                                                MinVal:IN Asn1UInt)
      with depends => (
                        (K) =>( IntVal, K, MinVal),
                        (S) =>( S, IntVal, K, MinVal)
                       ),
    pre => IntVal - MinVal >= 0  and
            K+1>= S'First and  K + 72 <= S'Last,
    post => K >= K'Old +16 and K <=K'Old+72;

   PROCEDURE UPER_Dec_SemiConstraintPosWholeNumber (
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
				            IntVal :    OUT Asn1UInt;
         				    MinVal : IN     Asn1UInt;
                                             Result : OUT Boolean)
    with depends => ( (IntVal,Result) =>( K,      MinVal,      S ),
                K      => (K,      S)),
    pre =>  K.K+1>= S'First and K.K + 72 <= S'Last,
    post => K.K >= K'Old.K +8 and K.K <= K'Old.K + 72 and
             IntVal>= MinVal;




    PROCEDURE UPER_Enc_ConstraintWholeNumber(
                                            S : in out BitArray;
                                            K : in out Natural;
                                            IntVal : IN     Asn1Int;
                                            MinVal : IN     Asn1Int;
                                            nSizeInBits : IN Integer
                                           )
    with depends => ( K =>( K, nSizeInBits ),
                S =>( S, IntVal, K, MinVal, nSizeInBits)),
    pre =>  IntVal >= MinVal and nSizeInBits>=0 and nSizeInBits<=64 and
             K+1>= S'First and K + nSizeInBits <= S'Last,
    post => K = K'Old + nSizeInBits;




    PROCEDURE UPER_Dec_ConstraintWholeNumber(
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
                                            IntVal : out     Asn1Int;
                                            MinVal : IN     Asn1Int;
                                            MaxVal : IN     Asn1Int;
                                             nSizeInBits : IN Integer;
                                             Result : OUT boolean
                                           )
    with depends => ( (IntVal,Result) =>( K,      MaxVal,      MinVal,      nSizeInBits,      S ),
                K      => (K,      nSizeInBits)),
    pre =>  nSizeInBits>=0 and nSizeInBits<=64 and
             K.K+1>= S'First and  K.K + nSizeInBits <= S'Last,
    post => K.K = K'Old.K + nSizeInBits and
             ( Result = True  and then ( ((IntVal>= MinVal) AND (IntVal <=MaxVal)))) and
             ( Result = False and then (IntVal = MinVal));



    PROCEDURE UPER_Enc_ConstraintPosWholeNumber(
                                            S : in out BitArray;
                                            K : in out Natural;
                                            IntVal : IN     Asn1UInt;
                                            MinVal : IN     Asn1UInt;
                                            nSizeInBits : IN Integer
                                           )
    with depends => ( K =>( K, nSizeInBits ),
                S =>( S, IntVal, K, MinVal, nSizeInBits)),
    pre =>  IntVal >= MinVal and nSizeInBits>=0 and nSizeInBits<=64 and
             K+1>= S'First and K + nSizeInBits <= S'Last,
    post => K = K'Old + nSizeInBits;




    PROCEDURE UPER_Dec_ConstraintPosWholeNumber(
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
                                            IntVal : out     Asn1UInt;
                                            MinVal : IN     Asn1UInt;
                                            MaxVal : IN     Asn1UInt;
                                             nSizeInBits : IN Integer;
                                             Result : OUT boolean
                                           )
    with depends => ( (IntVal,Result) =>( K,      MaxVal,      MinVal,      nSizeInBits,      S ),
                K      => (K,      nSizeInBits)),
    pre =>  nSizeInBits>=0 and nSizeInBits<=64 and
             K.K+1>= S'First and  K.K + nSizeInBits <= S'Last,
    post => K.K = K'Old.K + nSizeInBits and
             ( Result = True  and then ( ((IntVal>= MinVal) AND (IntVal <=MaxVal)))) and
             ( Result = False and then (IntVal = MinVal));




    PROCEDURE UPER_Dec_ConstraintWholeNumberInt(
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
                                            IntVal : out    Integer;
                                            MinVal : IN     Integer;
                                            MaxVal : IN     Integer;
                                            nSizeInBits : IN Integer;
                                            Result : OUT boolean
                                           )
    with depends => ( (IntVal,Result) =>( K,      MaxVal,      MinVal,      nSizeInBits,      S ),
                K      =>  (K,      nSizeInBits)),
    pre =>  nSizeInBits>=0 and nSizeInBits<=64 and
             K.K+1>= S'First and  K.K + nSizeInBits <= S'Last,
    post => K.K = K'Old.K + nSizeInBits and
             ( Result = True  and then ( ((IntVal>= MinVal) AND (IntVal <=MaxVal)))) and
             ( Result = False and then (IntVal = MinVal));


    PROCEDURE UPER_Enc_UnConstraintWholeNumber (
                                                S : in out BitArray;
                                                K : in out Natural;
                                                IntVal:IN Asn1Int)
      with depends => (
                        (K) =>( IntVal, K),
                        (S) =>( S, IntVal, K)
                       ),
    pre =>  K+1>= S'First and K + 72 <= S'Last,
    post => K >= K'Old +16 and K <=K'Old+72;


    PROCEDURE UPER_Dec_UnConstraintWholeNumber (
                                                S : in BitArray;
                                                K : in out DECODE_PARAMS;
                                                IntVal:OUT Asn1Int;
                                               Result : OUT Boolean)
    with depends => ( (IntVal, K, Result) =>( K,      S)),
    pre =>  K.K+1>= S'First and K.K + 72 <= S'Last,
    post => K.K >= K'Old.K +8 and K.K <=K'Old.K+72;

    PROCEDURE UPER_Dec_UnConstraintWholeNumberMax (
                                                S : in BitArray;
                                                K : in out DECODE_PARAMS;
                                                IntVal:OUT Asn1Int;
                                                MaxVal : IN     Asn1Int;
                                                Result : OUT Boolean)
    with depends => ( (IntVal, Result) =>( K, MaxVal, S ),
       		K      =>( K, S)),
    pre =>  K.K+1>= S'First and K.K + 72 <= S'Last,
    post => K.K >= K'Old.K +8 and K.K <=K'Old.K+72 and IntVal<=MaxVal;




   PROCEDURE UPER_Enc_Boolean (S : in out BitArray; I : in out Natural; Val:IN Asn1Boolean)
    with depends => ( I =>( I ),  S =>( S,  Val, I)),
    pre => I >= S'First -1 and I <= S'Last - 1,
    post => I = I'Old + 1;

   PROCEDURE UPER_Dec_boolean(S : in BitArray; P : in out DECODE_PARAMS; val:OUT Asn1Boolean; result:OUT Boolean)
    with depends => ( val =>( P, S ),
                P      =>( P ),
       		result =>( P )),
    pre => P.K >= S'First -1 and P.K <= S'Last - 1,
    post => P.K = P'Old.K + 1;

   PROCEDURE UPER_Enc_Real(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    with depends => ( S =>( S, RealVal,K ),
                K =>(  RealVal,K)),
    pre =>  K+1>= S'First and K + 104 <= S'Last,
    post => K >= K'Old  and K <=K'Old+104;


    PROCEDURE UPER_Dec_Real (
        S       : IN     BitArray;
        K       : in out DECODE_PARAMS;
        RealVal : OUT    Asn1Real;
        Result  : OUT    ASN1_RESULT)
    with depends => (  K 	 =>( S,K ),
       		 RealVal =>( S,K ),
                 Result  =>( S,K)),
    pre =>  K.K+1>= S'First and K.K + 104 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+104;



    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt; Size:IN Integer)
    with depends => ( K =>( K, Size ),
                S =>( S, IntVal, K, Size)),
    pre =>  IntVal >= 0 and Size>=0 and Size<=64 and IntVal<=2**Size-1 and
             K+1>= S'First and K + Size <= S'Last,
    post => K = K'Old + Size;


    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_8 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and IntVal<=255 and
             K+1>= S'First and K + 8 <= S'Last,
    post => K = K'Old + 8;


    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and IntVal<=65535 and
             K+1>= S'First and K + 16 <= S'Last,
    post => K = K'Old + 16;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and IntVal<=4294967295 and
             K+1>= S'First and K + 32 <= S'Last,
    post => K = K'Old + 32;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0  and
             K+1>= S'First and K + 64 <= S'Last,
    post => K = K'Old + 64;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and IntVal<=65535 and
             K+1>= S'First and K + 16 <= S'Last,
    post => K = K'Old + 16;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and IntVal<=4294967295 and
             K+1>= S'First and K + 32 <= S'Last,
    post => K = K'Old + 32;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0  and
             K+1>= S'First and K + 64 <= S'Last,
    post => K = K'Old + 64;

    PROCEDURE Acn_Enc_Int_PositiveInteger_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
      with depends => (
                        (K) =>(IntVal,  K),
                        (S) =>( S,  IntVal,  K)
                       ),
    pre => IntVal >= 0  and
            K+1>= S'First and  K + 72 <= S'Last,
    post => K >= K'Old +16 and K <=K'Old+72;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int; Size:IN Integer)
    with depends => ( K =>( K, Size ),
                S =>( S, IntVal, K, Size)),
    pre =>  IntVal >= -2**(Size-1) and Size>=0 and Size<=64 and IntVal<=2**(Size-1)-1 and
             K+1>= S'First and K + Size <= S'Last,
    post => K = K'Old + Size;


    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_8 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -128 and IntVal<=127 and
             K+1>= S'First and K + 8 <= S'Last,
    post => K = K'Old + 8;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_big_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -32768 and IntVal<=32767 and
             K+1>= S'First and K + 16 <= S'Last,
    post => K = K'Old + 16;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_big_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -2147483648 and IntVal<=2147483647 and
             K+1>= S'First and K + 32 <= S'Last,
    post => K = K'Old + 32;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_big_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -9223372036854775808 and IntVal<=9223372036854775807 and
             K+1>= S'First and K + 64 <= S'Last,
    post => K = K'Old + 64;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_little_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -32768 and IntVal<=32767 and
             K+1>= S'First and K + 16 <= S'Last,
    post => K = K'Old + 16;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_little_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -2147483648 and IntVal<=2147483647 and
             K+1>= S'First and K + 32 <= S'Last,
    post => K = K'Old + 32;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_little_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= -9223372036854775808 and IntVal<=9223372036854775807 and
             K+1>= S'First and K + 64 <= S'Last,
    post => K = K'Old + 64;

    PROCEDURE Acn_Enc_Int_TwosComplement_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
      with depends => (
                        (K)   =>(K, IntVal),
                        (S) =>( S,  K, IntVal)
                       ),
    pre => K+1>= S'First and  K + 72 <= S'Last,
    post => K >= K'Old +16 and K <=K'Old+72;

    PROCEDURE Acn_Enc_Int_BCD_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt; nNibbles:IN Integer)
    with depends => ( K =>( K, nNibbles ),
                S =>( S, IntVal, K, nNibbles)),
    pre =>  IntVal >= 0 and nNibbles>=0 and nNibbles<=18 and IntVal<=10**nNibbles-1 and
             K+1>= S'First and K + 4*nNibbles <= S'Last,
    post => K = K'Old + 4*nNibbles;

    PROCEDURE Acn_Enc_Int_BCD_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K, IntVal ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and
             K+1>= S'First and K + 88 <= S'Last,
    post => K >= K'Old  and K <=K'Old+88;

    PROCEDURE Acn_Enc_Int_BCD_VarSize_NullTerminated(S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt)
    with depends => ( K =>( K, IntVal ),
                S =>( S, IntVal, K)),
    pre =>  IntVal >= 0 and
             K+1>= S'First and K + 76 <= S'Last,
    post => K >= K'Old  and K <=K'Old+76;

    PROCEDURE Acn_Enc_Int_ASCII_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int; nChars:IN Integer)
    with depends => ( K =>( K, nChars ),
                S =>( S, IntVal, K, nChars)),
    pre =>  nChars>=0 and nChars<=18 and IntVal>=-(10**(nChars-1)-1) and IntVal<=10**(nChars-1)-1 and
       	     IntVal>=-99999999999999999 and IntVal<=99999999999999999 and
             K+1>= S'First and K + 8*nChars <= S'Last,
    post => K = K'Old + 8*nChars;

    PROCEDURE Acn_Enc_UInt_ASCII_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1UInt; nChars:IN Integer)
    with depends => ( K =>( K, nChars ),
                S =>( S, IntVal, K, nChars)),
    pre =>  nChars>=0 and nChars<=18 and IntVal>=0 and IntVal<=10**(nChars)-1 and
       	     IntVal>=0 and IntVal<=999999999999999999 and
             K+1>= S'First and K + 8*nChars <= S'Last,
    post => K = K'Old + 8*nChars;

    PROCEDURE Acn_Enc_Int_ASCII_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K, IntVal ),
                S =>( S, IntVal, K)),
    pre => K+1>= S'First and K + 160 <= S'Last,
    post => K >= K'Old  and K <=K'Old+160;

    PROCEDURE Acn_Enc_Int_ASCII_VarSize_NullTerminated(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    with depends => ( K =>( K, IntVal ),
                S =>( S, IntVal, K)),
    pre =>  K+1>= S'First and K + 160 <= S'Last,
    post => K >= K'Old  and K <=K'Old+160;







    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; nSizeInBits:IN Integer; Result:OUT ASN1_RESULT)
    with depends => ( IntVal =>( K, nSizeInBits, S, minVal, maxVal ),
                Result =>( K, nSizeInBits, S, minVal, maxVal ),
                K      => (K,  nSizeInBits)),
    pre =>  nSizeInBits>=0 and nSizeInBits<=64 and
             K.K+1>= S'First and  K.K + nSizeInBits <= S'Last,
    post => K.K = K'Old.K + nSizeInBits and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));


    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_8(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal, Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 8 <= S'Last,
    post => K.K = K'Old.K + 8 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 16 <= S'Last,
    post => K.K = K'Old.K + 16 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 32 <= S'Last,
    post => K.K = K'Old.K + 32 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 64 <= S'Last,
    post => K.K = K'Old.K + 64 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 16 <= S'Last,
    post => K.K = K'Old.K + 16 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 32 <= S'Last,
    post => K.K = K'Old.K + 32 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal  ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 64 <= S'Last,
    post => K.K = K'Old.K + 64 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_PositiveInteger_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal ),
                K      =>( K, S)),
    pre =>  K.K+1>= S'First and  K.K + 72 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+72 and
             ( Result.Success = True  and then (IntVal>= minVal)) and
             ( Result.Success = False and then (IntVal = minVal));


    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; nSizeInBits:IN Integer; Result:OUT ASN1_RESULT)
    with depends => ( IntVal =>( K, nSizeInBits, S, minVal, maxVal ),
                Result =>( K, nSizeInBits, S, minVal, maxVal ),
                K      => (K,  nSizeInBits)),
    pre =>  nSizeInBits>=0 and nSizeInBits<=64 and
             K.K+1>= S'First and  K.K + nSizeInBits <= S'Last and
             -2**(nSizeInBits-1)<=minVal and maxVal<=2**(nSizeInBits-1)-1,
    post => K.K = K'Old.K + nSizeInBits and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));


    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_8(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 8 <= S'Last
             and -128<=minVal and maxVal<=127,
    post => K.K = K'Old.K + 8 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_big_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 16 <= S'Last
             and -32768<=minVal and maxVal<=32767,
    post => K.K = K'Old.K + 16 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_big_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 32 <= S'Last
             and -2147483648<=minVal and maxVal<=2147483647,
    post => K.K = K'Old.K + 32 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_big_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 64 <= S'Last,
    post => K.K = K'Old.K + 64 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_little_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 16 <= S'Last
             and -32768<=minVal and maxVal<=32767,
    post => K.K = K'Old.K + 16 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_little_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 32 <= S'Last
             and -2147483648<=minVal and maxVal<=2147483647,
    post => K.K = K'Old.K + 32 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_little_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 64 <= S'Last,
    post => K.K = K'Old.K + 64 and
             ( Result.Success = True  and then ( ((IntVal>= minVal)) AND (IntVal <=maxVal))) and
             ( Result.Success = False and then (IntVal = minVal));



    PROCEDURE Acn_Dec_Int_TwosComplement_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S ),
                K      =>( K, S)),
    pre =>  K.K+1>= S'First and  K.K + 72 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+72;

    PROCEDURE Acn_Dec_Int_BCD_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; nNibbles:IN Integer; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, nNibbles, minVal, maxVal ),
                K      =>( K, S, nNibbles)),
    pre =>  K.K+1>= S'First and  K.K + 4*nNibbles <= S'Last and nNibbles>=0 and nNibbles<=18 and minVal>=0 and maxVal <= 10**nNibbles-1,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+4*nNibbles and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));


    PROCEDURE Acn_Dec_Int_BCD_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 88 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+88 and
             ( Result.Success = True  and then (IntVal>= 0)) and
             ( Result.Success = False and then (IntVal = 0));

    PROCEDURE Acn_Dec_Int_BCD_VarSize_NullTerminated(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, minVal, maxVal ),
                K      =>( K, S)),
    pre =>  K.K+1>= S'First and  K.K + 76 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+76 and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_ASCII_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; nChars:IN Integer; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, nChars, minVal, maxVal ),
                K      =>( K, S, nChars)),
    pre =>  K.K+1>= S'First and  K.K + 8*nChars <= S'Last and nChars>=1 and nChars<=19,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+8*nChars and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_UInt_ASCII_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1UInt; minVal:IN Asn1UInt; maxVal:IN Asn1UInt; nChars:IN Integer; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S, nChars, minVal, maxVal ),
                K      =>( K, S, nChars)),
    pre =>  K.K+1>= S'First and  K.K + 8*nChars <= S'Last and nChars>=1 and nChars<=19,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+8*nChars and
             ( Result.Success = True  and then ( ((IntVal>= minVal) AND (IntVal <=maxVal)))) and
             ( Result.Success = False and then (IntVal = minVal));

    PROCEDURE Acn_Dec_Int_ASCII_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 160 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+160 and
             ( Result.Success = True  and then ( ((IntVal>= 0) ))) and
             ( Result.Success = False and then (IntVal = 0));

    PROCEDURE Acn_Dec_Int_ASCII_VarSize_NullTerminated(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    with depends => ( (IntVal,
                Result) =>( K, S ),
                K      =>( K)),
    pre =>  K.K+1>= S'First and  K.K + 160 <= S'Last,
    post => K.K >= K'Old.K  and K.K <=K'Old.K+160 and
             ( Result.Success = True  and then ( ((IntVal>= 0) ))) and
             ( Result.Success = False and then (IntVal = 0));

    PROCEDURE Acn_Enc_Real_IEEE754_32_big_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    with depends => ( S =>( S, RealVal,K ),
                K =>(  K)),
    pre =>  K+1>= S'First and K + 32 <= S'Last,
    post => K = K'Old+32;

    PROCEDURE Acn_Dec_Real_IEEE754_32_big_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K ),
       		 RealVal =>( S,K ),
                 Result  =>( K)),
    pre =>  K.K+1>= S'First and K.K + 32 <= S'Last,
    post => K.K >= K'Old.K  and K.K <= K'Old.K + 32;

    PROCEDURE Acn_Enc_Real_IEEE754_64_big_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    with depends => ( S =>( S, RealVal,K ),
                K =>(  K)),
    pre =>  K+1>= S'First and K + 64 <= S'Last,
    post => K = K'Old+64;

    PROCEDURE Acn_Dec_Real_IEEE754_64_big_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K ),
       		 RealVal =>( S,K ),
                 Result  =>( K)),
    pre =>  K.K+1>= S'First and K.K + 64 <= S'Last,
    post => K.K >= K'Old.K  and K.K <= K'Old.K + 64;

    PROCEDURE Acn_Enc_Real_IEEE754_32_little_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    with depends => ( S =>( S, RealVal,K ),
                K =>(  K)),
    pre =>  K+1>= S'First and K + 32 <= S'Last,
    post => K = K'Old+32;

    PROCEDURE Acn_Dec_Real_IEEE754_32_little_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K ),
       		 RealVal =>( S,K ),
                 Result  =>( K)),
    pre =>  K.K+1>= S'First and K.K + 32 <= S'Last,
    post => K.K >= K'Old.K  and K.K <= K'Old.K + 32;

    PROCEDURE Acn_Enc_Real_IEEE754_64_little_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    with depends => ( S =>( S, RealVal,K ),
                K =>(  K)),
    pre =>  K+1>= S'First and K + 64 <= S'Last,
    post => K = K'Old+64;

    PROCEDURE Acn_Dec_Real_IEEE754_64_little_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K ),
       		 RealVal =>( S,K ),
                 Result  =>( K)),
    pre =>  K.K+1>= S'First and K.K + 64 <= S'Last,
    post => K.K >= K'Old.K  and K.K <= K'Old.K + 64;

    PROCEDURE Acn_Enc_Boolean_true_pattern(S : in out BitArray; K : in out Natural; BoolVal:IN Asn1Boolean; pattern : IN BitArray)
    with depends => ( S =>( S, BoolVal, K, pattern ),
                K =>(  K, pattern)),
    pre =>  K+1>= S'First and K + pattern'Length <= S'Last,
    post => K = K'Old+pattern'Length;

    PROCEDURE Acn_Dec_Boolean_true_pattern(S : in BitArray; K : in out DECODE_PARAMS; BoolVal:OUT Asn1Boolean; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K, pattern ),
       		 BoolVal =>( S,K, pattern ),
                 Result  =>( K, pattern)),
    pre =>  K.K+1>= S'First and K.K + pattern'Length <= S'Last,
    post => K.K = K'Old.K + pattern'Length;


    PROCEDURE Acn_Enc_Boolean_false_pattern(S : in out BitArray; K : in out Natural; BoolVal:IN Asn1Boolean; pattern : IN BitArray)
    with depends => ( S =>( S, BoolVal, K, pattern ),
                K =>(  K, pattern)),
    pre =>  K+1>= S'First and K + pattern'Length <= S'Last,
    post => K = K'Old+pattern'Length;

    PROCEDURE Acn_Dec_Boolean_false_pattern(S : in BitArray; K : in out DECODE_PARAMS; BoolVal:OUT Asn1Boolean; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K, pattern ),
       		 BoolVal =>( S,K, pattern ),
                 Result  =>( K, pattern)),
    pre =>  K.K+1>= S'First and K.K + pattern'Length <= S'Last,
    post => K.K = K'Old.K + pattern'Length;


    PROCEDURE Acn_Enc_NullType_pattern(S : in out BitArray; K : in out Natural; encVal: IN Asn1NullType; pattern : IN BitArray)
    with depends => ( S =>( S, K, encVal, pattern ),
                K =>(  K, pattern)),
    pre =>  K+1>= S'First and K + pattern'Length <= S'Last,
    post => K = K'Old+pattern'Length;


    PROCEDURE Acn_Dec_NullType_pattern(S : in BitArray; K : in out DECODE_PARAMS; decValue : out Asn1NullType; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K, pattern ),
                 Result  =>( K, pattern, S  ),
                 decValue =>( S, K, pattern)),
    pre =>  K.K+1>= S'First and K.K + pattern'Length <= S'Last,
    post => K.K = K'Old.K + pattern'Length;



    PROCEDURE Acn_Enc_NullType_pattern2(S : in out BitArray; K : in out Natural; pattern : IN BitArray)
    with depends => ( S =>( S, K, pattern ),
                K =>(  K, pattern)),
    pre =>  K+1>= S'First and K + pattern'Length <= S'Last,
    post => K = K'Old+pattern'Length;


    PROCEDURE Acn_Dec_NullType_pattern2(S : in BitArray; K : in out DECODE_PARAMS; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K, pattern ),
                 Result  =>( K, pattern, S )),
    pre =>  K.K+1>= S'First and K.K + pattern'Length <= S'Last,
    post => K.K = K'Old.K + pattern'Length;


    PROCEDURE Acn_Enc_NullType(S : in out BitArray; K : in out Natural; encVal: IN Asn1NullType)
    with depends => ( S =>( S, K, encVal ),
                K =>(  K)),
    pre =>  K+1>= S'First and K <= S'Last,
    post => K = K'Old;

    PROCEDURE Acn_Dec_NullType(S : in BitArray; K : in out DECODE_PARAMS; decValue : out Asn1NullType; Result:OUT ASN1_RESULT)
    with depends => (  K 	 =>( K ),
                 Result  =>( K  ),
                 decValue =>( S, K)),
    pre =>  K.K+1>= S'First and K.K  <= S'Last,
    post => K.K = K'Old.K ;



    -- String functions
     PROCEDURE Acn_Enc_String_Ascii_FixSize(S : in out BitArray; K : in out Natural; strVal : in String)
    with depends => (    S =>( S, K, strVal ),
       		   K =>( K, strVal)),
    pre =>  K+1>= S'First and K + 8*(strVal'Length-1) <= S'Last,
    post => K = K'Old + 8*(strVal'Length-1);


    PROCEDURE Acn_Dec_String_Ascii_FixSize(S : in BitArray; K : in out DECODE_PARAMS; strVal : in out String; Result:OUT ASN1_RESULT)
    with depends => (    K =>(S, K, strVal ),
                   strVal =>( S, K, strVal ),
                   Result =>( S, K, strVal)),
    pre =>  S'First = 1 and K.K+1>= S'First and K.K + 8*(strVal'Length-1) <= S'Last,
    post => K.K = K'Old.K + 8*(strVal'Length-1);



    PROCEDURE Acn_Enc_String_Ascii_Null_Teminated(S : in out BitArray; K : in out Natural; null_character : in Integer; strVal : in String);
    PROCEDURE Acn_Dec_String_Ascii_Null_Teminated(S : in BitArray; K : in out DECODE_PARAMS; null_character : in Integer; strVal : in out String; Result:OUT ASN1_RESULT);

    PROCEDURE Acn_Enc_String_Ascii_Internal_Field_Determinant(S : in out BitArray; K : in out Natural; asn1Min: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : in String);
    PROCEDURE Acn_Dec_String_Ascii_Internal_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; asn1Min: Asn1Int; asn1Max: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : in out String; Result:OUT ASN1_RESULT);

    PROCEDURE Acn_Enc_String_Ascii_External_Field_Determinant(S : in out BitArray; K : in out Natural; strVal : in String);
    PROCEDURE Acn_Dec_String_Ascii_External_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; extSizeDeterminatFld : IN Asn1UInt; strVal :in out String; Result:OUT ASN1_RESULT);


     PROCEDURE Acn_Enc_String_CharIndex_FixSize(S : in out BitArray; K : in out Natural; charSet : String; nCharSize:Integer; strVal : in String);
     PROCEDURE Acn_Dec_String_CharIndex_FixSize(S : in BitArray; K : in out DECODE_PARAMS; charSet : String; nCharSize:Integer; strVal : in out String; Result:OUT ASN1_RESULT);

     PROCEDURE Acn_Enc_String_CharIndex_External_Field_Determinant(S : in out BitArray; K : in out Natural; charSet : String; nCharSize:Integer; strVal : in String);
     PROCEDURE Acn_Dec_String_CharIndex_External_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; charSet : String; nCharSize:Integer; extSizeDeterminatFld : IN Asn1UInt; strVal : in out String; Result:OUT ASN1_RESULT);

     PROCEDURE Acn_Enc_String_CharIndex_Internal_Field_Determinant(S : in out BitArray; K : in out Natural; charSet : String; nCharSize:Integer; asn1Min: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : in String);
     PROCEDURE Acn_Dec_String_CharIndex_Internal_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; charSet : String; nCharSize:Integer; asn1Min: Asn1Int; asn1Max: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal :in out String; Result:OUT ASN1_RESULT);



     FUNCTION milbus_encode(IntVal:IN Asn1Int) RETURN Asn1Int;
     FUNCTION milbus_decode(IntVal:IN Asn1Int) RETURN Asn1Int;


END adaasn1rtl;
