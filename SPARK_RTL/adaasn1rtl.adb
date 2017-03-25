with Interfaces;
with Ada.Unchecked_Conversion;
use type Interfaces.Integer_32;
use type Interfaces.Integer_16;
use type Interfaces.Unsigned_8;
use type Interfaces.Unsigned_32;
use type Interfaces.Unsigned_16;
use type Interfaces.Integer_8;
use type Interfaces.Unsigned_64;
use type Interfaces.Integer_64;

PACKAGE BODY adaasn1rtl IS

   MASKS : CONSTANT OctetBuffer_8 := OctetBuffer_8'(16#80#, 16#40#, 16#20#, 16#10#, 16#08#, 16#04#, 16#02#, 16#01#);
   MSBIT_ONE  : CONSTANT Asn1UInt := 16#8000000000000000#;

   MSBYTE_FF  : CONSTANT Asn1UInt:= 16#FF00000000000000#;

   MantissaFactor : CONSTANT Asn1Real:=Asn1Real(Interfaces.Unsigned_64(2)**Asn1Real'Machine_Mantissa);

   ERR_END_OF_STREAM           :CONSTANT INTEGER:= 1001;
   ERR_UNSUPPORTED_ENCODING    :CONSTANT INTEGER:= 1001;  --  Returned when the uPER encoding for REALs is not binary encoding


   FUNCTION Asn1Real_Equal(Left, Right: in Asn1Real) RETURN Boolean
   IS
       ret : Boolean;
   BEGIN
       IF Left = Right THEN
           ret := true;
       ELSIF Left = 0.0 THEN
           ret := Right = 0.0;
       ELSE
           ret := ABS((Left - Right) / Left) < 0.00001;
       END IF;
       RETURN ret;
   END Asn1Real_Equal;


   FUNCTION Asn1Boolean_Equal(Left, Right: in Boolean) RETURN Boolean
   IS (Left = Right);

   FUNCTION Asn1Int_Equal(Left, Right: in Asn1Int) RETURN Boolean
   IS (Left = Right);

   FUNCTION Asn1NullType_Equal(Left, Right: in Asn1NullType) RETURN Boolean
   IS (TRUE);

   FUNCTION getStringSize(str:String) RETURN Integer
   IS
      I:Integer:=1;
   BEGIN
      WHILE I<=str'Last AND THEN str(I)/=NUL LOOP
         pragma Loop_Invariant (I>=1 AND I<=str'Last);
         I:=I+1;
      END LOOP;
      RETURN I-1;
   END  getStringSize;


   FUNCTION stringContainsChar(str:String; ch:Character) RETURN Boolean
   IS
      I:INTEGER;
      bFound:BOOLEAN:=false;
   BEGIN
      I:=str'First;
      WHILE I<=str'Last AND NOT bFound LOOP
         --# assert I>=str'First AND I<=str'Last;
         bFound := str(I) = ch;
         I:=I+1;
      END LOOP;
      return bFound;
   END stringContainsChar;


   FUNCTION To_Int(IntVal: Asn1UInt) return Asn1Int
   IS
       ret:Asn1Int;
       c:Asn1UInt;
   BEGIN
       IF IntVal > Asn1UInt(Asn1Int'Last) THEN
           c := NOT IntVal;
           ret := -Asn1Int(c) - 1;
       ELSE
           ret := Asn1Int(IntVal);
       END IF;
       RETURN ret;
   END To_Int;


   FUNCTION Zero return Asn1Real is
   BEGIN
        return 0.0;
   END Zero;

   FUNCTION PLUS_INFINITY return Asn1Real
   is
      --# hide PLUS_INFINITY;
   BEGIN
        return 1.0/Zero;
   END PLUS_INFINITY;

   FUNCTION MINUS_INFINITY return Asn1Real
   is
      --# hide MINUS_INFINITY;
   BEGIN
        return -1.0/Zero;
   END MINUS_INFINITY;


   FUNCTION RequiresReverse(dummy:BOOLEAN) return BOOLEAN
   IS
      --# hide RequiresReverse;
      dword:Integer := 16#00000001#;
      arr: aliased OctetArray4;
      for arr'Address use dword'Address;
   BEGIN
      return arr(arr'First)=1;
   END RequiresReverse;

   FUNCTION To_Int_n(IntVal: Asn1UInt; nBits: INTEGER) return Asn1Int
   --# pre nBits>=0 and nBits<=64;
   IS
      ret:Asn1Int;
      c:Asn1UInt;
  BEGIN
      IF nBits = 0 THEN
          ret :=0;
      ELSIF nBits = 64 THEN
          ret := To_Int(IntVal);
      ELSE
      --# assert  nBits>=1 and nBits<=63
      --# and 2**(nBits-1)>=1 AND 2**(nBits-1)<=4611686018427387904 AND 2**nBits-1>=1 AND 2**nBits-1<=9223372036854775807;
          IF IntVal > Asn1UInt(2)**(nBits-1) THEN
              c := NOT (Asn1UInt(2)**nBits-1);
              ret := To_Int(IntVal OR c);
          ELSE
              ret := Asn1Int(IntVal);
          END IF;
      END IF;
      RETURN ret;
  END To_Int_n;




    PROCEDURE BitStream_AppendBit(S : in out BitArray; I : in out Natural; BitVal:IN BIT) IS
    BEGIN
        I := I + 1;
        S(I) := BitVal;
   END BitStream_AppendBit;




    PROCEDURE BitStream_ReadBit(S : in BitArray; P : in out DECODE_PARAMS; BitVal:OUT BIT; result:OUT BOOLEAN)
    IS
    BEGIN
        P.K := P.K + 1;
        BitVal := S(P.K);
        result := P.DataLen - P.K >=0;
    END BitStream_ReadBit;






    ---# pre K +1 >= S'First and K+8 <= S'Last;
    ---# post K = K~ + 8;

    PROCEDURE BitStream_AppendByte(S : in out BitArray; K : in out Natural; ByteValue:IN Asn1Byte; Negate:IN Boolean)
    IS
        ByteVal: Asn1Byte;
    BEGIN
        IF Negate THEN
            ByteVal := NOT ByteValue;
        ELSE
            ByteVal := ByteValue;
        END IF;

        FOR I IN  RANGE_1_8 LOOP
            --# assert K = K~ and K + 1>= S'First and K + 8 <= S'Last and K+I >=S'First  and K+I-1 < S'Last;
            IF  (MASKS(I) AND ByteVal)>0 THEN
                S(K+I) := 1;
            ELSE
                S(K+I) := 0;
            END IF;
        END LOOP;
        K := K + 8;

    END BitStream_AppendByte;

     PROCEDURE BitStream_DecodeByte(S : in  BitArray; P : in out DECODE_PARAMS; ByteValue:OUT Asn1Byte; success: OUT Boolean)
     IS
     BEGIN
        ByteValue := 0;
        FOR I IN Integer range 1..8 LOOP
    --# assert 	P.K + 8 <= S'Last and P.K+1>= S'First and
    --#		P.K=P~.K and  P.K + I - 1< S'Last;

            IF S(P.K+I)=0 THEN
                ByteValue := 2*ByteValue;
            ELSE
                ByteValue := 2*ByteValue + 1;
            END IF;

        END LOOP;

        P.K := P.K + 8;
        success := P.DataLen-P.K>=0;
     END BitStream_DecodeByte;


    PROCEDURE BitStream_AppendPartialByte (S : in out BitArray; K : in out Natural; ByteValue:IN Asn1Byte; NBits:IN INTEGER; Negate:IN Boolean)
    IS
        ByteVal: Asn1Byte;

    BEGIN
        IF Negate THEN
            ByteVal := NOT ByteValue;
        ELSE
            ByteVal := ByteValue;
        END IF;

        FOR I IN Integer range 1 .. NBITS LOOP
--            --# assert  NBits >= MASKS'FIRST and NBits < MASKS'LAST and K + 1 >= S'First and K + NBits <= S'Last and S'First + nBits -1 <= S'Last and
            --# assert  NBits >= MASKS'FIRST and NBits < MASKS'LAST and K + 1 >= S'First and K + NBits <= S'Last and
            --#         K = K~ and  K + I>=S'First  and K + I - 1< S'Last and
            --#   	I+(MASKS'LAST - NBITS) >=MASKS'First and I+(MASKS'LAST - NBITS) <=MASKS'Last;
            IF  (MASKS(I+(MASKS'LAST - NBITS)) AND ByteVal)>0 THEN
                S(K+I) := 1;
            ELSE
                S(K+I) := 0;
            END IF;
        END LOOP;

        K := K + NBits;
    END BitStream_AppendPartialByte;


     PROCEDURE BitStream_ReadNibble(S : in  BitArray; P : in out DECODE_PARAMS; ByteValue:OUT Asn1Byte; success: OUT Boolean)
     IS
     BEGIN
        ByteValue := 0;
        FOR I IN Integer range 1..4 LOOP
    --# assert 	P.K + 4 <= S'Last and P.K+1>= S'First and
    --#		P.K=P~.K and  P.K + I - 1< S'Last;

            IF S(P.K+I)=0 THEN
                ByteValue := 2*ByteValue;
            ELSE
                ByteValue := 2*ByteValue + 1;
            END IF;

        END LOOP;

        P.K := P.K + 4;
        success := P.DataLen-P.K>=0;
     END BitStream_ReadNibble;


    PROCEDURE BitStream_Encode_Non_Negative_Integer (S : in out BitArray; K : in out Natural;
                                                     IntValue : IN     Asn1UInt;
                                                     nBitsRange : IN Integer)
    IS
        IVAL :          Asn1UInt;
        scaleFactor : Asn1UInt;
        nBitsToSkip : Integer;
    BEGIN
        IF nBitsRange <= 63 THEN
            nBitsToSkip := 64 - nBitsRange;
            scaleFactor := 2**nBitsToSkip;
            IVal := IntValue * scaleFactor;
        ELSE
            IVal := IntValue;
        END IF;

        FOR I IN Integer range 1..nBitsRange LOOP
    --# assert 	nBitsRange >= 1 and nBitsRange <= 64 and
    --#         K + nBitsRange <= S'Last and
    --#         K+1>= S'First and
    --#		K=K~ and  K + I - 1< S'Last;

            IF (IVAL AND MSBIT_ONE)=0 THEN
                S(K+I) := 0;
            ELSE
                S(K+I) := 1;
            END IF;

            IVal := IVal * 2;
        END LOOP;

        K := K + nBitsRange;
    END BitStream_Encode_Non_Negative_Integer;


    PROCEDURE BitStream_Decode_Non_Negative_Integer (S : in BitArray;
                                                     P : in out DECODE_PARAMS;
                                                     IntValue : out     Asn1UInt;
                                                     nBitsRange : IN Integer;
                                                     result : OUT Boolean)
    --# derives IntValue from S, P, nBitsRange & P from P, nBitsRange & result from P, nBitsRange;
    --# pre 	nBitsRange >= 0 and nBitsRange <= 64 and
    --#         P.K+1>= S'First and P.K + nBitsRange <= S'Last;
    --# post P.K = P~.K + nBitsRange;
    IS
    BEGIN

        IntValue := 0;
        FOR I IN Integer range 1..nBitsRange LOOP
    --# assert 	nBitsRange >= 1 and nBitsRange <= 64 and
    --#         P.K + nBitsRange <= S'Last and
    --#         P.K+1>= S'First and
    --#		P.K=P~.K and  P.K + I - 1< S'Last;

            IF S(P.K+I)=0 THEN
                IntValue := 2*IntValue;
            ELSE
                IntValue := 2*IntValue + 1;
            END IF;

        END LOOP;

        P.K := P.K + nBitsRange;
        result := P.DataLen-P.K>=0;
    END BitStream_Decode_Non_Negative_Integer;



    FUNCTION Sub (A : IN     Asn1Int; B : IN     Asn1Int)    RETURN Asn1UInt
    --# pre A >= B;
    --# return Asn1Uint(A-B);
    IS
        --# hide Sub;
        ret:Asn1UInt ;
        diff:Asn1Int;
    BEGIN
        diff := A-B;
        if (diff >= 0) then
            ret := Asn1UInt(diff);
        else
            ret := Asn1UInt(-diff);
            ret := NOT ret;
            ret := ret + 1;
        end if;
        RETURN ret;
    END Sub;




    FUNCTION GetBytes (V : Asn1Uint)   RETURN Integer
      --# return M => M>=1 and M<=8;
    IS
      Ret:Integer;
    BEGIN
        IF    V<16#100#             THEN Ret:=1;
        ELSIF V<16#10000#           THEN Ret:=2;
        ELSIF V<16#1000000#         THEN Ret:=3;
        ELSIF V<16#100000000#       THEN Ret:=4;
        ELSIF V<16#10000000000#     THEN Ret:=5;
        ELSIF V<16#1000000000000#   THEN Ret:=6;
        ELSIF V<16#100000000000000# THEN Ret:=7;
        ELSE                             Ret:=8;
        END IF;
        return Ret;
    END GetBytes;



    PROCEDURE Enc_UInt (
                        S : in out BitArray;
                        K : in out Natural;
                      	EncodedValue : IN     Asn1UInt;
                        nBytes : IN Integer)
    --# derives S from S, K, EncodedValue, nBytes & K from K, nBytes;
    --# pre nBytes >= 1  and nBytes<=8 and
    --#     K+1>= S'First and K + nBytes*8 <= S'Last;
    --# post K = K~ + nBytes*8;
    IS
        ActualEncodedValue :Asn1UInt;
        byteToEncode:Interfaces.Unsigned_8;
    BEGIN



        ActualEncodedValue := EncodedValue;

        --Encode number
        FOR I IN Integer range 1..(8-nBytes) LOOP
            --# assert nBytes >= 1  and nBytes<=8 and K=K~ and I>=1 and I<=7 and
            --#        K+1>= S'First and K + nBytes*8 <= S'Last;
            ActualEncodedValue := ActualEncodedValue * 16#100#;
        END LOOP;

        FOR I IN Integer range 0..nBytes-1 LOOP
            --# assert nBytes >= 1  and nBytes<=8 and I>=0 and I<=7 and K = K~ + 8*I and
            --#        K+1>= S'First and K + 8 <= S'Last;
            byteToEncode :=  Interfaces.Unsigned_8((ActualEncodedValue AND MSBYTE_FF)/16#100000000000000#);
            ActualEncodedValue := ActualEncodedValue * 16#100#;
            BitStream_AppendByte(S,K, byteToEncode, FALSE);
        END LOOP;
    END Enc_UInt;








    FUNCTION GetLengthInBytesOfSIntAux (V : Asn1Uint)     RETURN Integer
      --# pre V >= 0;
      --# return M => M>=1 and M<=8;
    IS
        Ret:Integer;
    BEGIN
        IF    V<16#80#             THEN Ret := 1;
        ELSIF V<16#8000#           THEN Ret := 2;
        ELSIF V<16#800000#         THEN  Ret := 3;
        ELSIF V<16#80000000#       THEN  Ret := 4;
        ELSIF V<16#8000000000#     THEN  Ret := 5;
        ELSIF V<16#800000000000#   THEN  Ret := 6;
        ELSIF V<16#80000000000000# THEN  Ret := 7;
        ELSE  Ret := 8;
        END IF;

        RETURN Ret;
    END GetLengthInBytesOfSIntAux;


    FUNCTION GetLengthInBytesOfSInt (V : Asn1Int) RETURN Integer
      --# return M => M>=1 and M<=8;
    IS
        Ret:Integer;
    BEGIN
        IF V >= 0 THEN
            Ret := GetLengthInBytesOfSIntAux(Asn1UInt(V));
        ELSE
            Ret := GetLengthInBytesOfSIntAux(Asn1UInt(-(V + 1)));
        END IF;
        RETURN Ret;
    END GetLengthInBytesOfSInt;

    FUNCTION To_UInt(IntVal: Asn1Int) return Asn1Uint
    IS
        ret:Asn1Uint;
    Begin
        IF IntVal < 0 THEN
            ret:=Asn1UInt(-(IntVal+1));
            ret := NOT ret;
        ELSE
            ret:= Asn1UInt(IntVal);
        END IF;
      return ret;
    End To_UInt;

    FUNCTION To_UInt32(IntVal: Asn1Int) return Interfaces.Unsigned_32
    --# pre IntVal >= 0 and IntVal <= Interfaces.Unsigned_32'Last;
    IS
    Begin
    	return Interfaces.Unsigned_32(IntVal);
    End To_UInt32;

    FUNCTION Int32_UInt32(IntVal: Interfaces.Integer_32) return Interfaces.Unsigned_32
    IS
        ret:Interfaces.Unsigned_32;
    Begin

        IF IntVal < 0 THEN
            ret:=Interfaces.Unsigned_32(-(IntVal+1));
            ret := NOT ret;
        ELSE
            ret:= Interfaces.Unsigned_32(IntVal);
        END IF;
      return ret;
    End Int32_UInt32;

    FUNCTION UInt32_Int32(IntVal: Interfaces.Unsigned_32) return Interfaces.Integer_32
    IS
        ret:Interfaces.Integer_32;
        c:Interfaces.Unsigned_32;
    Begin
        IF IntVal > Interfaces.Unsigned_32(Interfaces.Integer_32'Last) THEN
            c := NOT IntVal;
            ret := -Interfaces.Integer_32(c) - 1;
        ELSE
            ret := Interfaces.Integer_32(IntVal);
        END IF;
      return ret;
    End UInt32_Int32;




    FUNCTION To_UInt16(IntVal: Asn1Int) return Interfaces.Unsigned_16
    --# pre IntVal >= 0 and IntVal <= Interfaces.Unsigned_16'Last;
    IS
    Begin
    	return Interfaces.Unsigned_16(IntVal);
    End To_UInt16;


    FUNCTION Int16_UInt16(IntVal: Interfaces.Integer_16) return Interfaces.Unsigned_16
    IS
        ret:Interfaces.Unsigned_16;
    Begin

        IF IntVal < 0 THEN
            ret:=Interfaces.Unsigned_16(-(IntVal+1));
            ret := NOT ret;
        ELSE
            ret:= Interfaces.Unsigned_16(IntVal);
        END IF;
      return ret;
    End Int16_UInt16;

    FUNCTION UInt16_Int16(IntVal: Interfaces.Unsigned_16) return Interfaces.Integer_16
    IS
        ret:Interfaces.Integer_16;
        c:Interfaces.Unsigned_16;
    Begin
        IF IntVal > Interfaces.Unsigned_16(Interfaces.Integer_16'Last) THEN
            c := NOT IntVal;
            ret := -Interfaces.Integer_16(c) - 1;
        ELSE
            ret := Interfaces.Integer_16(IntVal);
        END IF;
      return ret;
    End UInt16_Int16;


    PROCEDURE UPER_Enc_ConstraintWholeNumber(
                                            S : in out BitArray;
                                            K : in out Natural;
                                            IntVal : IN     Asn1Int;
                                            MinVal : IN     Asn1Int;
                                            nSizeInBits : IN Integer
                                           )
    IS
        encVal : Asn1UInt;
    BEGIN
        encVal := Sub(IntVal, MinVal);
        BitStream_Encode_Non_Negative_Integer(S, K, encVal, nSizeInBits);
    END UPER_Enc_ConstraintWholeNumber;




    PROCEDURE UPER_Dec_ConstraintWholeNumber(
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
                                            IntVal : out     Asn1Int;
                                            MinVal : IN     Asn1Int;
                                            MaxVal : IN     Asn1Int;
                                             nSizeInBits : IN Integer;
                                             Result : OUT Boolean
                                            )
    IS
        encVal : Asn1UInt;
    BEGIN
        BitStream_Decode_Non_Negative_Integer(S, K, encVal, nSizeInBits, Result);
        IF Result THEN
            IntVal := To_Int(encVal + To_UInt(MinVal));

            Result := IntVal>= MinVal AND IntVal <=MaxVal;
            IF NOT Result THEN
                IntVal := MinVal;
            END IF;
        ELSE
            IntVal := MinVal;
        END IF;


    END UPER_Dec_ConstraintWholeNumber;

    PROCEDURE UPER_Dec_ConstraintWholeNumberInt(
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
                                            IntVal : out    Integer;
                                            MinVal : IN     Integer;
                                            MaxVal : IN     Integer;
                                            nSizeInBits : IN Integer;
                                            Result : OUT boolean
                                               )
    IS
    	Ret : Asn1Int;
    BEGIN
        UPER_Dec_ConstraintWholeNumber(S,K,Ret,Asn1Int(MinVal),Asn1Int(MaxVal),nSizeInBits,Result);
        IntVal := Integer(Ret);
    END UPER_Dec_ConstraintWholeNumberInt;




    PROCEDURE UPER_Enc_SemiConstraintWholeNumber (
                                                  S : in out BitArray;
                                                  K : in out Natural;
                                                  IntVal : IN     Asn1Int;
                                                  MinVal : IN     Asn1Int)
    IS
        nBytes : Integer;
        ActualEncodedValue : Asn1UInt;
    BEGIN
      ActualEncodedValue  := Sub (IntVal,  MinVal);

        nBytes:=GetBytes(ActualEncodedValue);

      -- encode length
      BitStream_AppendByte(S,K, Interfaces.Unsigned_8(nBytes),FALSE);
      --Encode number
      Enc_UInt(S,K, ActualEncodedValue, nBytes);
   END UPER_Enc_SemiConstraintWholeNumber;











    PROCEDURE Dec_UInt (
           S : in BitArray;
           K : in out DECODE_PARAMS;
           nBytes  : Integer;
           Ret : OUT Asn1UInt;
           result : OUT Boolean)
    --#derives K    from K, nBytes &
    --#        Ret  from S, K, nBytes &
    --#        result from K, nBytes;
    --#pre     nBytes>=1 AND nBytes<=8 AND
    --#        K.K+1>= S'First and K.K + nBytes*8 <= S'Last;
    --#post    K.K >= K~.K AND K.K<=K~.K+nBytes*8;
    IS
       ByteVal : Asn1UInt;
       I	      : Integer;
    BEGIN
        I :=1;
        Ret := 0;
        result := True;
        WHILE I <= nBytes AND result LOOP
        --# assert I<=nBytes and I>=1 and K~.K+1>= S'First and K~.K + nBytes*8 <= S'Last and K.K=K~.K+8*(I-1);
            BitStream_Decode_Non_Negative_Integer(S,K,ByteVal,8, result);
            IF result THEN
                Ret := (Ret*256) OR ByteVal;
                I := I + 1;
            END IF;
        END LOOP;
        result := result AND K.DataLen-K.K >=0;
    END Dec_UInt;



    PROCEDURE Dec_Int (
           S : in BitArray;
           K : in out DECODE_PARAMS;
           nBytes  : Integer;
           RetVal : OUT Asn1Int;
           result : OUT Boolean)
    --#derives K       from K, nBytes &
    --#        RetVal  from S, K, nBytes &
    --#        result  from K, nBytes;
    --#pre     nBytes>=1 AND nBytes<=8 AND
    --#        K.K+1>= S'First and K.K + nBytes*8 <= S'Last;
    --#post    K.K >= K~.K AND K.K<=K~.K+nBytes*8;
    IS
        ByteVal : Asn1UInt;
        I       : Integer;
        Ret     : Asn1UInt;
    BEGIN
        I :=1;
        IF S(K.K+1) = 0 THEN
            Ret := 0;
        ELSE
            Ret:=Asn1UInt'Last;
        END IF;
        result := True;
        WHILE I <= nBytes AND result LOOP
        --# assert I<=nBytes and I>=1 and K~.K+1>= S'First and K~.K + nBytes*8 <= S'Last and K.K=K~.K+8*(I-1);
            BitStream_Decode_Non_Negative_Integer(S,K,ByteVal,8, result);
            IF result THEN
                Ret := (Ret*256) OR ByteVal;
                I := I + 1;
            END IF;
        END LOOP;
        RetVal := To_Int(Ret);
        result := result AND K.DataLen-K.K >=0;
    END Dec_Int;




   PROCEDURE UPER_Dec_SemiConstraintWholeNumber (
                                            S : in BitArray;
                                            K : in out DECODE_PARAMS;
				            IntVal : OUT Asn1Int;
         				    MinVal : IN  Asn1Int;
                                            Result : OUT Boolean)
   IS
      NBytes  : Asn1Int;
--      ByteVal : Asn1UInt;
      Ret     : Asn1UInt;
--      I_MAX   : Integer;
--      I	      : Integer;
   BEGIN

      IntVal := MinVal;
      UPER_Dec_ConstraintWholeNumber(S,K,NBytes,0,255,8,Result);
      IF Result AND NBytes>=1 AND NBytes<=8 THEN
            Dec_UInt(S, K, Integer(nBytes), Ret, result);
            IF result THEN
                IntVal := To_Int(Ret + To_UInt(MinVal));
                Result := IntVal>= MinVal;
                IF NOT Result THEN IntVal := MinVal; END IF;
            END IF;
      ELSE
      	 Result :=FALSE;
      END IF;

   END UPER_Dec_SemiConstraintWholeNumber;


    PROCEDURE UPER_Enc_UnConstraintWholeNumber (
                                                S : in out BitArray;
                                                K : in out Natural;
                                                IntVal:IN Asn1Int)
    IS
       nBytes : Integer;
    BEGIN

        nBytes:=GetLengthInBytesOfSInt(IntVal);

        -- encode length
        BitStream_AppendByte(S, K, Interfaces.Unsigned_8(NBytes),FALSE);
        Enc_UInt(S, K, To_UInt(IntVal), nBytes);
    END UPER_Enc_UnConstraintWholeNumber;





    PROCEDURE UPER_Dec_UnConstraintWholeNumber (
                                                S : in BitArray;
                                                K : in out DECODE_PARAMS;
                                                IntVal:OUT Asn1Int;
                                               Result : OUT Boolean)
    IS
        NBytes  : Asn1Int;
    BEGIN
       UPER_Dec_ConstraintWholeNumber(S,K,NBytes,0,255,8,Result);
       IF Result AND NBytes>=1 AND NBytes<=8 THEN
           Dec_Int(S, K, Integer(nBytes), IntVal, result);
       ELSE
           IntVal := 0;
           Result := False;
       END IF;
    END UPER_Dec_UnConstraintWholeNumber;


    PROCEDURE UPER_Dec_UnConstraintWholeNumberMax (
                                                S : in BitArray;
                                                K : in out DECODE_PARAMS;
                                                IntVal:OUT Asn1Int;
                                                MaxVal : IN     Asn1Int;
                                                Result : OUT Boolean)
    ---# derives IntVal,
    ---#         Result from K, MaxVal, S &
    ---#		K      from K, S;
    ---# pre  K.K+1>= S'First and K.K + 72 <= S'Last;
    ---# post K.K >= K~.K +8 and K.K <=K~.K+72 and IntVal<=MaxVal;
    IS
    BEGIN
    	UPER_Dec_UnConstraintWholeNumber(S, K, IntVal, Result);
        Result := Result AND IntVal <= MaxVal;
        IF NOT Result THEN
	    IntVal := MaxVal;
        END IF;
    END UPER_Dec_UnConstraintWholeNumberMax;


   PROCEDURE UPER_Enc_Boolean (S : in out BitArray; I : in out Natural; Val:IN Asn1Boolean)
   IS
      b:BIT;
   BEGIN

      IF Val THEN
         b := 1;
      ELSE
         b := 0;
      END IF;
      BitStream_AppendBit(S, I, b);
   END  UPER_Enc_Boolean;


   PROCEDURE UPER_Dec_boolean(S : in BitArray; P : in out DECODE_PARAMS; val:OUT Asn1Boolean; result:OUT Boolean)
   IS
      v:BIT;
   BEGIN
       BitStream_ReadBit(S,P,v, result);
       val := v=1;
   END UPER_Dec_boolean;


   FUNCTION GetExponent(V:Asn1Real) return Asn1Int
   IS
      --# hide GetExponent;
      --due to the fact that Examiner has not yet implement the Exponent attribute
   BEGIN
      RETURN Asn1Int(Asn1Real'Exponent(V) - Asn1Real'Machine_Mantissa);
   END GetExponent;

   FUNCTION GetMantissa(V:Asn1Real) return Asn1UInt
   IS
      --# hide GetMantissa;
      --due to the fact that Examiner has not yet implement the Fraction attribute
   BEGIN
      RETURN Asn1UInt(Asn1Real'Fraction(V)* MantissaFactor);
   END GetMantissa;


   PROCEDURE UPER_Enc_Real(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
   IS
      Header   : Interfaces.Unsigned_8 := 16#80#;
      NExpLen  : Integer;
      NManLen  : Integer;
      Exp      : Asn1Int;
      Mantissa : Asn1UInt;
      V        : Asn1Real;
   BEGIN

      IF RealVal>=0.0 AND RealVal<=0.0 THEN
         BitStream_AppendByte(S, K, 0, FALSE);
      ELSIF RealVal = PLUS_INFINITY THEN
         BitStream_AppendByte(S, K, 1, FALSE);
         BitStream_AppendByte(S, K, 16#40#, FALSE);
      ELSIF RealVal = MINUS_INFINITY THEN
         BitStream_AppendByte(S, K, 1, FALSE);
         BitStream_AppendByte(S, K, 16#41#, FALSE);
      ELSE
      	 V := RealVal;

         IF V < 0.0 THEN
            V:= -V;
            HEADER := HEADER OR 16#40#;
         END IF;

         Exp := GetExponent(V);
         Mantissa := GetMantissa(V);

         NExpLen := GetLengthInBytesOfSInt(Exp);
         NManLen := GetBytes(Mantissa);

         IF NExpLen >=4 THEN
            NExpLen := 3;
         END IF;

         IF NExpLen = 2 THEN
            Header := Header OR 1;
         ELSIF NExpLen = 3 THEN
            Header := Header OR 2;
         END IF;

         --#check NExpLen>=1 AND NExpLen<=3;

         -- encode length
         BitStream_AppendByte(S, K, Interfaces.Unsigned_8((1+NExpLen)+NManLen), FALSE); --1

         -- encode header
         BitStream_AppendByte(S, K, Header, FALSE); --1

         -- encode exponent
         Enc_UInt(S, K, To_UInt(Exp), NExpLen); --max 3 octets

         -- encode mantissa
         Enc_UInt(S, K, Mantissa, NManLen); --max 8 octets
      END IF;
   END UPER_Enc_Real;


    FUNCTION CalcReal(Factor:Asn1UInt;N : Asn1UInt; base:Integer; Exp:Integer) RETURN Asn1Real
    --# pre base=2 OR base=8 OR base=16;
    IS
      --# hide CalcReal;
    BEGIN
        RETURN Asn1Real(Factor*N)*Asn1Real(Base)**Exp;
    END CalcReal;

    PROCEDURE UPER_Dec_Real_AsBinary_aux (
        S         : IN     BitArray;
        K         : in out DECODE_PARAMS;
        ExpLen    : IN     Interfaces.Unsigned_8;
        Length    : IN     Interfaces.Unsigned_8;
        Factor    : IN     Asn1UInt;
        Sign      : IN     Integer;
        Base      : IN     Integer;
        RealVal   : OUT    Asn1Real;
        Result    : OUT    ASN1_RESULT)
    --# derives K from K, ExpLen, Length &
    --#         RealVal from S, K, ExpLen, Length, Factor, Sign, Base &
    --#         Result  from  S, K, ExpLen, Length;
    --# pre  K.K+1>= S'First and K.K + 88 <= S'Last AND (base=2 OR base=8 OR base=16) AND ExpLen>=1;
    --# post K.K >= K~.K  and K.K <=K~.K+88;
    IS
        Exp       : Asn1Int;
        N         : Asn1UInt ;
    BEGIN
        RealVal:=0.0;
        Result := ASN1_RESULT'(Success   => FALSE, ErrorCode => ERR_END_OF_STREAM);
        IF ExpLen<Length AND ExpLen<=3 THEN
            Dec_Int(S, K, Integer(ExpLen), Exp,result.Success);

            IF result.Success AND Length-ExpLen<=8 THEN
                Dec_UInt(S,K,Integer(Length-ExpLen),N,result.Success);
          	IF result.Success AND Exp>Asn1Int(Integer'First) AND Exp<Asn1Int(Integer'Last)  THEN
		    RealVal := CalcReal(Factor,N,base,Integer(Exp));

                    IF Sign<0 THEN
                       RealVal:=- RealVal;
                    END IF;

                    Result := ASN1_RESULT'(Success   => TRUE, ErrorCode => 0);
                END IF;
            END IF;
    	END IF;
    END UPER_Dec_Real_AsBinary_aux;


    PROCEDURE UPER_Dec_Real_AsBinary (
        S         : IN     BitArray;
        K         : in out DECODE_PARAMS;
        Header    : IN     Interfaces.Unsigned_8;
        EncLength : IN     Interfaces.Unsigned_8;
        RealVal   : OUT    Asn1Real;
        Result    : OUT    ASN1_RESULT)
    --# derives K from K, Header, EncLength &
    --#         RealVal from S, Header, K, EncLength &
    --#         Result  from  S, Header, K, EncLength;
    --# pre  K.K+1>= S'First and K.K + 88 <= S'Last AND EncLength<=11;
    --# post K.K >= K~.K  and K.K <=K~.K+88;

    IS
        Sign          : Integer    := 1;
        Base          : Integer    := 2;
        F             : Interfaces.Unsigned_8;
        Factor        : Asn1UInt   := 1;
        ExpLen        : Interfaces.Unsigned_8;

    BEGIN

        IF (Header AND 16#40#)>0 THEN
            Sign := -1;
        END IF;

        IF (Header AND 16#10#)>0 THEN
            Base := 8;
        ELSIF (Header AND 16#20#)>0 THEN
            Base := 16;
        END IF;

        F:= (Header AND 16#0C#)/4;
        Factor:=Factor*(2**Integer(F));


        ExpLen := (Header AND 16#03#) + 1;

  	UPER_Dec_Real_AsBinary_aux(S, K, ExpLen, EncLength, Factor, Sign, Base, RealVal, Result);

     END UPER_Dec_Real_AsBinary;


    PROCEDURE UPER_Dec_Real (
        S       : IN     BitArray;
        K       : in out DECODE_PARAMS;
        RealVal : OUT    Asn1Real;
        Result  : OUT    ASN1_RESULT)
    IS
        Header : Interfaces.Unsigned_8;
        Length : Interfaces.Unsigned_8;
    BEGIN
       RealVal:=0.0;
       Result := ASN1_RESULT'(Success   => FALSE, ErrorCode => ERR_END_OF_STREAM);

       BitStream_DecodeByte (S, K, Length, Result.Success);
       IF Result.Success AND  Length<=12 THEN
           IF Length > 0 THEN
               BitStream_DecodeByte (S, K, Header, Result.Success);
               IF Result.Success  THEN
                   IF Header=16#40# THEN
                       RealVal:= PLUS_INFINITY;
                       Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => 0);
                   ELSIF Header=16#41# THEN
                       RealVal:= MINUS_INFINITY;
                       Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => 0);
                   ELSIF (Header AND 16#80#)>0 THEN
                       UPER_Dec_Real_AsBinary(S, K, Header, Length-1, RealVal, Result);
                   ELSE
       		       Result := ASN1_RESULT'(Success   => FALSE, ErrorCode => ERR_UNSUPPORTED_ENCODING);
                   END IF;
               END IF;
           ELSE
              Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => 0);
           END IF;
       END IF;
     END UPER_Dec_Real;


        ---# assert I>=AllowedCharSet'FIRST AND I<=AllowedCharSet'LAST AND AllowedCharSet'First=1 AND
        ---# AllowedCharSet'Last>=AllowedCharSet'First AND AllowedCharSet'Last<=INTEGER'LAST-1 AND
        ---# ret=I-AllowedCharSet'First;


    FUNCTION GetZeroBasedCharIndex (CharToSearch : Character; AllowedCharSet : IN String) RETURN Integer
    IS
    	ret:INTEGER;
    BEGIN
    	ret:=0;
        FOR I IN INTEGER range AllowedCharSet'RANGE LOOP
	    ret:=I-AllowedCharSet'First;
        --# assert I>=AllowedCharSet'FIRST AND I<=AllowedCharSet'LAST AND
        --# AllowedCharSet'Last>=AllowedCharSet'First AND AllowedCharSet'Last<=INTEGER'LAST-1 AND
        --# ret=I-AllowedCharSet'First;
            exit when CharToSearch=AllowedCharSet(I);
       END LOOP;
       return ret;
    END GetZeroBasedCharIndex;

    FUNCTION CharacterPos(C : Character) RETURN Integer
    IS
    	ret:INTEGER;
    BEGIN
    	ret := Character'Pos(C);
        IF NOT (ret>=0 AND ret<=127) THEN
            ret := 0;
        END IF;
        RETURN ret;
    END CharacterPos;









-- ACN Functions


    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int; Size:IN Integer)
    IS
    BEGIN
        UPER_Enc_ConstraintWholeNumber(S, K, IntVal, 0, Size);
    END Acn_Enc_Int_PositiveInteger_ConstSize;


    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_8 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        UPER_Enc_ConstraintWholeNumber(S, K, IntVal, 0, 8);
    END Acn_Enc_Int_PositiveInteger_ConstSize_8;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        UPER_Enc_ConstraintWholeNumber(S, K, IntVal, 0, 16);
    END Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_16;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        UPER_Enc_ConstraintWholeNumber(S, K, IntVal, 0, 32);
    END Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_32;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        UPER_Enc_ConstraintWholeNumber(S, K, IntVal, 0, 64);
    END Acn_Enc_Int_PositiveInteger_ConstSize_big_endian_64;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
	tmp : OctetArray2;
    BEGIN
    	tmp := UInt16_to_OctetArray2(To_UInt16(IntVal));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN  RANGE_1_2 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN reverse RANGE_1_2 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_16;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
	tmp : OctetArray4;
    BEGIN
    	tmp := UInt32_to_OctetArray4(To_UInt32(IntVal));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN  RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN reverse RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_32;

    PROCEDURE Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
	tmp : OctetArray8;
    BEGIN
    	tmp := Asn1UInt_to_OctetArray8(To_UInt(IntVal));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN  RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN reverse RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Int_PositiveInteger_ConstSize_little_endian_64;


    PROCEDURE Acn_Enc_Int_PositiveInteger_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        UPER_Enc_SemiConstraintWholeNumber(S, K, IntVal, 0);
    END Acn_Enc_Int_PositiveInteger_VarSize_LengthEmbedded;


    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int; Size:IN Integer)
    IS
    BEGIN
    	BitStream_Encode_Non_Negative_Integer(S,K,To_UInt(IntVal), Size);
    END Acn_Enc_Int_TwosComplement_ConstSize;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_8 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        Acn_Enc_Int_TwosComplement_ConstSize(S, K, IntVal, 8);
    END Acn_Enc_Int_TwosComplement_ConstSize_8;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_big_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        Acn_Enc_Int_TwosComplement_ConstSize(S, K, IntVal, 16);
    END Acn_Enc_Int_TwosComplement_ConstSize_big_endian_16;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_big_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        Acn_Enc_Int_TwosComplement_ConstSize(S, K, IntVal, 32);
    END Acn_Enc_Int_TwosComplement_ConstSize_big_endian_32;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_big_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        Acn_Enc_Int_TwosComplement_ConstSize(S, K, IntVal, 64);
    END Acn_Enc_Int_TwosComplement_ConstSize_big_endian_64;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_little_endian_16 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
	tmp : OctetArray2;
    BEGIN
    	tmp := UInt16_to_OctetArray2(Int16_UInt16(Interfaces.Integer_16(IntVal)));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN  RANGE_1_2 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN reverse RANGE_1_2 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Int_TwosComplement_ConstSize_little_endian_16;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_little_endian_32 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
	tmp : OctetArray4;
    BEGIN
    	tmp := UInt32_to_OctetArray4(Int32_UInt32(Interfaces.Integer_32(IntVal)));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN  RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN reverse RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Int_TwosComplement_ConstSize_little_endian_32;

    PROCEDURE Acn_Enc_Int_TwosComplement_ConstSize_little_endian_64 (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
	tmp : OctetArray8;
    BEGIN
    	tmp := Asn1UInt_to_OctetArray8(To_UInt(IntVal));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN  RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN reverse RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Int_TwosComplement_ConstSize_little_endian_64;


    PROCEDURE Acn_Enc_Int_TwosComplement_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
    BEGIN
        UPER_Enc_UnConstraintWholeNumber(S, K, IntVal);
    END Acn_Enc_Int_TwosComplement_VarSize_LengthEmbedded;



    PROCEDURE Acn_Enc_Int_BCD_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int; nNibbles:IN Integer)
    IS
        totalNibbles:Integer:=1;
        tmp  : OctetArray100 := OctetArray100'(others => 0);
        intValCopy : Asn1Int;
    BEGIN
        intValCopy := IntVal;
        WHILE intValCopy>0 and totalNibbles<=nNibbles LOOP
        --# assert totalNibbles>=1 and totalNibbles>=1 and totalNibbles<=nNibbles and K~ + 1>=S'First and K~ + 4*nNibbles <= S'Last and K~=K;
            tmp(totalNibbles) := Interfaces.Unsigned_8(intValCopy MOD 10);
            totalNibbles := totalNibbles + 1;
            intValCopy := intValCopy / 10;
        END LOOP;


        FOR I IN REVERSE INTEGER range 1..nNibbles LOOP
        --# assert K~ + 1>=S'First and K~ + 4*nNibbles <= S'Last and K = K~ + (nNibbles-I)*4;
            BitStream_AppendPartialByte(S, K, tmp(i), 4, FALSE);
        END LOOP;
    END Acn_Enc_Int_BCD_ConstSize;

    PROCEDURE Acn_Enc_Int_BCD_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
      --# hide Acn_Enc_Int_BCD_VarSize_LengthEmbedded;
    BEGIN
        null;
    END Acn_Enc_Int_BCD_VarSize_LengthEmbedded;

    PROCEDURE Acn_Enc_Int_BCD_VarSize_NullTerminated(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
        totalNibbles:Integer:=1;
        tmp  : OctetArray100 := OctetArray100'(others => 0);
        intValCopy : Asn1Int;
    BEGIN
        intValCopy := IntVal;
        WHILE intValCopy>0 and totalNibbles<=18 LOOP
        --# assert totalNibbles>=1 and totalNibbles<=18 and K~ + 1>=S'First and K~ + 76 <= S'Last and K~=K;
            tmp(totalNibbles) := Interfaces.Unsigned_8(intValCopy MOD 10);
            totalNibbles := totalNibbles + 1;
            intValCopy := intValCopy / 10;
        END LOOP;

	totalNibbles:= totalNibbles - 1;

        FOR I IN REVERSE INTEGER range 1..totalNibbles LOOP
        --# assert totalNibbles>=1 and totalNibbles<=18 and K~ + 1>=S'First and K~ + 76 <= S'Last and K = K~ + (totalNibbles-I)*4;
            BitStream_AppendPartialByte(S, K, tmp(i), 4, FALSE);
        END LOOP;
        BitStream_AppendPartialByte(S, K, 16#F#, 4, FALSE);

    END Acn_Enc_Int_BCD_VarSize_NullTerminated;



    PROCEDURE Acn_Enc_Int_ASCII_VarSize_LengthEmbedded(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
      --# hide Acn_Enc_Int_ASCII_VarSize_LengthEmbedded;
    BEGIN
        null;
    END Acn_Enc_Int_ASCII_VarSize_LengthEmbedded;

    PROCEDURE Acn_Enc_Int_ASCII_VarSize_NullTerminated(S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int)
    IS
      --# hide Acn_Enc_Int_ASCII_VarSize_NullTerminated;
    BEGIN
        null;
    END Acn_Enc_Int_ASCII_VarSize_NullTerminated;






    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; nSizeInBits:IN Integer; Result:OUT ASN1_RESULT)
    IS
        encVal : Asn1UInt;
    BEGIN
    	result.ErrorCode := 0;
        BitStream_Decode_Non_Negative_Integer(S, K, encVal, nSizeInBits, result.Success);
        IF result.Success THEN
            IntVal := To_Int(encVal + To_UInt(adjustVal));

            Result.Success := IntVal>= MinVal AND IntVal <=MaxVal;
            IF NOT Result.Success THEN
                IntVal := MinVal;
                Result.ErrorCode := ERR_INCORRECT_STREAM;
            END IF;
        ELSE
            IntVal := minVal;
            Result.ErrorCode := ERR_INCORRECT_STREAM;
        END IF;
    END Acn_Dec_Int_PositiveInteger_ConstSize;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_8(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
        Acn_Dec_Int_PositiveInteger_ConstSize(S, K, IntVal, adjustVal, minVal, maxVal, 8, result);
    END Acn_Dec_Int_PositiveInteger_ConstSize_8;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
         Acn_Dec_Int_PositiveInteger_ConstSize(S, K, IntVal, adjustVal, minVal, maxVal, 16, result);
    END Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_16;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
         Acn_Dec_Int_PositiveInteger_ConstSize(S, K, IntVal, adjustVal, minVal, maxVal, 32, result);
    END Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_32;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
         Acn_Dec_Int_PositiveInteger_ConstSize(S, K, IntVal, adjustVal, minVal, maxVal, 64, result);
    END Acn_Dec_Int_PositiveInteger_ConstSize_big_endian_64;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
        PRAGMA Unreferenced(adjustVal);
	tmp : OctetArray2:=OctetArray2'(others=>0);
        I   : INTEGER;
        ret : Asn1Int;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        ret := MinVal;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_2'Last;
            WHILE Result.Success AND I>=RANGE_1_2'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_2'First;
            WHILE Result.Success AND I<=RANGE_1_2'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    ret := Asn1Int(OctetArray2_to_UInt16(tmp));
            Result.Success := ret>= MinVal AND ret <=MaxVal;
        END IF;
        IF Result.Success THEN
            IntVal := ret;
        ELSE
            IntVal := MinVal;
        END IF;
    END Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_16;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
        PRAGMA Unreferenced(adjustVal);
	tmp : OctetArray4:=OctetArray4'(others=>0);
        I   : INTEGER;
        ret : Asn1Int;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        ret := MinVal;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_4'Last;
            WHILE Result.Success AND I>=RANGE_1_4'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_4'First;
            WHILE Result.Success AND I<=RANGE_1_4'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    ret := Asn1Int(OctetArray4_to_UInt32(tmp));
            Result.Success := ret>= MinVal AND ret <=MaxVal;
        END IF;
        IF Result.Success THEN
            IntVal := ret;
        ELSE
            IntVal := MinVal;
        END IF;
    END Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_32;

    PROCEDURE Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
        PRAGMA Unreferenced(adjustVal);
	tmp : OctetArray8:=OctetArray8'(others=>0);
        I   : INTEGER;
        ret : Asn1Int;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        ret := MinVal;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_8'Last;
            WHILE Result.Success AND I>=RANGE_1_8'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_8'First;
            WHILE Result.Success AND I<=RANGE_1_8'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    ret := To_Int(OctetArray8_to_Asn1UInt(tmp));
            Result.Success := ret>= MinVal AND ret <=MaxVal;
        END IF;
        IF Result.Success THEN
            IntVal := ret;
        ELSE
            IntVal := MinVal;
        END IF;
    END Acn_Dec_Int_PositiveInteger_ConstSize_little_endian_64;


    PROCEDURE Acn_Dec_Int_PositiveInteger_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; adjustVal:IN Asn1Int; minVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
      NBytes  : Asn1Int;
      Ret     : Asn1UInt;
   BEGIN

      IntVal := MinVal;
      result.ErrorCode := 0;
      UPER_Dec_ConstraintWholeNumber(S,K,NBytes,0,255,8,result.Success);
      IF Result.Success AND NBytes>=1 AND NBytes<=8 THEN
            Dec_UInt(S, K, Integer(nBytes), Ret, result.Success);
            IF result.Success THEN
                IntVal := To_Int(Ret + To_UInt(adjustVal));
                Result.Success := IntVal>= MinVal;
                IF NOT Result.Success THEN
                     IntVal := MinVal;
      	             result.ErrorCode := ERR_INCORRECT_STREAM;
                END IF;
            ELSE
  	        result.ErrorCode := ERR_INCORRECT_STREAM;
            END IF;
      ELSE
      	 result.ErrorCode := ERR_INCORRECT_STREAM;
      	 Result.Success :=FALSE;
      END IF;
    END Acn_Dec_Int_PositiveInteger_VarSize_LengthEmbedded;


    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; nSizeInBits:IN Integer; Result:OUT ASN1_RESULT)
    IS
        encVal : Asn1UInt;
    BEGIN
    	result.ErrorCode := 0;
        BitStream_Decode_Non_Negative_Integer(S, K, encVal, nSizeInBits, result.Success);
        IF result.Success THEN
            IntVal := To_Int_n(encVal, nSizeInBits);
            Result.Success := IntVal>= MinVal AND IntVal<=maxVal;
            IF NOT Result.Success THEN
                IntVal := minVal;
                Result.ErrorCode := ERR_INCORRECT_STREAM;
            END IF;
        ELSE
            IntVal := minVal;
            Result.ErrorCode := ERR_INCORRECT_STREAM;
        END IF;
    END Acn_Dec_Int_TwosComplement_ConstSize;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_8(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
        Acn_Dec_Int_TwosComplement_ConstSize(S, K, IntVal, minVal, maxVal, 8, Result);
    END Acn_Dec_Int_TwosComplement_ConstSize_8;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_big_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
        Acn_Dec_Int_TwosComplement_ConstSize(S, K, IntVal, minVal, maxVal, 16, Result);
    END Acn_Dec_Int_TwosComplement_ConstSize_big_endian_16;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_big_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
        Acn_Dec_Int_TwosComplement_ConstSize(S, K, IntVal, minVal, maxVal, 32, Result);
    END Acn_Dec_Int_TwosComplement_ConstSize_big_endian_32;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_big_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
        Acn_Dec_Int_TwosComplement_ConstSize(S, K, IntVal, minVal, maxVal, 64, Result);
    END Acn_Dec_Int_TwosComplement_ConstSize_big_endian_64;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_little_endian_16(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray2:=OctetArray2'(others=>0);
        I   : INTEGER;
        ret : Asn1Int;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        ret := MinVal;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_2'Last;
            WHILE Result.Success AND I>=RANGE_1_2'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_2'First;
            WHILE Result.Success AND I<=RANGE_1_2'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    ret := Asn1Int(UInt16_Int16(OctetArray2_to_UInt16(tmp)));
            Result.Success := ret>= MinVal AND ret <=MaxVal;
        END IF;
        IF Result.Success THEN
            IntVal := ret;
        ELSE
            IntVal := MinVal;
        END IF;
    END Acn_Dec_Int_TwosComplement_ConstSize_little_endian_16;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_little_endian_32(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray4:=OctetArray4'(others=>0);
        I   : INTEGER;
        ret : Asn1Int;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        ret := MinVal;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_4'Last;
            WHILE Result.Success AND I>=RANGE_1_4'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_4'First;
            WHILE Result.Success AND I<=RANGE_1_4'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    ret :=  Asn1Int(UInt32_Int32(OctetArray4_to_UInt32(tmp)));
            Result.Success := ret>= MinVal AND ret <=MaxVal;
        END IF;
        IF Result.Success THEN
            IntVal := ret;
        ELSE
            IntVal := MinVal;
        END IF;
    END Acn_Dec_Int_TwosComplement_ConstSize_little_endian_32;

    PROCEDURE Acn_Dec_Int_TwosComplement_ConstSize_little_endian_64(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray8:=OctetArray8'(others=>0);
        I   : INTEGER;
        ret : Asn1Int;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        ret := MinVal;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_8'Last;
            WHILE Result.Success AND I>=RANGE_1_8'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_8'First;
            WHILE Result.Success AND I<=RANGE_1_8'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    ret := To_Int(OctetArray8_to_Asn1UInt(tmp));
            Result.Success := ret>= MinVal AND ret <=MaxVal;
        END IF;
        IF Result.Success THEN
            IntVal := ret;
        ELSE
            IntVal := MinVal;
        END IF;
    END Acn_Dec_Int_TwosComplement_ConstSize_little_endian_64;







    FUNCTION UInt16_to_OctetArray2(x:Interfaces.Unsigned_16) RETURN OctetArray2
    IS
        --# hide UInt16_to_OctetArray2;
        function do_it IS NEW Ada.Unchecked_Conversion(Interfaces.Unsigned_16, OctetArray2);
    BEGIN
        RETURN do_it(x);
    END UInt16_to_OctetArray2;

    FUNCTION OctetArray2_to_UInt16(x:OctetArray2) RETURN Interfaces.Unsigned_16
    IS
        --# hide OctetArray2_to_UInt16;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray2, Interfaces.Unsigned_16);
    BEGIN
        RETURN do_it(x);
    END OctetArray2_to_UInt16;


    FUNCTION UInt32_to_OctetArray4(x:Interfaces.Unsigned_32) RETURN OctetArray4
    IS
        --# hide UInt32_to_OctetArray4;
        function do_it IS NEW Ada.Unchecked_Conversion(Interfaces.Unsigned_32, OctetArray4);
    BEGIN
        RETURN do_it(x);
    END UInt32_to_OctetArray4;

    FUNCTION OctetArray4_to_UInt32(x:OctetArray4) RETURN Interfaces.Unsigned_32
    IS
        --# hide OctetArray4_to_UInt32;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray4, Interfaces.Unsigned_32);
    BEGIN
        RETURN do_it(x);
    END OctetArray4_to_UInt32;


    FUNCTION Asn1UInt_to_OctetArray8(x:Asn1UInt) RETURN OctetArray8
    IS
        --# hide Asn1UInt_to_OctetArray8;
        function do_it  IS NEW Ada.Unchecked_Conversion(Asn1UInt, OctetArray8);
    BEGIN
        RETURN do_it(x);
    END Asn1UInt_to_OctetArray8;

    FUNCTION OctetArray8_to_Asn1UInt(x:OctetArray8) RETURN Asn1UInt
    IS
        --# hide OctetArray8_to_Asn1UInt;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray8, Asn1UInt);
    BEGIN
        RETURN do_it(x);
    END OctetArray8_to_Asn1UInt;



   FUNCTION Int16_to_OctetArray2(x:Interfaces.Integer_16) RETURN OctetArray2
   IS
   	--# hide Int16_to_OctetArray2;
        function do_it IS NEW Ada.Unchecked_Conversion(Interfaces.Integer_16, OctetArray2);
   BEGIN
   	RETURN do_it(x);
   END Int16_to_OctetArray2;

   FUNCTION OctetArray2_to_Int16(x:OctetArray2) RETURN Interfaces.Integer_16
   IS
   	--# hide OctetArray2_to_Int16;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray2, Interfaces.Integer_16);
   BEGIN
   	RETURN do_it(x);
   END OctetArray2_to_Int16;


   FUNCTION Int32_to_OctetArray4(x:Interfaces.Integer_32) RETURN OctetArray4
   IS
   	--# hide Int32_to_OctetArray4;
        function do_it IS NEW Ada.Unchecked_Conversion(Interfaces.Integer_32, OctetArray4);
   BEGIN
   	RETURN do_it(x);
   END Int32_to_OctetArray4;

   FUNCTION OctetArray4_to_Int32(x:OctetArray4) RETURN Interfaces.Integer_32
   IS
   	--# hide OctetArray4_to_Int32;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray4, Interfaces.Integer_32);
   BEGIN
   	RETURN do_it(x);
   END OctetArray4_to_Int32;


   FUNCTION Asn1Int_to_OctetArray8(x:Asn1Int) RETURN OctetArray8
   IS
   	--# hide Asn1Int_to_OctetArray8;
        function do_it  IS NEW Ada.Unchecked_Conversion(Asn1Int, OctetArray8);
   BEGIN
   	RETURN do_it(x);
   END Asn1Int_to_OctetArray8;

   FUNCTION OctetArray8_to_Asn1Int(x:OctetArray8) RETURN Asn1Int
   IS
   	--# hide OctetArray8_to_Asn1Int;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray8, Asn1Int);
   BEGIN
   	RETURN do_it(x);
   END OctetArray8_to_Asn1Int;















   FUNCTION Float_to_OctetArray4(x:Float) RETURN OctetArray4
   IS
   	--# hide Float_to_OctetArray4;
        function do_it IS NEW Ada.Unchecked_Conversion(Float, OctetArray4);
   BEGIN
   	RETURN do_it(x);
   END Float_to_OctetArray4;

   FUNCTION Long_Float_to_OctetArray8(x:Asn1Real) RETURN OctetArray8
   IS
   	--# hide Long_Float_to_OctetArray8;
        function do_it  IS NEW Ada.Unchecked_Conversion(Asn1Real, OctetArray8);
   BEGIN
   	RETURN do_it(x);
   END Long_Float_to_OctetArray8;


   FUNCTION OctetArray4_to_Float(x:OctetArray4) RETURN Float
   IS
   	--# hide OctetArray4_to_Float;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray4, Float);
   BEGIN
   	RETURN do_it(x);
   END OctetArray4_to_Float;

   FUNCTION OctetArray8_to_Long_Float(x:OctetArray8) RETURN Asn1Real
   IS
   	--# hide OctetArray8_to_Long_Float;
        function do_it IS NEW Ada.Unchecked_Conversion(OctetArray8, Asn1Real);
   BEGIN
   	RETURN do_it(x);
   END OctetArray8_to_Long_Float;



    PROCEDURE Acn_Dec_Int_TwosComplement_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    IS
    BEGIN
    	Result.ErrorCode := ERR_INCORRECT_STREAM;
        UPER_Dec_UnConstraintWholeNumber(S, K, IntVal,Result.Success);
    END Acn_Dec_Int_TwosComplement_VarSize_LengthEmbedded;


    PROCEDURE Acn_Dec_Int_BCD_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; nNibbles:IN Integer; Result:OUT ASN1_RESULT)
    IS
        digit:Asn1Byte;
        I : Integer;
        max_aux : CONSTANT Asn1Int := Asn1Int'Last/10 - 9;
    BEGIN
        intVal:=0;
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        I := nNibbles;
        WHILE I>0 AND Result.Success LOOP
        --# assert K~.K+1>= S'First and  K~.K + 4*nNibbles <= S'Last and
        --#        I>0 and I<=nNibbles and
        --#        K.K = K~.K + (nNibbles-I)*4;
            BitStream_ReadNibble(S, K, digit, Result.Success);

            Result.Success := Result.Success AND digit<=9 AND intVal>=0 AND intVal <=max_aux;
            IF Result.Success THEN
                intVal := intVal*10;
                intVal := intVal + Asn1Int(digit);
                I:= I -1;
            END IF;
        END LOOP;

	Result.Success := Result.Success AND THEN ((IntVal>= minVal) AND (IntVal <=maxVal));
	IF NOT Result.Success THEN
            intVal:=minVal;
        END IF;
    END Acn_Dec_Int_BCD_ConstSize;

    PROCEDURE Acn_Dec_Int_BCD_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    IS
      --# hide Acn_Dec_Int_BCD_VarSize_LengthEmbedded;
    BEGIN
        null;
    END Acn_Dec_Int_BCD_VarSize_LengthEmbedded;

    PROCEDURE Acn_Dec_Int_BCD_VarSize_NullTerminated(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; Result:OUT ASN1_RESULT)
    IS
        digit:Asn1Byte;
        I : Integer;
        max_aux : CONSTANT Asn1Int := Asn1Int'Last/10 - 9;
        stopDigitFound : BOOLEAN :=FALSE;
    BEGIN
        intVal:=0;
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        I := 0;
        WHILE Result.Success AND (NOT stopDigitFound) AND I <18 LOOP
        --# assert K~.K+1>= S'First and  K~.K + 76 <= S'Last and
        --#        I>=0 and I<18 and
        --#        K.K = K~.K + I*4;
            BitStream_ReadNibble(S, K, digit, Result.Success);

            Result.Success := Result.Success AND (digit<=9 OR digit=16#F#) AND intVal>=0 AND intVal <=max_aux;
            stopDigitFound := digit=16#F#;
            IF Result.Success AND (NOT stopDigitFound) THEN
                intVal := intVal*10;
                intVal := intVal + Asn1Int(digit);
            END IF;
            I:= I + 1;
        END LOOP;

	Result.Success := Result.Success AND THEN ((IntVal>= minVal) AND (IntVal <=maxVal));
	IF NOT Result.Success THEN
            intVal:=minVal;
        END IF;
    END Acn_Dec_Int_BCD_VarSize_NullTerminated;

    PROCEDURE Acn_Enc_Int_ASCII_ConstSize (S : in out BitArray; K : in out Natural; IntVal:IN Asn1Int; nChars:IN Integer)
    IS
        I : INTEGER;
        tmp  : OctetArray100 := OctetArray100'(others => Character'Pos('0'));
        intValCopy : Asn1Int;
    BEGIN
    	IF IntVal>=0 THEN
            tmp(1) := Character'Pos('+');
            intValCopy := IntVal;
        ELSE
            tmp(1) := Character'Pos('-');
            intValCopy := -IntVal;
        END IF;

        I := nChars;
        WHILE intValCopy>0 and I>=2 LOOP
        --# assert I>=2 and I<=nChars and K~ + 1>=S'First and K~ + 8*nChars <= S'Last and K~=K;
            tmp(I) := Interfaces.Unsigned_8(Character'Pos('0') + (intValCopy MOD 10));
            I := I - 1;
            intValCopy := intValCopy / 10;
        END LOOP;

        FOR J IN INTEGER range 1..nChars LOOP
        --# assert K~ + 1>=S'First and K~ + 8*nChars <= S'Last and K = K~ + (J-1)*8;
            BitStream_AppendByte(S, K, tmp(J), FALSE);
        END LOOP;
    END Acn_Enc_Int_ASCII_ConstSize;

    PROCEDURE Acn_Dec_Int_ASCII_ConstSize (S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; minVal:IN Asn1Int; maxVal:IN Asn1Int; nChars:IN Integer; Result:OUT ASN1_RESULT)
    IS
        digit: Asn1Byte;
        Ch   : Character;

        I : Integer;
        max_aux : CONSTANT Asn1Int := Asn1Int'Last/10 - 9;
	negative:BOOLEAN:=FALSE;
    BEGIN
        intVal:=0;
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        BitStream_DecodeByte(S, K, digit, Result.Success);
        IF Result.Success THEN
       	    IF digit = Character'Pos('+') THEN
                negative := FALSE;
            ELSIF digit = Character'Pos('-') THEN
                negative := TRUE;
            ELSE
                Result.Success := FALSE;
            END IF;
            I := nChars-1;
            WHILE I>0 AND Result.Success LOOP
                --# assert K~.K+1>= S'First and  K~.K + 8*nChars <= S'Last and
                --#        I>0 and I<=nChars-1 and
                --#        K.K = K~.K + (nChars-I)*8;
                BitStream_DecodeByte(S, K, digit, Result.Success);
                ch := Character'Val(digit);
                digit := Character'Pos(ch) - Character'Pos('0');

                Result.Success := Result.Success AND digit<=9 AND intVal>=0 AND intVal <=max_aux;
                IF Result.Success THEN
                    intVal := intVal*10;
                    intVal := intVal + Asn1Int(digit);
                    I:= I -1;
                END IF;
            END LOOP;
            IF negative AND IntVal>Asn1Int'First THEN
		IntVal := -IntVal;
            END IF;

            Result.Success := Result.Success AND THEN ((IntVal>= minVal) AND (IntVal <=maxVal));
        END IF;
	IF NOT Result.Success THEN
            intVal:=minVal;
        END IF;
    END Acn_Dec_Int_ASCII_ConstSize;

    PROCEDURE Acn_Dec_Int_ASCII_VarSize_LengthEmbedded(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    IS
      --# hide Acn_Dec_Int_ASCII_VarSize_LengthEmbedded;
    BEGIN
        null;
    END Acn_Dec_Int_ASCII_VarSize_LengthEmbedded;

    PROCEDURE Acn_Dec_Int_ASCII_VarSize_NullTerminated(S : in BitArray; K : in out DECODE_PARAMS; IntVal:OUT Asn1Int; Result:OUT ASN1_RESULT)
    IS
      --# hide Acn_Dec_Int_ASCII_VarSize_NullTerminated;
    BEGIN
        null;
    END Acn_Dec_Int_ASCII_VarSize_NullTerminated;


    FUNCTION Long_Float_to_Float(x:Asn1Real) RETURN Float
    IS
        --# hide Long_Float_to_Float;
    BEGIN
        RETURN float(x);
    END Long_Float_to_Float;

    PROCEDURE Acn_Enc_Real_IEEE754_32_big_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    IS
	tmp : OctetArray4;
    BEGIN
    	tmp := Float_to_OctetArray4(Long_Float_to_Float(RealVal));
	IF RequiresReverse(K>0) THEN
		FOR I IN reverse RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 32 <= S'Last and K = K~ + 8*(4-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 32 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Real_IEEE754_32_big_endian;

    PROCEDURE Acn_Dec_Real_IEEE754_32_big_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray4:=OctetArray4'(others=>0);
        I   : INTEGER;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        RealVal := 0.0;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_4'Last;
            WHILE Result.Success AND I>=RANGE_1_4'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 32 <= S'Last and K.K = K~.K + 8*(4-I) AND I>=1 AND I<=4;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_4'First;
            WHILE Result.Success AND I<=RANGE_1_4'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 32 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=4;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    RealVal := Asn1Real(OctetArray4_to_Float(tmp));
        END IF;
    END Acn_Dec_Real_IEEE754_32_big_endian;

    PROCEDURE Acn_Enc_Real_IEEE754_64_big_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    IS
	tmp : OctetArray8;
    BEGIN
    	tmp := Long_Float_to_OctetArray8(RealVal);
	IF RequiresReverse(K>0) THEN
		FOR I IN reverse RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Real_IEEE754_64_big_endian;

    PROCEDURE Acn_Dec_Real_IEEE754_64_big_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray8:=OctetArray8'(others=>0);
        I   : INTEGER;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        RealVal := 0.0;
	IF RequiresReverse(K.K>0) THEN
            I:=RANGE_1_8'Last;
            WHILE Result.Success AND I>=RANGE_1_8'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_8'First;
            WHILE Result.Success AND I<=RANGE_1_8'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    RealVal := OctetArray8_to_Long_Float(tmp);
        END IF;
    END Acn_Dec_Real_IEEE754_64_big_endian;

    PROCEDURE Acn_Enc_Real_IEEE754_32_little_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    IS
	tmp : OctetArray4;
    BEGIN
    	tmp := Float_to_OctetArray4(Long_Float_to_Float(RealVal));
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN reverse RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 32 <= S'Last and K = K~ + 8*(4-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN RANGE_1_4 LOOP
                --# assert K~+1>= S'First and K~ + 32 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Real_IEEE754_32_little_endian;

    PROCEDURE Acn_Dec_Real_IEEE754_32_little_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray4:=OctetArray4'(others=>0);
        I   : INTEGER;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        RealVal := 0.0;
	IF NOT RequiresReverse(K.K>0) THEN
            I:=RANGE_1_4'Last;
            WHILE Result.Success AND I>=RANGE_1_4'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 32 <= S'Last and K.K = K~.K + 8*(4-I) AND I>=1 AND I<=4;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_4'First;
            WHILE Result.Success AND I<=RANGE_1_4'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 32 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=4;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    RealVal := Asn1Real(OctetArray4_to_Float(tmp));
        END IF;
    END Acn_Dec_Real_IEEE754_32_little_endian;

    PROCEDURE Acn_Enc_Real_IEEE754_64_little_endian(S : in out BitArray; K : in out Natural; RealVal:IN Asn1Real)
    IS
	tmp : OctetArray8;
    BEGIN
    	tmp := Long_Float_to_OctetArray8(RealVal);
	IF NOT RequiresReverse(K>0) THEN
		FOR I IN reverse RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(8-I);
			BitStream_AppendByte(S,K, tmp(I), FALSE);
		END LOOP;
	ELSE
		FOR I IN RANGE_1_8 LOOP
                --# assert K~+1>= S'First and K~ + 64 <= S'Last and K = K~ + 8*(I-1);
			BitStream_AppendByte(S, K, tmp(I), FALSE);
		END LOOP;
	END IF;
    END Acn_Enc_Real_IEEE754_64_little_endian;

    PROCEDURE Acn_Dec_Real_IEEE754_64_little_endian(S : in BitArray; K : in out DECODE_PARAMS; RealVal:OUT Asn1Real; Result:OUT ASN1_RESULT)
    IS
	tmp : OctetArray8:=OctetArray8'(others=>0);
        I   : INTEGER;
    BEGIN
	Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        RealVal := 0.0;
	IF NOT RequiresReverse(K.K>0) THEN
            I:=RANGE_1_8'Last;
            WHILE Result.Success AND I>=RANGE_1_8'First LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(8-I) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I - 1;
            END LOOP;
	ELSE
            I:=RANGE_1_8'First;
            WHILE Result.Success AND I<=RANGE_1_8'Last LOOP
            --# assert K~.K+1>= S'First and K~.K + 64 <= S'Last and K.K = K~.K + 8*(I-1) AND I>=1 AND I<=8;
                BitStream_DecodeByte(S,K, tmp(I), Result.Success);
                I := I + 1;
            END LOOP;
	END IF;
        IF Result.Success THEN
	    RealVal := OctetArray8_to_Long_Float(tmp);
        END IF;
    END Acn_Dec_Real_IEEE754_64_little_endian;



    PROCEDURE Acn_Enc_Boolean_true_pattern(S : in out BitArray; K : in out Natural; BoolVal:IN Asn1Boolean; pattern : IN BitArray)
    ---# derives S from S, BoolVal, K, pattern &
    ---#         K from  K, pattern;
    ---# pre  K+1>= S'First and K + pattern'Length <= S'Last;
    ---# post K = K~+pattern'Length;
    IS
    BEGIN
        IF BoolVal THEN
    	    FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
                S(K+((I-pattern'First)+1)) := pattern(I);
            END LOOP;
        ELSE
    	    FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
                S(K+((I-pattern'First)+1)) := NOT pattern(I);
            END LOOP;
        END IF;
        K := K + pattern'Length;
    END Acn_Enc_Boolean_true_pattern;


    PROCEDURE Acn_Dec_Boolean_true_pattern(S : in BitArray; K : in out DECODE_PARAMS; BoolVal:OUT Asn1Boolean; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    ---# derives  K 	 from K, pattern &
    ---#		 BoolVal from S,K, pattern &
    ---#          Result  from K, pattern;
    ---# pre  K.K+1>= S'First and K.K + pattern'Length <= S'Last;
    ---# post K.K = K~.K + pattern'Length;
    IS
    BEGIN
        BoolVal := TRUE;
	FOR I IN INTEGER range pattern'Range LOOP
        --# assert K.K = K~.K and K.K + 1>= S'First and K.K + pattern'Length <= S'Last and K.K+I-pattern'First+1 >=S'First  and K.K+I-pattern'First < S'Last;
             BoolVal := BoolVal AND S(K.K+((I-pattern'First)+1)) = pattern(I);
        END LOOP;
        K.K := K.K + pattern'Length;
        result := ASN1_RESULT'(Success => K.DataLen - K.K >=0, ErrorCode => ERR_INCORRECT_STREAM);
    END Acn_Dec_Boolean_true_pattern;




    PROCEDURE Acn_Enc_Boolean_false_pattern(S : in out BitArray; K : in out Natural; BoolVal:IN Asn1Boolean; pattern : IN BitArray)
    ---# derives S from S, BoolVal, K, pattern &
    ---#         K from  K, pattern;
    ---# pre  K+1>= S'First and K + pattern'Length <= S'Last;
    ---# post K = K~+pattern'Length;
    IS
    BEGIN
        IF not BoolVal THEN
    	    FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
                S(K+((I-pattern'First)+1)) := pattern(I);
            END LOOP;
        ELSE
    	    FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
                S(K+((I-pattern'First)+1)) := NOT pattern(I);
            END LOOP;
        END IF;
        K := K + pattern'Length;
    END Acn_Enc_Boolean_false_pattern;


    PROCEDURE Acn_Dec_Boolean_false_pattern(S : in BitArray; K : in out DECODE_PARAMS; BoolVal:OUT Asn1Boolean; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    ---# derives  K 	 from K, pattern &
    ---#		 BoolVal from S,K, pattern &
    ---#          Result  from K, pattern;
    ---# pre  K.K+1>= S'First and K.K + pattern'Length <= S'Last;
    ---# post K.K = K~.K + pattern'Length;
    IS
    BEGIN
        Acn_Dec_Boolean_true_pattern(S, K, BoolVal, pattern, Result);
        BoolVal := NOT BoolVal;
    END Acn_Dec_Boolean_false_pattern;


    PROCEDURE Acn_Enc_NullType_pattern(S : in out BitArray; K : in out Natural; encVal: IN Asn1NullType; pattern : IN BitArray)
    ---# derives S from S, K, encVal, pattern &
    ---#         K from  K, pattern;
    ---# pre  K+1>= S'First and K + pattern'Length <= S'Last;
    ---# post K = K~+pattern'Length;
    IS
    BEGIN
    	IF encVal = 0 THEN
   	    FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
                S(K+((I-pattern'First)+1)) := pattern(I);
            END LOOP;
        ELSE
   	    FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
                S(K+((I-pattern'First)+1)) := pattern(I);
            END LOOP;
        END IF;
        K := K + pattern'Length;
    END Acn_Enc_NullType_pattern;


    PROCEDURE Acn_Dec_NullType_pattern(S : in BitArray; K : in out DECODE_PARAMS; decValue : out Asn1NullType; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    ---# derives  K 	 from K, pattern &
    ---#          Result  from K, pattern  &
    ---#          decValue from S, K, pattern;
    ---# pre  K.K+1>= S'First and K.K + pattern'Length <= S'Last;
    ---# post K.K = K~.K + pattern'Length;
    IS
    	BoolVal:Boolean := TRUE;
    BEGIN
        decValue := 0;
	FOR I IN INTEGER range pattern'Range LOOP
        --# assert K.K = K~.K and K.K + 1>= S'First and K.K + pattern'Length <= S'Last and K.K+I-pattern'First+1 >=S'First  and K.K+I-pattern'First < S'Last;
             BoolVal := BoolVal AND S(K.K+((I-pattern'First)+1)) = pattern(I);
        END LOOP;
        K.K := K.K + pattern'Length;
        IF not BoolVal THEN
            decValue := 1;
        END IF;

        result := ASN1_RESULT'(Success => K.DataLen - K.K >=0 AND BoolVal, ErrorCode => ERR_INCORRECT_STREAM);
    END Acn_Dec_NullType_pattern;



    PROCEDURE Acn_Enc_NullType_pattern2(S : in out BitArray; K : in out Natural;  pattern : IN BitArray)
    ---# derives S from S, K, encVal, pattern &
    ---#         K from  K, pattern;
    ---# pre  K+1>= S'First and K + pattern'Length <= S'Last;
    ---# post K = K~+pattern'Length;
    IS
    BEGIN
 	FOR I IN INTEGER range pattern'Range LOOP
            --# assert K = K~ and K + 1>= S'First and K + pattern'Length <= S'Last and K+I-pattern'First+1 >=S'First  and K+I-pattern'First < S'Last;
            S(K+((I-pattern'First)+1)) := pattern(I);
        END LOOP;
        K := K + pattern'Length;
    END Acn_Enc_NullType_pattern2;


    PROCEDURE Acn_Dec_NullType_pattern2(S : in BitArray; K : in out DECODE_PARAMS; pattern : IN BitArray; Result:OUT ASN1_RESULT)
    ---# derives  K 	 from K, pattern &
    ---#          Result  from K, pattern  &
    ---#          decValue from S, K, pattern;
    ---# pre  K.K+1>= S'First and K.K + pattern'Length <= S'Last;
    ---# post K.K = K~.K + pattern'Length;
    IS
    	BoolVal:Boolean := TRUE;
    BEGIN
	FOR I IN INTEGER range pattern'Range LOOP
        --# assert K.K = K~.K and K.K + 1>= S'First and K.K + pattern'Length <= S'Last and K.K+I-pattern'First+1 >=S'First  and K.K+I-pattern'First < S'Last;
             BoolVal := BoolVal AND S(K.K+((I-pattern'First)+1)) = pattern(I);
        END LOOP;
        K.K := K.K + pattern'Length;

        result := ASN1_RESULT'(Success => K.DataLen - K.K >=0 AND BoolVal, ErrorCode => ERR_INCORRECT_STREAM);
    END Acn_Dec_NullType_pattern2;





    PROCEDURE Acn_Enc_NullType(S : in out BitArray; K : in out Natural; encVal: IN Asn1NullType)
    ---# derives S from S, K, encVal &
    ---#         K from  K;
    ---# pre  K+1>= S'First and K <= S'Last;
    ---# post K = K~;
    IS
       --# hide Acn_Enc_NullType;
    BEGIN
        null;
    END Acn_Enc_NullType;

    PROCEDURE Acn_Dec_NullType(S : in BitArray; K : in out DECODE_PARAMS; decValue : out Asn1NullType; Result:OUT ASN1_RESULT)
    ---# derives  K 	 from K &
    ---#          Result  from K  &
    ---#          decValue from S, K;
    ---# pre  K.K+1>= S'First and K.K  <= S'Last;
    ---# post K.K = K~.K ;
    IS
    	--# hide Acn_Dec_NullType;
        PRAGMA Unreferenced(S);
        PRAGMA Unreferenced(K);
    BEGIN
    	decValue:=0;
        Result := ASN1_RESULT'(Success => True,ErrorCode => 0);
    END Acn_Dec_NullType;


     PROCEDURE Acn_Enc_String_Ascii_FixSize(S : in out BitArray; K : in out Natural; strVal : in String)
     IS
         I:Integer:=strVal'First;
     BEGIN
         WHILE I<=strVal'Last - 1 LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(CharacterPos(strVal(I))), 0, 8);

             I:=I+1;
         END LOOP;

     END Acn_Enc_String_Ascii_FixSize;


     PROCEDURE Acn_Dec_String_Ascii_FixSize(S : in BitArray; K : in out DECODE_PARAMS; strVal : in out String; Result:OUT ASN1_RESULT)
     IS
         I:Integer:=strVal'First;
         charIndex:Integer;
     BEGIN
	 Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
         WHILE I<=strVal'Last - 1 and Result.Success LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, 255, 8, Result.Success);
             strVal(i) := Character'Val(charIndex);

             I:=I+1;
         END LOOP;
         strVal(strVal'Last) := NUL;
     END Acn_Dec_String_Ascii_FixSize;



    PROCEDURE Acn_Enc_String_Ascii_Null_Teminated(S : in out BitArray; K : in out Natural; null_character : in Integer; strVal : in String)
     IS
         I:Integer:=strVal'First;
    BEGIN
          WHILE I<=strVal'Last - 1 AND THEN strVal(I)/=NUL LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(CharacterPos(strVal(I))), 0, 8);

             I:=I+1;
          END LOOP;
          UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(null_character), 0, 8);

    END Acn_Enc_String_Ascii_Null_Teminated;

    PROCEDURE Acn_Dec_String_Ascii_Null_Teminated(S : in BitArray; K : in out DECODE_PARAMS; null_character : in Integer; strVal : out String; Result:OUT ASN1_RESULT)
    IS
         I:Integer:=strVal'First;
         charIndex:Integer:=65; -- ascii code of 'A'. Let's hope that 'A' will never be null Character
    BEGIN
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
        WHILE result.Success AND THEN I<=strVal'Last AND THEN charIndex/=null_character LOOP
             --# assert I>=1 AND I<=str'Last;
            UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, 255, 8, result.Success);
            IF charIndex/=null_character THEN
                strVal(i) := Character'Val(charIndex);
            ELSE
                strVal(I) := NUL;
            END IF;

            I:=I+1;
        END LOOP;
        WHILE I <= strVal'Last LOOP
            strVal(I) := NUL;
             I:=I+1;
        END LOOP;

    END Acn_Dec_String_Ascii_Null_Teminated;




    PROCEDURE Acn_Enc_String_Ascii_Internal_Field_Determinant(S : in out BitArray; K : in out Natural; asn1Min: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : in String)
     IS
         I:Integer:=strVal'First;
    BEGIN
          UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(getStringSize(strVal)), asn1Min, nLengthDeterminantSizeInBits);
          WHILE I<=strVal'Last - 1 AND THEN strVal(I)/=NUL LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(CharacterPos(strVal(I))), 0, 8);

             I:=I+1;
          END LOOP;

    END Acn_Enc_String_Ascii_Internal_Field_Determinant;

    PROCEDURE Acn_Dec_String_Ascii_Internal_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; asn1Min: Asn1Int; asn1Max: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : out String; Result:OUT ASN1_RESULT)
    IS
         I:Integer:=strVal'First;
         nSize:Integer;
         charIndex:Integer;
    BEGIN
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);

        UPER_Dec_ConstraintWholeNumberInt(S, K, nSize, Integer(asn1Min), Integer(asn1Max), nLengthDeterminantSizeInBits, result.Success);
        WHILE result.Success AND THEN I<=strVal'Last-1 AND THEN I <=  nSize LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, 255, 8, result.Success);
             strVal(i) := Character'Val(charIndex);

             I:=I+1;
        END LOOP;
        WHILE I <= strVal'Last LOOP
            strVal(I) := NUL;
             I:=I+1;
        END LOOP;

    END Acn_Dec_String_Ascii_Internal_Field_Determinant;




    PROCEDURE Acn_Enc_String_Ascii_External_Field_Determinant(S : in out BitArray; K : in out Natural; strVal : in String)
     IS
         I:Integer:=strVal'First;
    BEGIN
          WHILE I<=strVal'Last - 1 AND THEN strVal(I)/=NUL LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(CharacterPos(strVal(I))), 0, 8);

             I:=I+1;
          END LOOP;

    END Acn_Enc_String_Ascii_External_Field_Determinant;

    PROCEDURE Acn_Dec_String_Ascii_External_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; extSizeDeterminatFld : IN Asn1Int; strVal : out String; Result:OUT ASN1_RESULT)
    IS
         I:Integer:=strVal'First;
         charIndex:Integer;
    BEGIN
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);

        WHILE result.Success AND THEN I<=strVal'Last-1 AND THEN I <=  Integer(extSizeDeterminatFld) LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, 255, 8, result.Success);
             strVal(i) := Character'Val(charIndex);

             I:=I+1;
        END LOOP;
        WHILE I <= strVal'Last LOOP
            strVal(I) := NUL;
             I:=I+1;
        END LOOP;


    END Acn_Dec_String_Ascii_External_Field_Determinant;




-- -------------------------------------
     PROCEDURE Acn_Enc_String_CharIndex_FixSize(S : in out BitArray; K : in out Natural; charSet : String; nCharSize:Integer; strVal : in String)
     IS
         I:Integer:=strVal'First;
         charIndex:Integer;
     BEGIN
         WHILE I<=strVal'Last - 1 LOOP
             --# assert I>=1 AND I<=str'Last-1;
             charIndex := GetZeroBasedCharIndex(strVal(I), charSet);
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(charIndex), 0, nCharSize);

             I:=I+1;
         END LOOP;

     END Acn_Enc_String_CharIndex_FixSize;


     PROCEDURE Acn_Dec_String_CharIndex_FixSize(S : in BitArray; K : in out DECODE_PARAMS; charSet : String; nCharSize:Integer; strVal : in out String; Result:OUT ASN1_RESULT)
     IS
         I:Integer:=strVal'First;
         charIndex:Integer;
         asn1Max:CONSTANT Integer := charSet'Last - 1;
     BEGIN
	 Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);
         WHILE I<=strVal'Last - 1 and Result.Success LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, asn1Max, nCharSize, Result.Success);
             strVal(i) := charSet(charIndex+1);

             I:=I+1;
         END LOOP;
         strVal(strVal'Last) := NUL;
     END Acn_Dec_String_CharIndex_FixSize;




    PROCEDURE Acn_Enc_String_CharIndex_External_Field_Determinant(S : in out BitArray; K : in out Natural; charSet : String; nCharSize:Integer; strVal : in String)
     IS
         I:Integer:=strVal'First;
         charIndex:Integer;
    BEGIN
          WHILE I<=strVal'Last - 1 AND THEN strVal(I)/=NUL LOOP
             --# assert I>=1 AND I<=str'Last-1;
             charIndex := GetZeroBasedCharIndex(strVal(I), charSet);
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(charIndex), 0, nCharSize);

             I:=I+1;
          END LOOP;

    END Acn_Enc_String_CharIndex_External_Field_Determinant;

    PROCEDURE Acn_Dec_String_CharIndex_External_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; charSet : String; nCharSize:Integer; extSizeDeterminatFld : IN Asn1Int; strVal : out String; Result:OUT ASN1_RESULT)
    IS
         I:Integer:=strVal'First;
         charIndex:Integer;
         asn1Max:CONSTANT Integer := charSet'Last - 1;
    BEGIN
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);

        WHILE result.Success AND THEN I<=strVal'Last-1 AND THEN I <=  Integer(extSizeDeterminatFld) LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, asn1Max, nCharSize, Result.Success);
             strVal(i) := charSet(charIndex+1);

             I:=I+1;
        END LOOP;
        WHILE I <= strVal'Last LOOP
            strVal(I) := NUL;
             I:=I+1;
        END LOOP;


    END Acn_Dec_String_CharIndex_External_Field_Determinant;


    PROCEDURE Acn_Enc_String_CharIndex_Internal_Field_Determinant(S : in out BitArray; K : in out Natural; charSet : String; nCharSize:Integer; asn1Min: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : in String)
     IS
         I:Integer:=strVal'First;
         charIndex:Integer;
    BEGIN
          UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(getStringSize(strVal)), asn1Min, nLengthDeterminantSizeInBits);
          WHILE I<=strVal'Last - 1 AND THEN strVal(I)/=NUL LOOP
             --# assert I>=1 AND I<=str'Last-1;
             charIndex := GetZeroBasedCharIndex(strVal(I), charSet);
             UPER_Enc_ConstraintWholeNumber(S, K, Asn1Int(charIndex), 0, nCharSize);

             I:=I+1;
          END LOOP;

    END Acn_Enc_String_CharIndex_Internal_Field_Determinant;

    PROCEDURE Acn_Dec_String_CharIndex_Internal_Field_Determinant(S : in BitArray; K : in out DECODE_PARAMS; charSet : String; nCharSize:Integer; asn1Min: Asn1Int; asn1Max: Asn1Int; nLengthDeterminantSizeInBits : IN Integer; strVal : out String; Result:OUT ASN1_RESULT)
    IS
         I:Integer:=strVal'First;
         nSize:Integer;
         charIndex:Integer;
    BEGIN
        Result := ASN1_RESULT'(Success   => TRUE,ErrorCode => ERR_INSUFFICIENT_DATA);

        UPER_Dec_ConstraintWholeNumberInt(S, K, nSize, Integer(asn1Min), Integer(asn1Max), nLengthDeterminantSizeInBits, result.Success);
        WHILE result.Success AND THEN I<=strVal'Last-1 AND THEN I <=  nSize LOOP
             --# assert I>=1 AND I<=str'Last-1;
             UPER_Dec_ConstraintWholeNumberInt(S, K, charIndex, 0, charSet'Last - 1, nCharSize, Result.Success);
             strVal(i) := charSet(charIndex+1);

             I:=I+1;
        END LOOP;
        WHILE I <= strVal'Last LOOP
            strVal(I) := NUL;
             I:=I+1;
        END LOOP;

    END Acn_Dec_String_CharIndex_Internal_Field_Determinant;


   FUNCTION milbus_encode(IntVal:IN Asn1Int) RETURN Asn1Int
   is
      ret : Asn1Int;
   begin
      if IntVal = 32 then
         ret := 0;
      else
         ret := IntVal;
      end if;
      return ret;
   end milbus_encode;

   FUNCTION milbus_decode(IntVal:IN Asn1Int) RETURN Asn1Int
   is
      ret : Asn1Int;
   begin
      if IntVal = 0 then
         ret := 32;
      else
         ret := IntVal;
      end if;
      return ret;
   end milbus_decode;


END adaasn1rtl;



