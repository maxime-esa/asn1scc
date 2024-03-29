package adaasn1rtl.encoding.uper with
   Spark_Mode
is

   subtype OctetArray1K is OctetBuffer (1 .. 1024);

   procedure UPER_Enc_Boolean (bs : in out Bitstream; Val : Asn1Boolean) with
      Depends => (bs => (bs, Val)),
      Pre     => bs.Current_Bit_Pos < Natural'Last
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < bs.Size_In_Bytes * 8,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + 1;

   procedure UPER_Dec_boolean
     (bs : in out Bitstream; val : out Asn1Boolean; result : out Boolean) with
      Depends => (bs => (bs), val => bs, result => bs),
      Pre     => bs.Current_Bit_Pos < Natural'Last
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < bs.Size_In_Bytes * 8,
      Post => result and bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + 1;

      --  UPER encode functions
   procedure UPER_Enc_SemiConstraintWholeNumber
     (bs : in out Bitstream; IntVal : Asn1Int; MinVal : Asn1Int) with
      Depends => (bs => (bs, IntVal, MinVal)),
      Pre     => IntVal >= MinVal
      and then bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8);

   procedure UPER_Dec_SemiConstraintWholeNumber
     (bs     : in out Bitstream; IntVal : out Asn1Int; MinVal : Asn1Int;
      Result :    out Boolean) with
      Depends => ((IntVal, Result) => (bs, MinVal), bs => (bs, MinVal)),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8) and
      IntVal >= MinVal;

   procedure UPER_Enc_SemiConstraintPosWholeNumber
     (bs : in out Bitstream; IntVal : Asn1UInt; MinVal : Asn1UInt) with
      Depends => (bs => (bs, IntVal, MinVal)),
      Pre     => IntVal >= MinVal
      and then bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8);

   procedure UPER_Dec_SemiConstraintPosWholeNumber
     (bs     : in out Bitstream; IntVal : out Asn1UInt; MinVal : Asn1UInt;
      Result :    out Boolean) with
      Depends => ((IntVal, Result) => (bs, MinVal), bs => (bs, MinVal)),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8) and
      IntVal >= MinVal;

   procedure UPER_Enc_ConstraintWholeNumber
     (bs    : in out Bitstream; IntVal : Asn1Int; MinVal : Asn1Int;
      nBits :        Integer) with
      Depends => (bs => (bs, IntVal, MinVal, nBits)),
      Pre     => IntVal >= MinVal and then nBits >= 0
      and then nBits <= Asn1UInt'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits;

   procedure UPER_Enc_ConstraintPosWholeNumber
     (bs    : in out Bitstream; IntVal : Asn1UInt; MinVal : Asn1UInt;
      nBits :        Integer) with
      Depends => (bs => (bs, IntVal, MinVal, nBits)),
      Pre     => IntVal >= MinVal and then nBits >= 0
      and then nBits <= Asn1UInt'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits;

   procedure UPER_Dec_ConstraintWholeNumber
     (bs     : in out Bitstream; IntVal : out Asn1Int; MinVal : Asn1Int;
      MaxVal :        Asn1Int; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Asn1UInt'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
         (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintWholeNumberInt8
     (bs     : in out Bitstream; IntVal : out Integer_8; MinVal : Integer_8;
      MaxVal :        Integer_8; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Integer_8'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintWholeNumberInt16
     (bs     : in out Bitstream; IntVal : out Integer_16; MinVal : Integer_16;
      MaxVal :        Integer_16; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Integer_16'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintWholeNumberInt32
     (bs     : in out Bitstream; IntVal : out Integer_32; MinVal : Integer_32;
      MaxVal :        Integer_32; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Integer_32'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintPosWholeNumberUInt8
     (bs : in out Bitstream; IntVal : out Unsigned_8; MinVal : Unsigned_8;
      MaxVal :        Unsigned_8; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Unsigned_8'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintPosWholeNumberUInt16
     (bs : in out Bitstream; IntVal : out Unsigned_16; MinVal : Unsigned_16;
      MaxVal :        Unsigned_16; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Unsigned_16'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintPosWholeNumberUInt32
     (bs : in out Bitstream; IntVal : out Unsigned_32; MinVal : Unsigned_32;
      MaxVal :        Unsigned_32; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Unsigned_32'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Dec_ConstraintPosWholeNumber
     (bs     : in out Bitstream; IntVal : out Asn1UInt; MinVal : Asn1UInt;
      MaxVal :        Asn1UInt; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Asn1UInt'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));
   procedure UPER_Dec_ConstraintWholeNumberInt
     (bs     : in out Bitstream; IntVal : out Integer; MinVal : Integer;
      MaxVal :        Integer; nBits : Integer; Result : out Boolean) with
      Depends => ((bs, IntVal, Result) => (bs, MinVal, MaxVal, nBits)),
      Pre     => MinVal <= MaxVal and then nBits >= 0
      and then nBits <= Asn1UInt'Size
      and then bs.Current_Bit_Pos < Natural'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - nBits,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + nBits and
      ((Result and (((IntVal >= MinVal) and (IntVal <= MaxVal)))) or
       (not Result and (IntVal = MinVal)));

   procedure UPER_Enc_UnConstraintWholeNumber
     (bs : in out Bitstream; IntVal : Asn1Int) with
      Depends => (bs => (bs, IntVal)),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8);

   procedure UPER_Dec_UnConstraintWholeNumber
     (bs : in out Bitstream; IntVal : out Asn1Int; Result : out Boolean) with
      Depends => ((IntVal, bs, Result) => bs),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8);

   procedure UPER_Dec_UnConstraintWholeNumberMax
     (bs     : in out Bitstream; IntVal : out Asn1Int; MaxVal : Asn1Int;
      Result :    out Boolean) with
      Pre => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 8)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 8),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 8);

      --  REAL FUNCTIONS

   function CalcReal
     (Factor : Asn1UInt; N : Asn1UInt; base : Integer; Exp : Integer)
      return Asn1Real with
      Pre => (Factor = 1 or Factor = 2 or Factor = 4 or Factor = 8)
      and then (base = 2 or base = 8 or base = 16);

   procedure UPER_Enc_Real (bs : in out Bitstream; RealVal : Asn1Real) with
      Depends => (bs => (bs, RealVal)),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 40)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 40),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 40);

   procedure UPER_Dec_Real
     (bs     : in out Bitstream; RealVal : out Asn1Real;
      Result :    out ASN1_RESULT) with
      Depends => ((bs, RealVal, Result) => (bs)),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 40)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 40),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 40);

   procedure UPER_Dec_Real_fp32
     (bs     : in out Bitstream; RealVal : out Standard.Float;
      Result :    out ASN1_RESULT) with
      Depends => ((bs, RealVal, Result) => (bs)),
      Pre     => bs.Current_Bit_Pos < Natural'Last - (Asn1UInt'Size + 40)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (Asn1UInt'Size + 40),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <= bs'Old.Current_Bit_Pos + (Asn1UInt'Size + 40);

   procedure ObjectIdentifier_uper_encode
     (bs : in out Bitstream; val : Asn1ObjectIdentifier) with
      Depends => (bs => (bs, val)),
      Pre     => bs.Current_Bit_Pos <
      Natural'Last -
        (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 -
          (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <=
        bs'Old.Current_Bit_Pos +
          (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last);

   procedure RelativeOID_uper_encode
     (bs : in out Bitstream; val : Asn1ObjectIdentifier) with
      Depends => (bs => (bs, val)),
      Pre     => bs.Current_Bit_Pos <
      Natural'Last -
        (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 -
          (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last),
      Post => bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      bs.Current_Bit_Pos <=
        bs'Old.Current_Bit_Pos +
          (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last);

   procedure ObjectIdentifier_uper_decode
     (bs     : in out Bitstream; val : out Asn1ObjectIdentifier;
      Result :    out ASN1_RESULT) with
      Depends => ((bs, val, Result) => (bs)),
      Pre     => bs.Current_Bit_Pos <
      Natural'Last -
        (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 -
          (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last),
      Post => bs.Current_Bit_Pos <=
      bs'Old.Current_Bit_Pos +
        (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last) and
      bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos;

   procedure RelativeOID_uper_decode
     (bs     : in out Bitstream; val : out Asn1ObjectIdentifier;
      Result :    out ASN1_RESULT) with
      Depends => ((bs, val, Result) => (bs)),
      Pre     => bs.Current_Bit_Pos <
      Natural'Last -
        (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last)
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 -
          (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last),
      Post => bs.Current_Bit_Pos <=
      bs'Old.Current_Bit_Pos +
        (16 + 8 * OBJECT_IDENTIFIER_MAX_LENGTH * OctetBuffer_16'Last) and
      bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos;

   procedure BitStream_EncodeOctetString_no_length
     (bs : in out Bitstream; data : OctetBuffer; data_length : Integer) with
      Pre => data_length >= 0 and then data'Last >= data'First
      and then data'Last < Positive'Last / 8
      and then data'Last - data'First < Positive'Last / 8
      and then data_length <= data'Last - data'First + 1
      and then data_length < Positive'Last / 8
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < Natural'Last - 8 * data_length
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - 8 * data_length,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + 8 * data_length;

   procedure BitStream_DecodeOctetString_no_length
     (bs : in out Bitstream; data : in out OctetBuffer; data_length : Integer;
      success :    out Boolean) with
      Pre => data_length >= 0 and then data'Last >= data'First
      and then data'Last < Positive'Last / 8
      and then data'Last - data'First < Positive'Last / 8
      and then data_length <= data'Last - data'First + 1
      and then data_length < Positive'Last / 8
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < Natural'Last - 8 * data_length
      and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - 8 * data_length,
      Post => bs.Current_Bit_Pos = bs'Old.Current_Bit_Pos + 8 * data_length;

   procedure BitStream_EncodeOctetString
     (bs    : in out Bitstream; data : OctetBuffer; data_length : Integer;
      nBits :    Integer; asn1SizeMin : Integer; asn1SizeMax : Integer) with
      Pre => asn1SizeMin >= 0 and then asn1SizeMin <= asn1SizeMax
      and then nBits >= 0 and then nBits <= Asn1UInt'Size
      and then
      ((asn1SizeMax <= 65536 and asn1SizeMin = asn1SizeMax and nBits = 0)
       or else
       (asn1SizeMax <= 65536 and asn1SizeMin /= asn1SizeMax and nBits > 0)
       or else (asn1SizeMax > 65536))
      and then data_length >= 0 and then data_length >= asn1SizeMin
      and then data'Last >= data'First and then data'Last < Positive'Last / 8
      and then data'Last - data'First < Positive'Last / 8
      and then data_length <= data'Last - data'First + 1
      and then data_length < Positive'Last / 8 - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < Natural'Last - (8 * data_length + nBits)
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (8 * data_length + nBits),
      Post => bs.Current_Bit_Pos <=
      bs'Old.Current_Bit_Pos + (8 * data_length + nBits) and
      bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos;

   procedure BitStream_DecodeOctetString
     (bs          : in out Bitstream; data : in out OctetBuffer;
      data_length :    out Integer; nBits : Integer; asn1SizeMin : Integer;
      asn1SizeMax :        Integer; success : out Boolean) with
      Pre => asn1SizeMin >= 0 and then asn1SizeMin <= asn1SizeMax
      and then asn1SizeMax < Positive'Last and then nBits >= 0
      and then nBits <= Asn1UInt'Size and then data'Last >= data'First
      and then data'Last < Positive'Last / 8
      and then data'Last - data'First < Positive'Last / 8
      and then asn1SizeMax <= data'Last - data'First + 1
      and then asn1SizeMax < Positive'Last / 8 - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < Natural'Last - (8 * asn1SizeMax + nBits)
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (8 * asn1SizeMax + nBits),
      Post => bs.Current_Bit_Pos <=
      bs'Old.Current_Bit_Pos + (8 * asn1SizeMax + nBits) and
      bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      data_length >= asn1SizeMin and data_length <= asn1SizeMax;

   procedure BitStream_EncodeBitString
     (bs    : in out Bitstream; data : OctetBuffer; data_length : Integer;
      nBits :    Integer; asn1SizeMin : Integer; asn1SizeMax : Integer) with
      Pre => asn1SizeMin >= 0 and then asn1SizeMin <= asn1SizeMax
      and then nBits >= 0 and then nBits <= Asn1UInt'Size
      and then data_length >= 0 and then data_length >= asn1SizeMin
      and then data'Last < Positive'Last / 8
      and then data'Length < Positive'Last / 8
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then data_length >= (data'Length - 1) * 8
      and then data_length <= (data'Length) * 8

      and then data'Last >= data'First
      and then data_length < Positive'Last - nBits
      and then bs.Current_Bit_Pos < Natural'Last - (data_length + nBits)
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (data_length + nBits),
      Post => bs.Current_Bit_Pos <=
      bs'Old.Current_Bit_Pos + (data_length + nBits) and
      bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos;

--        Pre     => bitMaskAsByteArray'First >= 0
--        and then bitMaskAsByteArray'Last < Natural'Last / 8
--        and then bits_to_read >= (bitMaskAsByteArray'Length - 1) * 8
--        and then bits_to_read <= (bitMaskAsByteArray'Length) * 8
--        and then bs.Current_Bit_Pos < Natural'Last - bits_to_read
--        and then bs.Size_In_Bytes < Positive'Last / 8
--        and then bs.Current_Bit_Pos <= bs.Size_In_Bytes * 8 - bits_to_read,

   procedure BitStream_DecodeBitString
     (bs          : in out Bitstream; data : in out OctetBuffer;
      data_length :    out Integer; nBits : Integer; asn1SizeMin : Integer;
      asn1SizeMax :        Integer; success : out Boolean) with
      Pre => asn1SizeMin >= 0 and then asn1SizeMin <= asn1SizeMax
      and then asn1SizeMax < Positive'Last and then nBits >= 0
      and then nBits <= Asn1UInt'Size and then data'First >= 0
      and then data'Last < Natural'Last / 8 and then data'Last >= data'First
      and then data'Last - data'First < Positive'Last / 8
--      and then asn1SizeMax <= (data'Last - data'First + 1) * 8

      and then asn1SizeMax <= data'Length * 8

      and then asn1SizeMax < Positive'Last - nBits
      and then bs.Size_In_Bytes < Positive'Last / 8
      and then bs.Current_Bit_Pos < Natural'Last - (asn1SizeMax + nBits)
      and then bs.Current_Bit_Pos <=
        bs.Size_In_Bytes * 8 - (asn1SizeMax + nBits),

      Post => bs.Current_Bit_Pos <=
      bs'Old.Current_Bit_Pos + (asn1SizeMax + nBits) and
      bs.Current_Bit_Pos >= bs'Old.Current_Bit_Pos and
      data_length >= asn1SizeMin and data_length <= asn1SizeMax;

end adaasn1rtl.encoding.uper;
