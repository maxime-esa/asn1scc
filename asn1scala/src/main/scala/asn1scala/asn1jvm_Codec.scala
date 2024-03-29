package asn1scala

import stainless.*
import stainless.lang.{None, Option, ghost as ghostExpr, _}
import stainless.collection.*
import stainless.annotation.*
import stainless.proof.*
import stainless.math.*
import StaticChecks.{require as staticRequire, _}

val masks2: Array[Int] = Array(
   0x00000000, //         0 / 0000 0000 0000 0000 0000 0000 0000 0000 / 0x0000 0000
   0x000000FF, //       255 / 0000 0000 0000 0000 0000 0000 1111 1111 / 0x0000 00FF
   0x0000FF00, //     65280 / 0000 0000 0000 0000 1111 1111 0000 0000 / 0x0000 FF00
   0x00FF0000, //  16711680 / 0000 0000 1111 1111 0000 0000 0000 0000 / 0x00FF 0000
   0xFF000000, // -16777216 / 1111 1111 0000 0000 0000 0000 0000 0000 / 0xFF00 0000
)

val CHAR_MINUS: Byte = 45
val CHAR_PLUS: Byte = 43
val CHAR_ZERO: Byte = 48
val CHAR_NINE: Byte = 57
val CHAR_0000: Byte = 0

/***********************************************************************************************/
/**    Byte Stream Functions                                                                  **/
/***********************************************************************************************/

// TODO is this needed? should always be called through ACN / PER / UPER
//def ByteStream_Init(count: Int): ByteStream = {
//   ByteStream(Array.fill(count)(0), 0, false)
//}

//@extern
//def runtimeAssert(condition: Boolean, s: String =""): Unit = assert(condition, s)

@extern
def writeToStdErr(s: String): Unit = Console.err.println(s)

@extern
def ByteStream_AttachBuffer(pStrm: ByteStream, buf: Array[Byte]): Unit = {
   pStrm.buf = buf // Illegal aliasing, therefore we need to workaround with this @extern...
   pStrm.currentByte = 0
}.ensuring(_ => pStrm.buf == buf && pStrm.currentByte == 0 && pStrm.EncodeWhiteSpace == old(pStrm).EncodeWhiteSpace)

def ByteStream_GetLength(pStrm: ByteStream): Int = {
   pStrm.currentByte
}

/***********************************************************************************************/
/**    Bit Stream Functions                                                                   **/
/***********************************************************************************************/
def BitString_equal(arr1: Array[UByte], arr2: Array[UByte]): Boolean = {
   arraySameElements(arr1, arr2)
}

/**
 * Base class for the PER Codec that is used by ACN and UPER
 *
 * @param count represents the number of bytes in the internal buffer
 *
 */
case class Codec private [asn1scala](bitStream: BitStream) {

   /** ******************************************************************************************** */
   /** ******************************************************************************************** */
   /** ******************************************************************************************** */
   /** Integer Functions                                                                          * */
   /** ******************************************************************************************** */
   /** ******************************************************************************************** */
   /** ******************************************************************************************** */

   /**
    * Encode number to the bitstream. The number of bits written is
    * specified by the position of the Most Significant set bit in
    * value v. This would be 64 if the value is -1.
    *
    * @param v value that gets encoded
    *
    */
   def encodeUnsignedInteger(v: ULong): Unit = {
      require(bitStream.validate_offset_bits(GetBitCountUnsigned(v)))

      appendNLeastSignificantBits(v.toRaw, GetBitCountUnsigned(v))
   }

   /**
    * Decode number from the bitstream. Reversal function of encodeUnsignedInteger.
    *
    * @param nBits Number of bits used for decoding. Valid range is from 0 to 64.
    * @return Unsigned integer with nBits decoded from bitstream.
    *
    */
   def decodeUnsignedInteger(nBits: Int): ULong = {
      require(nBits >= 0 && nBits <= NO_OF_BITS_IN_LONG)
      require(bitStream.validate_offset_bits(nBits))

      readNLeastSignificantBits(nBits).toRawULong
   }

   /**
    * Encode number to the bitstream within the [min,max] range
    * without a length. The number of bits written is specified by the
    * bits needed to represent the whole range. That would be 64bits in the
    * maximal case of min=0 to max=-1.
    *
    * @param v   number that gets encoded, needs to be within [min,max] range
    * @param min lower unsigned boundary of range
    * @param max upper unsigned boundary of range
    *
    * Remarks:
    * v, min and max get interpreted as unsigned numbers.
    *
    */
   def encodeConstrainedPosWholeNumber(v: ULong, min: ULong, max: ULong): Unit = {
      require(min <= max)
      require(min <= v)
      require(v <= max)

      val range = max - min
      if range == 0.toRawULong then
         return

      // get number of bits that get written
      val nRangeBits: Int = GetBitCountUnsigned(range)

      // get value that gets written
      val encVal = v - min

      @ghost val nEncValBits = GetBitCountUnsigned(encVal)
      assert(nRangeBits >= nEncValBits)
      assert(bitStream.validate_offset_bits(nRangeBits))

      appendNLeastSignificantBits(encVal, nRangeBits)
   }

   /**
    * Decode number from the bitstream. Reversal function of encodeConstrainedPosWholeNumber.
    *
    * @param min lower unsigned boundary of range
    * @param max hupper unsigned boundary of range
    * @return number in range [min,max] that gets extracted from the bitstream
    *
    * Remarks:
    * The returned value must be interpreted as an unsigned 64bit integer
    *
    */
   def decodeConstrainedPosWholeNumber(min: ULong, max: ULong): ULong = {
      require(min <= max)
      staticRequire(
         bitStream.validate_offset_bits(GetBitCountUnsigned(max - min))
      )

      val range: ULong = max - min

      // only one possible number
      if range == ULong.fromRaw(0) then
         return min

      val nRangeBits: Int = GetBitCountUnsigned(range)
      assert(bitStream.validate_offset_bits(nRangeBits))
      val decVal = decodeUnsignedInteger(nRangeBits)

      assert(min + decVal <= max)

      min + decVal
   }

   /**
    * Encode number to the bitstream within the [min,max] range
    * without a length. The number of bits written is specified by the
    * bits needed to represent the whole range. That would be 64bits in the
    * maximal case of min=Long.Min_Value to max=Long.MaxValue.
    *
    * @param v number that gets encoded, needs to be within [min,max] range
    * @param min lower boundary of range
    * @param max upper boundary of range
    *
    */
   def encodeConstrainedWholeNumber(v: Long, min: Long, max: Long): Unit = {
      require(min <= max)
      require(min <= v && v <= max)

      val range: Long = stainless.math.wrapping(max - min)
      if range == 0 then
         return

      // get number of bits that get written
      val nRangeBits: Int = GetBitCountUnsigned(range.toRawULong)

      // get value that gets written
      val encVal = stainless.math.wrapping(v - min).toRawULong

      @ghost val nEncValBits = GetBitCountUnsigned(encVal)
      assert(nRangeBits >= nEncValBits)
      assert(bitStream.validate_offset_bits(nRangeBits))

      appendNLeastSignificantBits(encVal, nRangeBits)
   }

   /**
    * Whole Number decoding and casts into all data types (meths below).
    * This is the reversal function of encodeConstrainedWholeNumber.
    * encodeConstrainedWholeNumber
    *
    * @param min lower boundary of range
    * @param max upper boundary of range
    * @return decoded value within the range [min,max]
    *
    * Remarks:
    * If the decoded data does not fulfill the range condition
    * this method will fail.
    *
   */
   def decodeConstrainedWholeNumber(min: Long, max: Long): Long = {
      require(min <= max)
      staticRequire(
         bitStream.validate_offset_bits(
            GetBitCountUnsigned(stainless.math.wrapping(max - min).toRawULong)
         )
      )

      val range: Long = stainless.math.wrapping(max - min)

      // only one possible value
      if range == 0 then
         return min

      val nRangeBits = GetBitCountUnsigned(range.toRawULong)
      assert(bitStream.validate_offset_bits(nRangeBits))
      val decVal = readNLeastSignificantBits(nRangeBits)

      assert(min + decVal <= max)

      min + decVal
   }
   def decodeConstrainedWholeNumberInt(min: Int, max: Int): Int = {
      require(min <= max)
      val i = decodeConstrainedWholeNumber(min, max).cutToInt

      assert(i >= min &&& i <= max)

      i
   }
   def decodeConstrainedWholeNumberShort(min: Short, max: Short): Short = {
      require(min <= max)
      val s = decodeConstrainedWholeNumber(min, max).cutToShort

      assert(s >= min &&& s <= max)

      s
   }
   def decodeConstrainedWholeNumberByte(min: Byte, max: Byte): Byte = {
      require(min <= max)
      val b = decodeConstrainedWholeNumber(min, max).cutToByte

      assert(b >= min &&& b <= max)

      b
   }

   /**
    * Encode number to the bitstream within the range [min, Long.Max_Value].
    * This function writes full bytes to the bitstream. The length is written as
    * an signed byte in front of the bytes written for the number v.
    *
    * @param v    number that gets encoded to the bitstream. Must be bigger than min.
    * @param min  lower boundary of range
    *
    */
   def encodeSemiConstrainedWholeNumber(v: Long, min: Long): Unit = {
      require(min <= v)
      staticRequire(bitStream.validate_offset_bytes(
         GetLengthForEncodingUnsigned(stainless.math.wrapping(v - min).toRawULong) + 1)
      )

      val encV: ULong = stainless.math.wrapping(v - min).toRawULong
      val nBytes = GetLengthForEncodingUnsigned(encV).toByte

      // need space for length and value
      assert(bitStream.validate_offset_bytes(nBytes + 1))

      // encode length
      appendByte(nBytes.toRawUByte)
      // encode value
      appendNLeastSignificantBits(encV.toRaw, nBytes * NO_OF_BITS_IN_BYTE)
   }

   /**
    * Decode number from bitstream that is in range [min, Long.MaxValue].
    * This is the reversal function of encodeSemiConstrainedWholeNumber.
    *
    * @param min lower boundary of range
    * @return value decoded from the bitstream.
    *
    */
   def decodeSemiConstrainedWholeNumber(min: Long): Long = {
      require(bitStream.validate_offset_bytes(1))

      // decode length
      val nBytes = readByte()
      // check bitstream precondition
      assert(bitStream.validate_offset_bytes(nBytes.toRaw))
      // decode number
      val v: ULong = readNLeastSignificantBits(nBytes.toRaw * NO_OF_BITS_IN_BYTE).toRawULong

      v + min
   }.ensuring(x => x >= min)

   /**
    * Encode number to the bitstream within the range [min, Long.Max_Value].
    * This function writes full bytes to the bitstream. The length is written as
    * an signed byte in front of the bytes written for the number v.
    *
    * @param v   number that gets encoded to the bitstream. Must be bigger than min.
    * @param min lower unsigned boundary of range
    *
    */
   def encodeSemiConstrainedPosWholeNumber(v: ULong, min: ULong): Unit = {
      require(min <= v)
      staticRequire(bitStream.validate_offset_bytes(
         GetLengthForEncodingUnsigned(stainless.math.wrapping(v - min)) + 1)
      )

      val encV = stainless.math.wrapping(v - min)
      val nBytes = GetLengthForEncodingUnsigned(encV.toRawULong).toByte

      /* need space for length and value */
      assert(bitStream.validate_offset_bytes(nBytes + 1))

      /* encode length */
      appendByte(nBytes.toRawUByte)
      /* encode number */
      appendNLeastSignificantBits(encV, nBytes * NO_OF_BITS_IN_BYTE)
   }

   /**
    * Decode unsigned number from the bitstream
    * within the range [min, Long.Max_Value].
    *
    * @param min lower unsigned boundary of range
    *
    */
   def decodeSemiConstrainedPosWholeNumber(min: ULong): ULong = {
      require(bitStream.validate_offset_bytes(1))

      // decode length
      val nBytes = readByte()
      // check bitstream precondition
      assert(bitStream.validate_offset_bytes(nBytes.toRaw))
      // decode number
      val v = readNLeastSignificantBits(nBytes.toRaw * NO_OF_BITS_IN_BYTE)
      val res = ULong.fromRaw(v + min) // For some reasons, the scala compiler chokes on this being returned
      res
   }.ensuring(x => min <= x)

   /**
    * 8.3 Encoding of an integer value
    *
    * The encoding of an integer value shall be primitive.
    * The contents octets shall consist of one or more octets.
    *
    * @param v The value that is always encoded in the smallest possible number of octets.
    */
   def encodeUnconstrainedWholeNumber(v: Long): Unit = {
      staticRequire(
         bitStream.validate_offset_bytes(1 + GetLengthForEncodingSigned(v))
      )

      // call func that fulfills 8.3.2
      val nBytes: Int = GetLengthForEncodingSigned(v)

      // need space for length and value
      assert(bitStream.validate_offset_bytes(nBytes + 1))

      // encode number - single octet
      appendByte(nBytes.toByte.toRawUByte)
      // encode number
      appendNLeastSignificantBits(v, nBytes * NO_OF_BITS_IN_BYTE)
   }

   /**
    * 8.3 Encoding of an integer value reverse operation
    *
    * To call this func at least 2 octets have to be available on the bitstream
    * The length n is the first octet, n octets with the value follow
    * Values with n > 8 are not supported
    *
    * @return decoded number
    */
   def decodeUnconstrainedWholeNumber(): Long = {
      require(bitStream.validate_offset_bytes(1))

      // get length
      val nBytes = readByte()
      // check bitstream precondition
      assert(bitStream.validate_offset_bytes(nBytes.toRaw))
      // read value
      readNLeastSignificantBits(nBytes.toRaw * NO_OF_BITS_IN_BYTE)
   }

   /**
    * Facade function for real encoding
    * @param vVal real input in IEEE754 double format
    */
   @extern
   def encodeReal(vVal: Double): Unit = {
      encodeRealBitString(java.lang.Double.doubleToRawLongBits(vVal))
   }

   /**
    * Binary encoding will be used
    * REAL = M*B^E
    * where
    * M = S*N*2^F
    *
    * ENCODING is done within three parts
    * part 1 is 1 byte header
    * part 2 is 1 or more byte for exponent
    * part 3 is 3 or more byte for mantissa (N)
    *
    * First byte
    * S :0-->+, S:1-->-1
    * Base will be always be 2 (implied by 6th and 5th bit which are zero)
    * ab: F    (0..3)
    * cd:00 --> 1 byte for exponent as 2's complement
    * cd:01 --> 2 byte for exponent as 2's complement
    * cd:10 --> 3 byte for exponent as 2's complement
    * cd:11 --> 1 byte for encoding the length of the exponent, then the exponent
    *
    * 8 7 6 5 4 3 2 1
    * +-+-+-+-+-+-+-+-+
    * |1|S|0|0|a|b|c|d|
    * +-+-+-+-+-+-+-+-+
    *
    */
   private def encodeRealBitString(vVal: Long): Unit = {
      // according to T-REC-X.690 2021

      var v = vVal

      // 8.5.2 Plus Zero
      if v == DoublePosZeroBitString then
         encodeConstrainedWholeNumber(0, 0, 0xFF)
         return;

      // 8.5.3 Minus Zero
      if v == DoubleNegZeroBitString then
         encodeConstrainedWholeNumber(1, 0, 0xFF)
         encodeConstrainedWholeNumber(0x43, 0, 0xFF)
         return;

      // 8.5.9 SpecialRealValues
      if (v & ExpoBitMask) == ExpoBitMask then

      // 8.5.9 PLUS-INFINITY
         if v == DoublePosInfBitString then
            encodeConstrainedWholeNumber(1, 0, 0xFF)
            encodeConstrainedWholeNumber(0x40, 0, 0xFF)
            return;

         // 8.5.9 MINUS-INFINITY
         else if v == DoubleNegInfBitString then
            encodeConstrainedWholeNumber(1, 0, 0xFF)
            encodeConstrainedWholeNumber(0x41, 0, 0xFF)
            return;

         // 8.5.9 NOT-A-NUMBER
         else
            encodeConstrainedWholeNumber(1, 0, 0xFF)
            encodeConstrainedWholeNumber(0x42, 0, 0xFF)
            return;

      // 8.5.6 a)
      // fixed encoding style to binary
      // 8.5.7.2 exp has always base 2 - bit 0x20 and 0x10 are always 0
      // 8.5.7.3 F value is always zero - bit 0x08 and 0x04 are always 0
      var header = 0x80

      // 8.5.7.1
      if ((v & SignBitMask) == SignBitMask) { // check sign bit
         header |= 0x40
         v &= InverseSignBitMask // clear sign bit
      }

      val (exponent, mantissa) = CalculateMantissaAndExponent(v)

      val nManLen: Int = GetLengthForEncodingUnsigned(mantissa)
      assert(nManLen <= 7) // 52 bit

      val compactExp = RemoveLeadingFFBytesIfNegative(exponent.toRaw)
      val nExpLen: Int = GetLengthForEncodingUnsigned(compactExp.toLong.toRawULong)
      assert(nExpLen >= 1 && nExpLen <= 2)

      // 8.5.7.4
      if nExpLen == 2 then
         header |= 0x01
      else if nExpLen == 3 then // this will never happen with this implementation
         header |= 0x02

      /* encode length */
      encodeConstrainedWholeNumber(1 + nExpLen + nManLen, 0, 0xFF)

      /* encode header */
      encodeConstrainedWholeNumber(header & 0xFF, 0, 0xFF)

      /* encode exponent */
      if exponent.toRaw >= 0 then
         // fill with zeros to have a whole byte
         appendNZeroBits(nExpLen * 8 - GetBitCountUnsigned(exponent.toULong))
         encodeUnsignedInteger(exponent.toULong)
      else
         encodeUnsignedInteger(compactExp.toLong.toRawULong)

      /* encode mantissa */
      appendNZeroBits(nManLen * 8 - GetBitCountUnsigned(mantissa))
      encodeUnsignedInteger(mantissa)
   }


   /**
    * facade function for real decoding
    * @return decoded real value in IE754 double format
    */
   @extern
   def decodeReal(): Double = java.lang.Double.longBitsToDouble(decodeRealBitString())

   /**
    * Real decoding implementation according to the PER standard
    * @return decoded double bits as 64 bit integer
    */
   private def decodeRealBitString(): Long = {
      require(bitStream.validate_offset_bytes(1))

      // get length
      val length = readByte().toRaw

      // 8.5.2 PLUS-ZERO
      if length == 0 then
         return 0

      // sanity check
      assert(length > 0 && length <= DoubleMaxLengthOfSentBytes)

      // get value
      assert(bitStream.validate_offset_bytes(1))
      val header = readByte().toRaw
      assert((header.unsignedToInt & 0x80) == 0x80, "only binary mode supported")

      // 8.5.9 PLUS-INFINITY
      if header == 0x40 then
         DoublePosInfBitString
      // 8.5.9 MINUS-INFINITY
      else if header == 0x41 then
         DoubleNegInfBitString
      // 8.5.9 NOT-A-NUMBER
      else if header == 0x42 then
         DoubleNotANumber
      // 8.5.3 MINUS-ZERO
      else if header == 0x43 then
         DoubleNegZeroBitString
      // Decode 8.5.7
      else
         decodeRealFromBitStream(length.toInt - 1, header.toRawUByte)
   }

   /**
    * Decode real number from bitstream, special cases are decoded by caller
    * The exponent length and other details given in the header have be be
    * decoded before calling this function
    *
    * @param lengthVal already decoded exponent length
    * @param header already decoded header
    * @return decoded real number as 64bit integer
    */
   private def decodeRealFromBitStream(lengthVal: Int, header: UByte): Long = {
      require(lengthVal >= 1 && lengthVal < DoubleMaxLengthOfSentBytes) // without header byte
      require((header.unsignedToInt & 0x80) == 0x80)
      require(bitStream.validate_offset_bytes(lengthVal))

      // 8.5.7.2 Base
      val expFactor: Int = header.unsignedToInt match
         case x if (x & 0x10) > 0 => 3 // 2^3 = 8
         case x if (x & 0x20) > 0 => 4 // 2^4 = 16
         case _ => 1 // 2^1 = 2

      // 8.5.7.3 Factor F
      val factor = 1 << ((header.toRaw & 0x0C) >>> 2)

      // 8.5.7.4 Length of Exponent
      val expLen = (header.toRaw & 0x03) + 1

      // sanity check
      assert(expLen <= lengthVal)

      // decode exponent
      var exponent: Int = if peekBit() then 0xFF_FF_FF_FF else 0

      var i: Int = 0
      (while i < expLen do
         decreases(expLen - i)

         exponent = exponent << 8 | (readByte().toRaw.toInt & 0xFF)

         i += 1
      ).invariant(i >= 0 && i <= expLen)

      // decode mantissa parts
      val length = lengthVal - expLen
      var N: Long = 0
      var j: Int = 0
      (while j < length do
         decreases(length - j)

         N = (N << 8) | (readByte().toRaw.toInt & 0xFF)

         j += 1
      ).invariant(j >= 0 && j <= length)

      var v: Long = GetDoubleBitStringByMantissaAndExp((N * factor).toLong.toRawULong, expFactor * exponent)

      // 8.5.7.1 Set Sign bit
      if (header.toRaw & 0x40) > 0 then
         v |= SignBitMask

      v
   }

   def encodeOctetString_no_length(arr: Array[UByte], nCount: Int): Unit = {
      require(bitStream.validate_offset_bytes(nCount))
      appendByteArray(arr, nCount)
   }

   def decodeOctetString_no_length(nCount: Int): Array[UByte] = {
      require(nCount >= 0 && nCount <= Integer.MAX_VALUE / NO_OF_BITS_IN_BYTE)
      require(bitStream.validate_offset_bytes(nCount))
      readByteArray(nCount)
   }

   def encodeOctetString_fragmentation(arr: Array[UByte], nCount: Int) = {
      require(nCount >= 0)

      var nRemainingItemsVar1: Int = nCount
      var nCurBlockSize1: Int = 0
      var nCurOffset1: Int = 0

      while nRemainingItemsVar1 >= 0x4000 do
         decreases(nRemainingItemsVar1)
         if nRemainingItemsVar1 >= 0x10000 then
            nCurBlockSize1 = 0x10000
            encodeConstrainedWholeNumber(0xC4, 0, 0xFF)
         else if nRemainingItemsVar1 >= 0xC000 then
            nCurBlockSize1 = 0xC000
            encodeConstrainedWholeNumber(0xC3, 0, 0xFF)
         else if nRemainingItemsVar1 >= 0x8000 then
            nCurBlockSize1 = 0x8000
            encodeConstrainedWholeNumber(0xC2, 0, 0xFF)
         else
            nCurBlockSize1 = 0x4000
            encodeConstrainedWholeNumber(0xC1, 0, 0xFF)

         var i1: Int = nCurOffset1
         while i1 < nCurBlockSize1 + nCurOffset1 do
            decreases(nCurBlockSize1 + nCurOffset1 - i1)
            appendByte(arr(i1))
            i1 += 1

         nCurOffset1 += nCurBlockSize1
         nRemainingItemsVar1 -= nCurBlockSize1

      if nRemainingItemsVar1 <= 0x7F then
         encodeConstrainedWholeNumber(nRemainingItemsVar1.toLong, 0, 0xFF)
      else
         appendBit(true)
         encodeConstrainedWholeNumber(nRemainingItemsVar1.toLong, 0, 0x7FFF)


      var i1: Int = nCurOffset1
      (while i1 < (nCurOffset1 + nRemainingItemsVar1) do
         decreases(nCurOffset1 + nRemainingItemsVar1 - i1)
         appendByte(arr(i1))
         i1 += 1
      ).invariant(true) // TODO
   }

   def decodeOctetString_fragmentation(asn1SizeMax: Long): Array[UByte] = {
      require(asn1SizeMax >= 0 && asn1SizeMax < Int.MaxValue)

      val arr: Array[UByte] = Array.fill(asn1SizeMax.toInt)(0.toRawUByte)
      var nCount: Int = 0

      var nLengthTmp1: Long = 0
      var nCurBlockSize1: Long = 0
      var nCurOffset1: Long = 0

      // get header data
      var nRemainingItemsVar1: Long = decodeConstrainedWholeNumber(0, 0xFF)

      // 11xx_xxxx header, there is a next fragment
      (while (nRemainingItemsVar1 & 0xC0) == 0xC0 do
         decreases(asn1SizeMax - nCurOffset1) // TODO: check experimental decrease

         // get current block size
         if nRemainingItemsVar1 == 0xC4 then
            nCurBlockSize1 = 0x10000
         else if nRemainingItemsVar1 == 0xC3 then
            nCurBlockSize1 = 0xC000
         else if nRemainingItemsVar1 == 0xC2 then
            nCurBlockSize1 = 0x8000
         else if nRemainingItemsVar1 == 0xC1 then
            nCurBlockSize1 = 0x4000
         else
            assert(false, "unsupported format")

         // fill current payload fragment into dest
         var i1: Int = nCurOffset1.toInt
         (while (nCurOffset1 + nCurBlockSize1 <= asn1SizeMax) && (i1 < (nCurOffset1 + nCurBlockSize1).toInt) do
            decreases((nCurOffset1 + nCurBlockSize1).toInt - i1)
            arr(i1) = readByte()
            i1 += 1
         ).invariant(true) // TODO invariant

         // sum combined length
         nLengthTmp1 += nCurBlockSize1
         // set offset for next run
         nCurOffset1 += nCurBlockSize1

         // get next header
         nRemainingItemsVar1 = decodeConstrainedWholeNumber(0, 0xFF)

      ).invariant(true) // TODO invariant

      // 1000_0000 header, last fragment has size bigger than 255 - current byte is upper, need to get lower
      if (nRemainingItemsVar1 & 0x80) > 0 then

         nRemainingItemsVar1 <<= 8 // put upper at correct position

         // get size (lower byte)
         nRemainingItemsVar1 |= decodeConstrainedWholeNumber(0, 0xFF) // combine 15bit (7 upper, 8 lower) into size
         nRemainingItemsVar1 &= 0x7FFF // clear the control bit

      assert(nCurOffset1 + nRemainingItemsVar1 <= asn1SizeMax) // TODO check with C implementation and standard

      var i1: Int = nCurOffset1.toInt

      // fill last payload fragment into dest
      (while i1 < (nCurOffset1 + nRemainingItemsVar1).toInt do
         decreases((nCurOffset1 + nRemainingItemsVar1).toInt - i1)
         arr(i1) = readByte()
         i1 += 1
      ).invariant(true) // TODO invariant

      // add remainingSize to already written size - this var holds the absolut number in all fragments
      nLengthTmp1 += nRemainingItemsVar1

      // resize output array and copy data
      assert((nLengthTmp1 >= 1) && (nLengthTmp1 <= asn1SizeMax)) // TODO check with C implementation and standard

      val newArr: Array[UByte] = Array.fill(nLengthTmp1.toInt)(0.toRawUByte)
      arrayCopyOffsetLen(arr, newArr, 0, 0, newArr.length)
      newArr
   }

   def encodeOctetString(arr: Array[UByte], nCount: Int, asn1SizeMin: Long, asn1SizeMax: Long) = {
      require(nCount >= asn1SizeMin && nCount <= asn1SizeMax)

      if asn1SizeMax < 65536 then
         if asn1SizeMin != asn1SizeMax then
            encodeConstrainedWholeNumber(nCount.toLong, asn1SizeMin, asn1SizeMax)
         encodeOctetString_no_length(arr, nCount)

      else
         encodeOctetString_fragmentation(arr, nCount)
   }

   def decodeOctetString(asn1SizeMin: Long, asn1SizeMax: Long): Array[UByte] = {

      if asn1SizeMax >= 0x1_00_00 then // 65'536, bigger than 2 unsigned bytes
         return decodeOctetString_fragmentation(asn1SizeMax)

      var nCount: Int = 0
      if asn1SizeMin != asn1SizeMax then
         nCount = decodeConstrainedWholeNumber(asn1SizeMin, asn1SizeMax).toInt
      else
         nCount = asn1SizeMin.toInt

      assert(nCount >= asn1SizeMin && nCount <= asn1SizeMax) // TODO check with C implementation and standard

      decodeOctetString_no_length(nCount)
   }

   def encodeBitString(arr: Array[UByte], nCount: Int, asn1SizeMin: Long, asn1SizeMax: Long): Unit = {
      if asn1SizeMax < 65536 then
         if asn1SizeMin != asn1SizeMax then
            encodeConstrainedWholeNumber(nCount.toLong, asn1SizeMin, asn1SizeMax)

         appendBitsMSBFirst(arr, nCount)

      else
         var nRemainingItemsVar1: Long = nCount.toLong
         var nCurBlockSize1: Long = 0
         var nCurOffset1: Long = 0
         (while nRemainingItemsVar1 >= 0x4000 do
            decreases(nRemainingItemsVar1)

            if nRemainingItemsVar1 >= 0x10000 then
               nCurBlockSize1 = 0x10000
               encodeConstrainedWholeNumber(0xC4, 0, 0xFF)

            else if nRemainingItemsVar1 >= 0xC000 then
               nCurBlockSize1 = 0xC000
               encodeConstrainedWholeNumber(0xC3, 0, 0xFF)
            else if nRemainingItemsVar1 >= 0x8000 then
               nCurBlockSize1 = 0x8000
               encodeConstrainedWholeNumber(0xC2, 0, 0xFF)
            else
               nCurBlockSize1 = 0x4000
               encodeConstrainedWholeNumber(0xC1, 0, 0xFF)

            val t: Array[UByte] = Array.fill(nCurBlockSize1.toInt)(0.toRawUByte) // STAINLESS: arr.slice((nCurOffset1 / 8).toInt, (nCurOffset1 / 8).toInt + nCurBlockSize1.toInt)
            appendBitsMSBFirst(t, nCurBlockSize1.toInt)
            nCurOffset1 += nCurBlockSize1
            nRemainingItemsVar1 -= nCurBlockSize1
         ).invariant(true) // TODO invariant

         if nRemainingItemsVar1 <= 0x7F then
            encodeConstrainedWholeNumber(nRemainingItemsVar1, 0, 0xFF)
         else
            appendBit(true)
            encodeConstrainedWholeNumber(nRemainingItemsVar1, 0, 0x7FFF)

         val t: Array[UByte] = Array.fill(nRemainingItemsVar1.toInt)(0.toRawUByte) // STAINLESS: arr.slice((nCurOffset1 / 8).toInt, (nCurOffset1 / 8).toInt + nRemainingItemsVar1.toInt)
         appendBitsMSBFirst(t, nRemainingItemsVar1.toInt)
   }

   def decodeBitString(asn1SizeMin: Long, asn1SizeMax: Long): Array[UByte] = {
      require(asn1SizeMax <= Int.MaxValue)
      // TODO enhance precondition

      if (asn1SizeMax < 65536) {
         var nCount: Long = 0
         if asn1SizeMin != asn1SizeMax then
            nCount = decodeConstrainedWholeNumber(asn1SizeMin, asn1SizeMax)
         else
            nCount = asn1SizeMin

         return readBits(nCount.toInt)

      }

      var nCurBlockSize1: Long = 0
      var nCurOffset1: Long = 0
      var nLengthTmp1: Long = 0
      var nRemainingItemsVar1: Long = decodeConstrainedWholeNumber(0, 0xFF)

      val arr: Array[UByte] = Array.fill(asn1SizeMax.toInt)(0.toRawUByte)
      (while (nRemainingItemsVar1 & 0xC0) == 0xC0 do
         decreases(asn1SizeMax - nCurOffset1) // TODO: check experimental decrease
         if nRemainingItemsVar1 == 0xC4 then
            nCurBlockSize1 = 0x10000
         else if nRemainingItemsVar1 == 0xC3 then
            nCurBlockSize1 = 0xC000
         else if nRemainingItemsVar1 == 0xC2 then
            nCurBlockSize1 = 0x8000
         else if nRemainingItemsVar1 == 0xC1 then
            nCurBlockSize1 = 0x4000
         else
            assert(false, "broken State") // TODO check with C implementation and standard

         assert(nCurOffset1 + nCurBlockSize1 > asn1SizeMax)

         arrayCopyOffsetLen(readBits(nCurBlockSize1.toInt), arr, 0, (nCurOffset1 / 8).toInt, nCurBlockSize1.toInt)
         nLengthTmp1 += nCurBlockSize1
         nCurOffset1 += nCurBlockSize1
         nRemainingItemsVar1 = decodeConstrainedWholeNumber(0, 0xFF)

      ).invariant(true) // TODO invariant

      if (nRemainingItemsVar1 & 0x80) > 0 then
         nRemainingItemsVar1 <<= 8
         nRemainingItemsVar1 |= decodeConstrainedWholeNumber(0, 0xFF)
         nRemainingItemsVar1 &= 0x7FFF

      assert(nCurOffset1 + nRemainingItemsVar1 <= asn1SizeMax)

      arrayCopyOffsetLen(readBits(nRemainingItemsVar1.toInt), arr, 0, (nCurOffset1 / 8).toInt, nRemainingItemsVar1.toInt)
      nLengthTmp1 += nRemainingItemsVar1
      assert((nLengthTmp1 >= 1) && (nLengthTmp1 <= asn1SizeMax))

      arr
   }

   // ***** Public wrapper for bitstream functions

   def appendBitOne(): Unit = {
      require(bitStream.validate_offset_bit())
      bitStream.appendBitOne()
   }

   def appendBitZero(): Unit = {
      require(bitStream.validate_offset_bit())
      bitStream.appendBitZero()
   }

   def appendBit(v: Boolean): Unit = {
      require(bitStream.validate_offset_bit())
      bitStream.appendBit(v)
   }

   def peekBit(): Boolean = {
      require(bitStream.validate_offset_bit())
      bitStream.peekBit()
   }

   def readBit(): Boolean = {
      require(bitStream.validate_offset_bit())
      bitStream.readBit()
   }

   def appendNZeroBits(nBits: Long): Unit = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.appendNZeroBits(nBits)
   }

   def appendNOneBits(nBits: Long): Unit = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.appendNOneBits(nBits)
   }

   def appendBitsLSBFirst(v: Long, nBits: Int): Unit = { // TODO remove if never used
      require(bitStream.validate_offset_bits(nBits))
      bitStream.appendBitsLSBFirst(v, nBits)
   }

   def appendBitsMSBFirst(srcBuffer: Array[UByte], nBits: Long): Unit = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.appendBitsMSBFirst(srcBuffer, nBits)
   }

   def appendNLeastSignificantBits(v: Long, nBits: Int): Unit = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.appendNLeastSignificantBits(v, nBits)
   }

   def readNLeastSignificantBits(nBits: Int): Long = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.readNLeastSignificantBits(nBits)
   }

   def readBits(nBits: Long): Array[UByte] = {
      require(nBits >= 0 && bitStream.validate_offset_bits(nBits))
      bitStream.readBits(nBits)
   }

   def appendByte(value: UByte): Unit = {
      require(bitStream.validate_offset_byte())
      bitStream.appendByte(value)
   }


   def readByte(): UByte = {
      require(bitStream.validate_offset_byte())
      bitStream.readByte()
   }

   def appendByteArray(arr: Array[UByte], noOfBytes: Int): Unit = {
      require(bitStream.validate_offset_bytes(noOfBytes))
      bitStream.appendByteArray(arr, noOfBytes)
   }

   def readByteArray(nBytes: Int): Array[UByte] = {
      require(nBytes >= 0 && nBytes <= Integer.MAX_VALUE / NO_OF_BITS_IN_BYTE)
      require(bitStream.validate_offset_bytes(nBytes))
      bitStream.readByteArray(nBytes)
   }

   def appendPartialByte(vVal: UByte, nBits: Byte): Unit = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.appendPartialByte(vVal, nBits)
   }

   def readPartialByte(nBits: Int): UByte = {
      require(nBits >= 0 && nBits <= NO_OF_BITS_IN_BYTE)
      require(bitStream.validate_offset_bits(nBits))
      bitStream.readPartialByte(nBits)
   }

   def checkBitPatternPresent(bit_terminated_pattern: Array[UByte], nBits: Long): Boolean = {
      require(bitStream.validate_offset_bits(nBits))
      bitStream.checkBitPatternPresent(bit_terminated_pattern, nBits)
   }

   // broken in C - do not translate
//   def readBits_nullterminated(bit_terminated_pattern: Array[UByte], bit_terminated_pattern_size_in_bits: Long, nMaxReadBits: Long): OptionMut[(Array[UByte], Long)] = {
//      val isValidPrecondition = bitStream.validate_offset_bits(nMaxReadBits)
//      assert(isValidPrecondition)
//      isValidPrecondition match
//         case true => SomeMut(bitStream.readBitsUntilTerminator(bit_terminated_pattern, bit_terminated_pattern_size_in_bits, nMaxReadBits))
//         case false => NoneMut()
//   }

   def alignToByte(): Unit = {
      require(bitStream.validate_offset_bits(
         NO_OF_BITS_IN_BYTE - (bitStream.bitIndex() % NO_OF_BITS_IN_BYTE)))
      bitStream.alignToByte()
   }

   def alignToShort(): Unit = {
      // TODO: precondition
      bitStream.alignToShort()
//      alignToByte()
//      currentByte = ((currentByte + (NO_OF_BYTES_IN_JVM_SHORT - 1)) / NO_OF_BYTES_IN_JVM_SHORT) * NO_OF_BYTES_IN_JVM_SHORT
   }

   def alignToInt(): Unit = {
      // TODO: precondition
      bitStream.alignToInt()
//      alignToByte()
//      currentByte = ((currentByte + (NO_OF_BYTES_IN_JVM_INT - 1)) / NO_OF_BYTES_IN_JVM_INT) * NO_OF_BYTES_IN_JVM_INT
   }

   def resetBitIndex(): Unit = {
      bitStream.resetBitIndex()
   }

   def getBufferLength: Int = {
      bitStream.getBufferLength
   }

   /**
    *
    * @return the number of used bytes in the underlying buffer
    *         if the currentBit is not 0, currentByte is added by 1
    *
    */
   def getLength: Int = {
      bitStream.getLength
   }
}
