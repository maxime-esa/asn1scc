
#include "asn1crt_util.h"


#if WORD_SIZE==8
const asn1SccUint64 ber_aux[] = {
    0xFF,
    0xFF00,
    0xFF0000,
    0xFF000000,
    0xFF00000000ULL,
    0xFF0000000000ULL,
    0xFF000000000000ULL,
    0xFF00000000000000ULL };
#else
const asn1SccUint32 ber_aux[] = {
    0xFF,
    0xFF00,
    0xFF0000,
    0xFF000000 };
#endif



asn1SccUint int2uint(asn1SccSint v) {
    asn1SccUint ret = 0;
    if (v < 0) {
        ret = (asn1SccUint)(-v - 1);
        ret = ~ret;
    }
    else {
        ret = (asn1SccUint)v;
    };
    return ret;
}

asn1SccSint uint2int(asn1SccUint v, int uintSizeInBytes) {
    int i;
    asn1SccUint tmp = 0x80;
    flag bIsNegative = (v & (tmp << ((uintSizeInBytes - 1) * 8)))>0;
    if (!bIsNegative)
        return (asn1SccSint)v;
    for (i = WORD_SIZE - 1; i >= uintSizeInBytes; i--)
        v |= ber_aux[i];
    return -(asn1SccSint)(~v) - 1;
}

int GetCharIndex(char ch, byte Set[], int setLen)
{
    int i=0;
    for(i=0; i<setLen; i++)
        if (ch == Set[i])
            return i;
    return 0;
}

static int GetNumberOfBitsForNonNegativeInteger32(asn1SccUint32 v)
{
    int ret=0;

    if (v<0x100) {
        ret = 0;
    } else if (v<0x10000) {
        ret = 8;
        v >>= 8;
    } else if (v<0x1000000) {
        ret = 16;
        v >>= 16;
    } else {
        ret = 24;
        v >>= 24;
    }
    while( v>0 ) {
        v >>= 1;
        ret++;
    }
    return ret;
}

int GetNumberOfBitsForNonNegativeInteger(asn1SccUint v)
{
#if WORD_SIZE==8
    if (v<0x100000000LL)
        return GetNumberOfBitsForNonNegativeInteger32((asn1SccUint32)v);
    else {
        asn1SccUint32 hi = (asn1SccUint32)(v>>32);
        return 32 + GetNumberOfBitsForNonNegativeInteger32(hi);
    }
#else
    return GetNumberOfBitsForNonNegativeInteger32(v);
#endif
}

int GetLengthInBytesOfUInt(asn1SccUint64 v)
{
    int ret=0;
    asn1SccUint32 v32 = (asn1SccUint32)v;
#if WORD_SIZE==8
    if (v>0xFFFFFFFF) {
        ret = 4;
        v32 = (asn1SccUint32)(v>>32);
    }
#endif

    if (v32<0x100)
        return ret+1;
    if (v32<0x10000)
        return ret+2;
    if (v32<0x1000000)
        return ret+3;
    return ret+4;
}

static int GetLengthSIntHelper(asn1SccUint v)
{
    int ret=0;
    asn1SccUint32 v32 = (asn1SccUint32)v;
#if WORD_SIZE==8
    if (v>0x7FFFFFFF) {
        ret = 4;
        v32 = (asn1SccUint32)(v>>32);
    }
#endif

    if (v32<=0x7F)
        return ret+1;
    if (v32<=0x7FFF)
        return ret+2;
    if (v32<=0x7FFFFF)
        return ret+3;
    return ret+4;
}

int GetLengthInBytesOfSInt(asn1SccSint v)
{
    if (v >= 0)
        return GetLengthSIntHelper((asn1SccUint)v);

    return GetLengthSIntHelper((asn1SccUint)(-v - 1));
}


asn1SccSint milbus_encode(asn1SccSint val)
{
  return val == 32 ? 0 : val;
}

asn1SccSint milbus_decode(asn1SccSint val)
{
  return val == 0 ? 32 : val;
}
