#ifndef ASN1SCC_ASN1CRT_UTIL_H_
#define ASN1SCC_ASN1CRT_UTIL_H_

#include "asn1crt_core.h"


#ifdef  __cplusplus
extern "C" {
#endif

#if WORD_SIZE==8
extern const asn1SccUint64 ber_aux[];
#else
extern const asn1SccUint32 ber_aux[];
#endif

int GetCharIndex(char ch, byte allowedCharSet[], int setLen);

int GetNumberOfBitsForNonNegativeInteger(asn1SccUint v);

int GetLengthInBytesOfSInt(asn1SccSint v);
int GetLengthInBytesOfUInt(asn1SccUint64 v);

asn1SccUint int2uint(asn1SccSint v);
asn1SccSint uint2int(asn1SccUint v, int uintSizeInBytes);

asn1SccSint milbus_encode(asn1SccSint val);
asn1SccSint milbus_decode(asn1SccSint val);


#ifdef _MSC_VER
#pragma warning( disable : 4127)
#endif

#define ASSERT_OR_RETURN_FALSE(_Expression) do { assert(_Expression); if (!(_Expression)) return FALSE;} while(0)



#ifdef  __cplusplus
}
#endif

#endif

