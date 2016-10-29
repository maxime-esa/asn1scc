#ifndef ASN1SCC_ASN1CRT_XER_H_
#define ASN1SCC_ASN1CRT_XER_H_

#include "asn1crt_core.h"
#include "ByteStream.h"


#ifdef  __cplusplus
extern "C" {
#endif

typedef struct {
	int TokenID;
	char Value[100];
} Token;

typedef struct {
	char Name[50];
	char Value[100];
} XmlAttribute;

typedef struct {
	XmlAttribute attrs[20];
	int nCount;
} XmlAttributeArray;




void Xer_EncodeXmlHeader(ByteStream* pByteStrm, const char* xmlHeader);
flag Xer_EncodeComment(ByteStream* pByteStrm, const char* comment, int *pErrCode);

flag Xer_EncodeInteger(ByteStream* pByteStrm, const char* elementTag, asn1SccSint value, int *pErrCode, int level);
flag Xer_EncodeBoolean(ByteStream* pByteStrm, const char* elementTag, flag value, int *pErrCode, int level);
flag Xer_EncodeEnumerated(ByteStream* pByteStrm, const char* elementTag, const char* value, int *pErrCode, int level);
flag Xer_EncodeReal(ByteStream* pByteStrm, const char* elementTag, double value, int *pErrCode, int level);
flag Xer_EncodeString(ByteStream* pByteStrm, const char* elementTag, const char* value, int *pErrCode, int level);
flag Xer_EncodeOctetString(ByteStream* pByteStrm, const char* elementTag, const byte value[], int nCount, int *pErrCode, int level);
flag Xer_EncodeBitString(ByteStream* pByteStrm, const char* elementTag, const byte value[], int nCount, int *pErrCode, int level);



flag Xer_DecodeInteger(ByteStream* pByteStrm, const char* elementTag, asn1SccSint* value, int *pErrCode);
flag Xer_DecodeBoolean(ByteStream* pByteStrm, const char* elementTag, flag* value, int *pErrCode);
flag Xer_DecodeEnumerated(ByteStream* pByteStrm, const char* elementTag, char* value, int *pErrCode);
flag Xer_DecodeReal(ByteStream* pByteStrm, const char* elementTag, double* value, int *pErrCode);
flag Xer_DecodeString(ByteStream* pByteStrm, const char* elementTag, char* value, int *pErrCode);
flag Xer_DecodeOctetString(ByteStream* pByteStrm, const char* elementTag, byte value[], long* nCount, int *pErrCode);
flag Xer_DecodeBitString(ByteStream* pByteStrm, const char* elementTag, byte value[], long* nCount, int *pErrCode);
flag Xer_EncodeComplexElementStart(ByteStream* pByteStrm, const char* elementTag, XmlAttributeArray* pAttrs, int *pErrCode, int level);
flag Xer_EncodeComplexElementEnd(ByteStream* pByteStrm, const char* elementTag, int *pErrCode, int level);
flag Xer_DecodeComplexElementStart(ByteStream* pByteStrm, const char* elementTag, XmlAttributeArray* pAttrs, int *pErrCode);
flag Xer_DecodeComplexElementEnd(ByteStream* pByteStrm, const char* elementTag, int *pErrCode);
flag Xer_NextEndElementIs(ByteStream* pByteStrm, const char* elementTag);
flag Xer_NextStartElementIs(ByteStream* pByteStrm, const char* elementTag);
flag Xer_LA_NextElementTag(ByteStream* pByteStrm, char* elementTag);
flag LoadXmlFile(const char* fileName, ByteStream* pStrm, int* nBytesLoaded);

#ifdef  __cplusplus
}
#endif

#endif
