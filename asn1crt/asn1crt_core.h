#ifndef ASN1SCC_ASN1CRT_CORE_H_
#define ASN1SCC_ASN1CRT_CORE_H_

#ifdef  __cplusplus
extern "C" {
#endif

#if (!defined(_MSC_VER) || _MSC_VER >= 1800)
#  ifndef SWIG
#    include <stdbool.h>
#  endif
#else
typedef unsigned char bool;
#define true 1
#define false 0
#endif


#ifndef NULL
#define NULL	0
#endif

#ifndef TRUE
#define TRUE	true
#endif

#ifndef FALSE
#define FALSE	false
#endif

#ifndef WORD_SIZE
#define WORD_SIZE	8
#endif


typedef int asn1SccSint32;
typedef unsigned int asn1SccUint32;

typedef unsigned char byte;

typedef long long asn1SccSint64;
typedef unsigned long long asn1SccUint64;

#if WORD_SIZE==8
typedef asn1SccUint64 asn1SccUint;
typedef asn1SccSint64 asn1SccSint;
#else
typedef asn1SccUint32 asn1SccUint;
typedef asn1SccSint32 asn1SccSint;
#endif


typedef bool flag;

typedef char NullType;

#define ERR_INSUFFICIENT_DATA	101
#define ERR_INCORRECT_PER_STREAM	102
#define ERR_INVALID_CHOICE_ALTERNATIVE	103
#define ERR_INVALID_ENUM_VALUE	104
#define ERR_INVALID_XML_FILE	200
#define ERR_INVALID_BER_FILE	201
#define ERR_BER_LENGTH_MISMATCH	202

#ifdef  __cplusplus
}
#endif

#endif
