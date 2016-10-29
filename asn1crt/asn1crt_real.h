#ifndef ASN1SCC_ASN1CRT_REAL_H_
#define ASN1SCC_ASN1CRT_REAL_H_

#include "asn1crt_core.h"

#ifdef  __cplusplus
extern "C" {
#endif

#ifdef _MSC_VER
#  ifndef INFINITY
#    define INFINITY (DBL_MAX+DBL_MAX)
#  endif
#  ifndef NAN
#    define NAN (INFINITY-INFINITY)
#  endif
#endif

#ifndef INFINITY
  #ifdef __GNUC__
    #define INFINITY (__builtin_inf())
  #endif
#endif




void CalculateMantissaAndExponent(double d, int* exp, asn1SccUint64* mantissa);
double GetDoubleByMantissaAndExp(asn1SccUint mantissa, int exp);

#ifdef  __cplusplus
}
#endif

#endif
