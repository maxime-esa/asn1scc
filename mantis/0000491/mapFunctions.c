#include <string.h>
#include <assert.h>
#include <math.h>
#include <float.h>

#include "asn1crt.h"

asn1SccSint milbus2_encode(asn1SccSint val) {
	return val == 32 ? 0 : val;
}

asn1SccSint milbus2_decode(asn1SccSint val) {
	return val == 0 ? 32 : val;
}
