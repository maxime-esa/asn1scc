
#include "ByteStream.h"
#include <string.h>

void ByteStream_Init(ByteStream* pStrm, byte* buf, long count)
{
    pStrm->count = count;
    pStrm->buf = buf;
    memset(pStrm->buf,0x0,(size_t)count);
    pStrm->currentByte = 0;
    pStrm->EncodeWhiteSpace = FALSE;
}

void ByteStream_AttachBuffer(ByteStream* pStrm, unsigned char* buf, long count)
{
    pStrm->count = count;
    pStrm->buf = buf;
    pStrm->currentByte = 0;
}

asn1SccSint ByteStream_GetLength(ByteStream* pStrm)
{
    return pStrm->currentByte;
}

flag ByteStream_PutByte(ByteStream* pStrm, byte v)
{
    if (pStrm->currentByte+1>pStrm->count+1)
        return FALSE;

    pStrm->buf[pStrm->currentByte] = v;
    pStrm->currentByte++;
    return TRUE;
}

flag ByteStream_GetByte(ByteStream* pStrm, byte* v)  {
    if (pStrm->currentByte+1>pStrm->count+1)
        return FALSE;
    *v = pStrm->buf[pStrm->currentByte];
    pStrm->currentByte++;
    return TRUE;
}
