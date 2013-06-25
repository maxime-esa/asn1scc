with spark_asn1_rtl;
use type spark_asn1_rtl.Asn1UInt;
use type spark_asn1_rtl.Asn1Int;

PACKAGE body Test1 IS


    PROCEDURE Init_Msg1(msg: OUT Msg1 )
    IS
    BEGIN
        msg.a := 0;
        msg.b := 0;
    END Init_Msg1;


    PROCEDURE Validate_Msg1(msg: IN Msg1;  Res : OUT spark_asn1_rtl.ASN1_RESULT)
    IS
    BEGIN
        Res := spark_asn1_rtl.ASN1_RESULT'(Success => True,ErrorCode => 0);
        Res := spark_asn1_rtl.ASN1_RESULT'(Success => Res.Success AND (msg.a>=0 AND msg.a <=7),ErrorCode => 1001);
        IF Res.Success THEN
       	    Res := spark_asn1_rtl.ASN1_RESULT'(Success => msg.b>=0 AND msg.b <=15,ErrorCode => 1002);
        END IF;
    END Validate_Msg1;


    PROCEDURE Encode_Msg1(S : in out spark_asn1_rtl.BitArray; K : in out Natural; msg: IN Msg1 )
    IS
    BEGIN
        spark_asn1_rtl.UPER_Enc_ConstraintWholeNumber(S,K,msg.a,0,3);

        spark_asn1_rtl.UPER_Enc_ConstraintWholeNumber(S,K,msg.b,0,4);
    END Encode_Msg1;


   PROCEDURE Decode_Msg1(S : in spark_asn1_rtl.BitArray; K : in out spark_asn1_rtl.DECODE_PARAMS; msg: IN OUT Msg1; Res : OUT spark_asn1_rtl.ASN1_RESULT )
    IS
    BEGIN
        Res.ErrorCode := 1001;
        spark_asn1_rtl.UPER_Dec_ConstraintWholeNumber(S,K,msg.a,0,7, 3, res.Success);
        IF res.Success THEN
            Res.ErrorCode := 1002;
            spark_asn1_rtl.UPER_Dec_ConstraintWholeNumber(S,K,msg.b,0,15,4, res.Success);
        END IF;
    END Decode_Msg1;



    PROCEDURE Encode_MsgSqOf(S : in out spark_asn1_rtl.BitArray; K : in out Natural; msg: IN MsgSqOf )
    --# derives S from S , K, msg & K from K, msg;
    --# pre msg.Length>=1 and msg.Length<=20 and
    --#     K+1>= S'First and K + 5+20*7 <= S'Last;
    --# post K<=K~+5+20*7;
    IS
    BEGIN
        spark_asn1_rtl.UPER_Enc_ConstraintWholeNumber(S,K,spark_asn1_rtl.Asn1Int(msg.Length),1,5);
        FOR I in integer range 1..msg.Length LOOP
            --# assert K=5+K~+7*(I-1);
            Encode_Msg1(S,K,msg.Data(I));
        END LOOP;
    END Encode_MsgSqOf;

    PROCEDURE Decode_MsgSqOf(S : in spark_asn1_rtl.BitArray; K : in out spark_asn1_rtl.DECODE_PARAMS; msg: IN OUT MsgSqOf; Res : OUT spark_asn1_rtl.ASN1_RESULT )
    --# derives msg from S , K, msg &
    --#         K from S, K &
    --#         res from S, K;
    --# pre K.K+1>= S'First and K.K + 5+20*7 <= S'Last;
    --# post K.K>=K~.K+5 and K.K<=K~.K+5+20*7 and
    --#      (Res.Success = True  -> (  msg.Length>=1 and msg.Length<=20 ));

    IS
        I:Integer:=1;
    BEGIN
        Res.ErrorCode := 1002;
        spark_asn1_rtl.UPER_Dec_ConstraintWholeNumberInt(S,K,msg.Length,1,20, 5, res.Success);
        IF res.Success THEN
            WHILE I<=msg.Length AND res.Success LOOP
                --# assert  I>=1 and I<=msg.Length  and
                --#        K.K>=K~.K+5 and K.K<=K~.K+5 + 7*(I-1);
                Decode_Msg1(S,K,msg.Data(I),res);
                I := I + 1;
            END LOOP;
        END IF;
    END Decode_MsgSqOf;







END Test1;
