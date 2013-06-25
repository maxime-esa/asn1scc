WITH spark_asn1_rtl;
--# inherit spark_asn1_rtl;


PACKAGE Test1
IS




    SUBTYPE Msg1_a is spark_asn1_rtl.Asn1Int range 0..7;
    SUBTYPE Msg1_b is spark_asn1_rtl.Asn1Int range 0..15;

    type Msg1 is record
        a : Msg1_a;	-- 0 .. 7
        b : Msg1_b;	-- 0 .. 15
    end record;




    SUBTYPE MsgSqOfList_index is integer range 1..20;

    TYPE MsgSqOfList IS ARRAY (MsgSqOfList_index) OF Msg1;

    SUBTYPE MsgSqOf_length_index is integer range 1..20;

    TYPE MsgSqOf IS  RECORD
       Length : MsgSqOf_length_index;
       Data  : MsgSqOfList;
    END RECORD;





    TYPE MyChoice_selection IS (a_PRESENT, b_PRESENT, c_PRESENT, d_PRESENT);
    for MyChoice_selection use (a_PRESENT => 1, b_PRESENT => 2, c_PRESENT => 3, d_PRESENT => 4);
    for MyChoice_selection'Size use 32;





    TYPE MyChoice IS RECORD
        kind : MyChoice_selection;
              a: spark_asn1_rtl.Asn1Int;
              b: spark_asn1_rtl.Asn1Int;
              c: spark_asn1_rtl.Asn1Real;
              d: Msg1;
    END RECORD;








    PROCEDURE Init_Msg1(msg: OUT Msg1 );
    --# derives msg from;

    PROCEDURE Validate_Msg1(msg: IN Msg1;  Res : OUT spark_asn1_rtl.ASN1_RESULT);
    --# derives Res from msg;


    PROCEDURE Encode_Msg1(S : in out spark_asn1_rtl.BitArray; K : in out Natural; msg: IN Msg1 );
    --# derives S from S , K, msg & K from K;
    --# pre K+1>= S'First and K + 7 <= S'Last;
    --# post K=K~+7;

    PROCEDURE Decode_Msg1(S : in spark_asn1_rtl.BitArray; K : in out spark_asn1_rtl.DECODE_PARAMS; msg: IN OUT Msg1; Res : OUT spark_asn1_rtl.ASN1_RESULT );
    --# derives msg from S , K, msg &
    --#         K from S, K &
    --#         res from S, K;
    --# pre K.K+1>= S'First and K.K + 7 <= S'Last;
    --# post K.K>=K~.K and K.K<=K~.K+7;


END Test1;

