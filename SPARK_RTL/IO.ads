WITH spark_asn1_rtl;
--# inherit spark_asn1_rtl;


PACKAGE IO
    --# own in Dummy_state;
IS
    PROCEDURE ReadDataDummy(S : in out spark_asn1_rtl.BitArray);
    --# global in Dummy_state;
    --# derives S from S , Dummy_state;

END IO;

