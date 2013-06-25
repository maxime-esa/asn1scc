WITH spark_asn1_rtl;
WITH SPARK_IO_05;
WITH MY_MODULE;
--# inherit spark_asn1_rtl, SPARK_IO_05, MY_MODULE;
--# main_program;



FUNCTION MainProgram RETURN INTEGER
IS --# hide MainProgram

    retCode     : INTEGER:=0;
    console     : SPARK_IO_05.File_Type;
    decodedPDU  : MY_MODULE.MySequence;
    stream      : MY_MODULE.MySequence_uPER_Stream;
    result      : spark_asn1_rtl.ASN1_RESULT;

    d1 		: Standard.Long_Float := Standard.Long_Float'Last/100.0;
    f1		: Standard.Float;

BEGIN

        f1 := Standard.Float(d1);



    console := SPARK_IO_05.Standard_Output;

    -- Check value against ASN.1 constraints
    result := MY_MODULE.MySequence_IsConstraintValid(MY_MODULE.aSeq);
    IF result.Success THEN
        -- Encode value
        MY_MODULE.MySequence_uPER_Encode(MY_MODULE.aSeq, stream);
        -- at this point steam contains the uPER data
        MY_MODULE.MySequence_uPER_Decode(decodedPDU, stream, result);
        IF result.Success THEN
            -- Check value against ASN.1 constraints
            result := MY_MODULE.MySequence_IsConstraintValid(decodedPDU);
            IF result.Success THEN
                IF NOT MY_MODULE.MySequence_Equal(MY_MODULE.aSeq, decodedPDU) THEN
                    SPARK_IO_05.Put_String(console, "Equal Failed!", 30);
                    retCode := 4;
                END IF;
            ELSE
                SPARK_IO_05.Put_String(console, "ASN.1 validations in the decoded message failed", 30);
                SPARK_IO_05.Put_Integer(console, result.ErrorCode ,10, 10);
                retCode := 3;
            END IF;
        ELSE
            SPARK_IO_05.Put_String(console, "Decode failed", 30);
            SPARK_IO_05.Put_Integer(console, result.ErrorCode ,10, 10);
            retCode := 2;
        END IF;
    ELSE
        SPARK_IO_05.Put_String(console, "ASN.1 validations failed", 30);
        SPARK_IO_05.Put_Integer(console, result.ErrorCode ,10, 10);
        retCode := 1;
    END IF;

    RETURN retCode;
END MainProgram;
