WITH Ada.Text_IO;
WITH adaasn1rtl; use type adaasn1rtl.Asn1UInt; use type adaasn1rtl.Asn1Int;use type adaasn1rtl.BIT;
WITH MOD1;
WITH MOD1_auto_encs_decs;
--# inherit adaasn1rtl, MOD1, MOD1_auto_encs_decs;
--# main_program;


FUNCTION MainProgram RETURN INTEGER
IS --# hide MainProgram
    USE Ada.Text_IO;
    USE MOD1;
    result      : adaasn1rtl.TEST_CASE_RESULT;
    totalErrors  : INTEGER:=0;
    
BEGIN

    result := MOD1_auto_encs_decs.RGBCOLORS_uPER_enc_dec(red);
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'rgbcolors_1' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'rgbcolors_1' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'rgbcolors_1' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'rgbcolors_1' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'rgbcolors_1' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was rgbcolors_1 RGBCOLORS ::= red");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    result := MOD1_auto_encs_decs.RGBCOLORS_uPER_enc_dec(green);
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'rgbcolors_2' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'rgbcolors_2' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'rgbcolors_2' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'rgbcolors_2' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'rgbcolors_2' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was rgbcolors_2 RGBCOLORS ::= green");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    result := MOD1_auto_encs_decs.RGBCOLORS_uPER_enc_dec(blue);
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'rgbcolors_3' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'rgbcolors_3' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'rgbcolors_3' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'rgbcolors_3' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'rgbcolors_3' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was rgbcolors_3 RGBCOLORS ::= blue");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    result := MOD1_auto_encs_decs.CH1_uPER_enc_dec(CH1_left_set(1));
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'ch1_1' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'ch1_1' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'ch1_1' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'ch1_1' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'ch1_1' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was ch1_1 CH1 ::= left:1");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    result := MOD1_auto_encs_decs.CH1_uPER_enc_dec(CH1_right_set(red));
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'ch1_2' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'ch1_2' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'ch1_2' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'ch1_2' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'ch1_2' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was ch1_2 CH1 ::= right:red");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    result := MOD1_auto_encs_decs.CH1_left_uPER_enc_dec(1);
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'ch1_left_1' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'ch1_left_1' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'ch1_left_1' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'ch1_left_1' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'ch1_left_1' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was ch1-left_1 CH1-left ::= 1");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    result := MOD1_auto_encs_decs.CH1_left_uPER_enc_dec(10);
    IF NOT result.Success THEN
        CASE result.Step IS
            WHEN adaasn1rtl.TC_VALIDATE =>
                Put_Line ("Test case 'ch1_left_2' failed in validation"); 
            WHEN adaasn1rtl.TC_ENCODE =>
                Put_Line ("Test case 'ch1_left_2' failed in encoding");
            WHEN adaasn1rtl.TC_DECODE =>
                Put_Line ("Test case 'ch1_left_2' failed in decoding");
            WHEN adaasn1rtl.TC_VALIDATE_DECODED =>
                Put_Line ("Test case 'ch1_left_2' failed in the validation of the decoded message");
            WHEN adaasn1rtl.TC_EQUAL =>
                Put_Line ("Test case 'ch1_left_2' failed. Encoded and decoded messages are different");
        END CASE;
        Put_Line ("Test Value was ch1-left_2 CH1-left ::= 10");
        Put_Line ("========================================");
        totalErrors := totalErrors + 1;
    END IF;


    -- used to increase statement coverage
    DECLARE
        dummy:MOD1.RGBCOLORS;
    BEGIN
        dummy:=MOD1.RGBCOLORS_Init;
    END;

    DECLARE
        dummy:MOD1.CH1;
    BEGIN
        dummy:=MOD1.CH1_Init;
    END;

    DECLARE
        dummy:MOD1.CH1_left;
    BEGIN
        dummy:=MOD1.CH1_left_Init;
    END;


    IF totalErrors > 0 THEN
        Put_Line (Integer'Image(totalErrors) & " out of 7 failed."); 
        RETURN 1;
    ELSE
        Put_Line ("All test cases (7) run successfully."); 
        RETURN 0;
    END IF;
END MainProgram;