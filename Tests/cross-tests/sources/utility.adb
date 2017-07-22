with Ada.Text_IO;
with Ada.Text_IO.Text_Streams;
with Ada.Integer_Text_IO;
with Ada.Long_Long_Integer_Text_IO;
with Interfaces;
with adaasn1rtl; use adaasn1rtl;
with Interfaces.C; use Interfaces.C;

package body utility is

procedure usage is
begin
    Ada.Text_IO.Put_Line("Descriptive help");
end usage;

procedure do_encoding is
    stream : kappa.MyInt_ACN_Stream;
begin
    kappa.MyInt_ACN_Encode(kappa.kappa, stream);
    save_to_file(stream.Data);
    Ada.Long_Long_Integer_Text_IO.Put(Long_Long_Integer(kappa.kappa));
end do_encoding;

procedure do_decoding is
    stream : kappa.MyInt_ACN_Stream;
    value : kappa.MyInt := 5;
    result : adaasn1rtl.ASN1_RESULT;
begin
    read_from_file(stream.Data);
    stream.DataLen := kappa.MyInt_REQUIRED_BITS_FOR_ACN_ENCODING;
    kappa.MyInt_ACN_Decode(value, stream, result);
    if (result.Success /= True) then
        Ada.Text_IO.Put(Ada.Text_IO.Standard_Error, "Error was set. Error code: ");
        Ada.Integer_Text_IO.Put(Ada.Text_IO.Standard_Error, result.ErrorCode);
        Ada.Text_IO.New_Line(Ada.Text_IO.Standard_Error);
    else
        Ada.Long_Long_Integer_Text_IO.Put(Long_Long_Integer(value));
    end if;
end do_decoding;

procedure save_to_file(buffer : in kappa.MyInt_ACN_bit_array) is
    result : Interfaces.C.int;
    c_name : String(1..filename'length + 1);
begin
    c_name(1..filename'length) := filename;
    c_name(filename'length + 1) := Character'Val(0);
    result := write_memory(c_name, buffer);
    if (result /= 0) then
        Ada.Text_IO.Put_Line(Ada.Text_IO.Standard_Error, "Writing to file failed");
    end if;
end save_to_file;

procedure read_from_file(buffer : in out kappa.MyInt_ACN_bit_array) is
    result : Interfaces.C.int;
    c_name : String(1..filename'length + 1);
begin
    c_name(1..filename'length) := filename;
    c_name(filename'length + 1) := Character'Val(0);
    result := read_memory(c_name, buffer);
    if (result /= 0) then
        Ada.Text_IO.Put_Line(Ada.Text_IO.Standard_Error, "Reading from file failed");
    end if;
end read_from_file;

function get(buffer : in kappa.MyInt_ACN_bit_array; index : in Interfaces.C.Int) return Interfaces.C.int is
begin
    if (buffer(Integer(index+1)) = 1) then
        return Interfaces.C.int(1);
    else
        return Interfaces.C.int(0);
    end if;
end get;

procedure set(buffer : in out kappa.MyInt_ACN_bit_array; index : in Interfaces.C.Int; value : in Interfaces.C.int) is
begin
    buffer(Integer(index+1)) := adaasn1rtl.BIT(value);
end set;

end utility;
