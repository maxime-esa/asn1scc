with kappa;
with Interfaces;
with Interfaces.C;

package utility is

procedure usage;
procedure do_encoding;
procedure do_decoding;
procedure save_to_file(buffer : in kappa.MyInt_ACN_bit_array);
procedure read_from_file(buffer : in out kappa.MyInt_ACN_bit_array);

function get(buffer : in kappa.MyInt_ACN_bit_array; index : in Interfaces.C.Int) return Interfaces.C.int;
procedure set(buffer : in out kappa.MyInt_ACN_bit_array; index : in Interfaces.C.Int; value : in Interfaces.C.int);
function write_memory(filename : in String; buffer : in kappa.MyInt_ACN_bit_array) return Interfaces.C.int;
function read_memory(filename : in String; buffer : in out kappa.MyInt_ACN_bit_array) return Interfaces.C.int;

pragma Export(C, get, "get");
pragma Export(C, set, "set");
pragma Import(C, write_memory, "write_memory");
pragma Import(C, read_memory, "read_memory");

private
    filename : constant String := "buffer";

end utility;
