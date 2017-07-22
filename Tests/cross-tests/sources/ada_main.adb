with Ada.Text_IO;
with Ada.Integer_Text_IO;
with Ada.Command_Line;
with utility;
with Ada.Long_Long_Integer_Text_IO;
with Interfaces;

procedure ada_main is
begin
    if (Ada.Command_Line.Argument_Count /= 1) then
        utility.usage;
        return;
    end if;

    if (Ada.Command_Line.Argument(1) = "encode") then
        utility.do_encoding;
    elsif (Ada.Command_Line.Argument(1) = "decode") then
        utility.do_decoding;
    else
        Ada.Text_IO.Put_Line(Ada.Text_IO.Standard_Error, "Unrecognized option: "
            & Ada.Command_Line.Argument(1));
        utility.usage;
    end if;
end ada_main;

