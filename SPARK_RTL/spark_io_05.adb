-------------------------------------------------------------------------------
-- (C) Altran Praxis Limited
-------------------------------------------------------------------------------
--
-- The SPARK toolset is free software; you can redistribute it and/or modify it
-- under terms of the GNU General Public License as published by the Free
-- Software Foundation; either version 3, or (at your option) any later
-- version. The SPARK toolset is distributed in the hope that it will be
-- useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
-- Public License for more details. You should have received a copy of the GNU
-- General Public License distributed with the SPARK toolset; see file
-- COPYING3. If not, go to http://www.gnu.org/licenses for a complete copy of
-- the license.
--
--=============================================================================

with Text_IO;
with Unchecked_Deallocation;

package body SPARK_IO_05
is
   --# hide SPARK_IO_05;

   --  File Management

   type File_Descriptor is record
      File_Ref : Text_IO.File_Type;
   end record;

   File_System_Standard_Input  : aliased File_Descriptor :=
     File_Descriptor'(File_Ref => Text_IO.Standard_Input);
   File_System_Standard_Output : aliased File_Descriptor :=
     File_Descriptor'(File_Ref => Text_IO.Standard_Output);

   type File_System is record
      Standard_Input  : File_Type;
      Standard_Output : File_Type;
   end record;

   File_Sys : constant File_System :=
     File_System'(Standard_Input  => File_System_Standard_Input'Access,
                  Standard_Output => File_System_Standard_Output'Access);

   function Standard_Input return File_Type
   is
   begin
      return File_Sys.Standard_Input;
   end Standard_Input;

   function Standard_Output return File_Type
   is
   begin
      return File_Sys.Standard_Output;
   end Standard_Output;

   procedure Dispose is new Unchecked_Deallocation
     (File_Descriptor, File_Type);

   procedure Create (File         :    out File_Type;
                     Name_Of_File : in     String;
                     Form_Of_File : in     String;
                     Status       :    out File_Status)
   is
   begin
      Create_Flex (File         => File,
                   Name_Length  => Name_Of_File'Length,
                   Name_Of_File => Name_Of_File,
                   Form_Of_File => Form_Of_File,
                   Status       => Status);
   end Create;

   procedure Create_Flex (File         :    out File_Type;
                          Name_Length  : in     Natural;
                          Name_Of_File : in     String;
                          Form_Of_File : in     String;
                          Status       :    out File_Status)
   is
   begin
      File := new File_Descriptor;
      Text_IO.Create (File.File_Ref,
                      Text_IO.Out_File,
                      Name_Of_File (Name_Of_File'First .. Name_Length),
                      Form_Of_File);
      Status := Ok;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
         Dispose (File);
      when Text_IO.Name_Error =>
         Status := Name_Error;
         Dispose (File);
      when Text_IO.Use_Error =>
         Status := Use_Error;
         Dispose (File);
      when Text_IO.Device_Error =>
         Status := Device_Error;
         Dispose (File);
      when Standard.Storage_Error =>
         Status := Storage_Error;
         Dispose (File);
      when Standard.Program_Error =>
         Status := Program_Error;
         Dispose (File);
   end Create_Flex;

   procedure Open (File         :    out File_Type;
                   Mode_Of_File : in     File_Mode;
                   Name_Of_File : in     String;
                   Form_Of_File : in     String;
                   Status       :    out File_Status)
   is
   begin
      Open_Flex (File         => File,
                 Mode_Of_File => Mode_Of_File,
                 Name_Length  => Name_Of_File'Length,
                 Name_Of_File => Name_Of_File,
                 Form_Of_File => Form_Of_File,
                 Status       => Status);
   end Open;

   procedure Open_Flex (File         :    out File_Type;
                        Mode_Of_File : in     File_Mode;
                        Name_Length  : in     Natural;
                        Name_Of_File : in     String;
                        Form_Of_File : in     String;
                        Status       :    out File_Status)
   is
      F_Mode : Text_IO.File_Mode;
   begin
      File := new File_Descriptor;
      case Mode_Of_File is
         when In_File     => F_Mode := Text_IO.In_File;
         when Out_File    => F_Mode := Text_IO.Out_File;
         when Append_File => F_Mode := Text_IO.Append_File;
      end case;
      Text_IO.Open (File.File_Ref,
                    F_Mode,
                    Name_Of_File (Name_Of_File'First .. Name_Length),
                    Form_Of_File);
      Status := Ok;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
         Dispose (File);
      when Text_IO.Name_Error =>
         Status := Name_Error;
         Dispose (File);
      when Text_IO.Use_Error =>
         Status := Use_Error;
         Dispose (File);
      when Text_IO.Device_Error =>
         Status := Device_Error;
         Dispose (File);
      when Standard.Storage_Error =>
         Status := Storage_Error;
         Dispose (File);
      when Standard.Program_Error =>
         Status := Program_Error;
         Dispose (File);
   end Open_Flex;

   procedure Close (File   : in out File_Type;
                    Status :    out File_Status)
   is
   begin
      if File = null then
         Status := Status_Error;
      else
         Text_IO.Close (File.File_Ref);
         Dispose (File);
         Status := Ok;
      end if;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
         Dispose (File);
      when Text_IO.Device_Error =>
         Status := Device_Error;
         Dispose (File);
      when Constraint_Error =>
         Status := Use_Error;
         Dispose (File);
      when Standard.Storage_Error =>
         Status := Storage_Error;
         Dispose (File);
      when Standard.Program_Error =>
         Status := Program_Error;
         Dispose (File);
   end Close;

   procedure Delete (File   : in out File_Type;
                     Status :    out File_Status)
   is
   begin
      if File = null then
         Status := Status_Error;
      else
         Text_IO.Delete (File.File_Ref);
         Dispose (File);
         Status := Ok;
      end if;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
         Dispose (File);
      when Text_IO.Use_Error =>
         Status := Use_Error;
         Dispose (File);
      when Text_IO.Device_Error =>
         Status := Device_Error;
         Dispose (File);
      when Constraint_Error =>
         Status := Use_Error;
         Dispose (File);
      when Standard.Storage_Error =>
         Status := Storage_Error;
         Dispose (File);
      when Standard.Program_Error =>
         Status := Program_Error;
         Dispose (File);
   end Delete;

   procedure Reset (File         : in out File_Type;
                    Mode_Of_File : in     File_Mode;
                    Status       :    out File_Status)
   is
      F_Mode : Text_IO.File_Mode;
   begin
      if File = null then
         Status := Status_Error;
      else
         case Mode_Of_File is
            when In_File     => F_Mode := Text_IO.In_File;
            when Out_File    => F_Mode := Text_IO.Out_File;
            when Append_File => F_Mode := Text_IO.Append_File;
         end case;
         Text_IO.Reset (File.File_Ref,
                        F_Mode);
         Status := Ok;
      end if;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
         Dispose (File);
      when Text_IO.Use_Error =>
         Status := Use_Error;
         Dispose (File);
      when Text_IO.Device_Error =>
         Status := Device_Error;
         Dispose (File);
      when Standard.Storage_Error =>
         Status := Storage_Error;
         Dispose (File);
      when Standard.Program_Error =>
         Status := Program_Error;
         Dispose (File);
   end Reset;

   function Valid_File (File : File_Type) return Boolean
   is
   begin
      return File /= null;
   end Valid_File;

   function Is_Open (File : File_Type) return Boolean
   is
   begin
      return Valid_File (File) and then
        Text_IO.Is_Open (File.File_Ref);
   end Is_Open;

   function Mode (File : File_Type) return File_Mode
   is
      F_Mode : File_Mode;
   begin
      if Is_Open (File) and then
        Text_IO.Is_Open (File.File_Ref) then
         case Text_IO.Mode (File.File_Ref) is
            when Text_IO.In_File =>
               F_Mode := In_File;
            when Text_IO.Out_File =>
               F_Mode := Out_File;
            when Text_IO.Append_File =>
               F_Mode := Append_File;
         end case;
      else
         F_Mode := In_File;
      end if;
      return F_Mode;
   end Mode;

   function Is_In (File : File_Type) return Boolean;

   function Is_In (File : File_Type) return Boolean
   is
   begin
      return Is_Open (File) and then Mode (File) = In_File;
   end Is_In;

   function Is_Out (File : File_Type) return Boolean;

   function Is_Out (File : File_Type) return Boolean
   is
   begin
      return Is_Open (File) and then (Mode (File) = Out_File or
                                        Mode (File) = Append_File);
   end Is_Out;

   procedure Name (File         : in     File_Type;
                   Name_Of_File :    out String;
                   Stop         :    out Natural)
   is
   begin
      if Is_Open (File) then
         declare
            FN : constant String := Text_IO.Name (File.File_Ref);
         begin
            if Name_Of_File'Length >= FN'Length then
               Name_Of_File (FN'Range) := FN;
               Stop := FN'Length;
            else
               Name_Of_File := FN (Name_Of_File'Range);
               Stop := Name_Of_File'Length;
            end if;
         end;
      else
         Stop := Name_Of_File'First - 1;
      end if;
   exception
      when others => Stop := Name_Of_File'First - 1;
   end Name;

   procedure Form (File         : in     File_Type;
                   Form_Of_File :    out String;
                   Stop         :    out Natural)
   is
   begin
      if Is_Open (File) then
         declare
            FM : constant String := Text_IO.Form (File.File_Ref);
         begin
            if Form_Of_File'Length >= FM'Length then
               Form_Of_File (FM'Range) := FM;
               Stop := FM'Length;
            else
               Form_Of_File := FM (Form_Of_File'Range);
               Stop := Form_Of_File'Length;
            end if;
         end;
      else
         Stop := Form_Of_File'First - 1;
      end if;
   exception
      when others => Stop := Form_Of_File'First - 1;
   end Form;

   --  Line and file terminator control

   function P_To_PC (P : Positive) return Text_IO.Positive_Count;

   function P_To_PC (P : Positive) return Text_IO.Positive_Count
   is
   begin
      return Text_IO.Positive_Count (P);
   end P_To_PC;

   function PC_To_P (PC : Text_IO.Positive_Count) return Positive;

   function PC_To_P (PC : Text_IO.Positive_Count) return Positive
   is
   begin
      return Positive (PC);
   end PC_To_P;

   procedure New_Line (File    : in File_Type;
                       Spacing : in Positive)
   is
      Gap : Text_IO.Positive_Count;
   begin
      if Is_Out (File) then
         Gap := P_To_PC (Spacing);
         Text_IO.New_Line (File.File_Ref, Gap);
      end if;
   exception
      when others => null;
   end New_Line;

   procedure Skip_Line (File    : in File_Type;
                        Spacing : in Positive)
   is
      Gap : Text_IO.Positive_Count;
   begin
      if Is_In (File) then
         Gap := P_To_PC (Spacing);
         Text_IO.Skip_Line (File.File_Ref, Gap);
      end if;
   exception
      when others => null;
   end Skip_Line;

   procedure New_Page (File : in File_Type)
   is
   begin
      if Is_Out (File) then
         Text_IO.New_Page (File.File_Ref);
      end if;
   exception
      when others => null;
   end New_Page;

   function End_Of_Line (File : File_Type) return Boolean
   is
      EOLN : Boolean;
   begin
      if Is_In (File) then
         EOLN := Text_IO.End_Of_Line (File.File_Ref);
      else
         EOLN := False;
      end if;
      return EOLN;
   end End_Of_Line;

   function End_Of_File (File : File_Type) return Boolean
   is
      EOF : Boolean;
   begin
      if Is_In (File) then
         EOF := Text_IO.End_Of_File (File.File_Ref);
      else
         EOF := True;
      end if;
      return EOF;
   end End_Of_File;

   procedure Set_Col (File : in File_Type;
                      Posn : in Positive);

   procedure Set_Col (File : in File_Type;
                      Posn : in Positive)
   is
      Col : Text_IO.Positive_Count;
   begin
      if Is_Open (File) then
         Col := P_To_PC (Posn);
         Text_IO.Set_Col (File.File_Ref, Col);
      end if;
   exception
      when others => null;
   end Set_Col;

   procedure Set_In_File_Col (File : in File_Type;
                              Posn : in Positive)
   is
   begin
      if Is_In (File) then
         Set_Col (File, Posn);
      end if;
   end Set_In_File_Col;

   procedure Set_Out_File_Col (File : in File_Type;
                               Posn : in Positive)
   is
   begin
      if Is_Out (File) then
         Set_Col (File, Posn);
      end if;
   end Set_Out_File_Col;

   function Col (File : File_Type) return Positive;

   function Col (File : File_Type) return Positive
   is
      Posn : Positive;
      Col  : Text_IO.Positive_Count;
   begin
      if Is_Open (File) then
         Col := Text_IO.Col (File.File_Ref);
         Posn := PC_To_P (Col);
      else
         Posn := 1;
      end if;
      return Posn;
   exception
      when Text_IO.Status_Error => return 1;
      when Text_IO.Layout_Error => return PC_To_P (Text_IO.Count'Last);
      when Text_IO.Device_Error => return 1;
      when Standard.Storage_Error => return 1;
      when Standard.Program_Error => return 1;
   end Col;

   function In_File_Col (File : File_Type) return Positive
   is
   begin
      if Is_In (File) then
         return Col (File);
      else
         return 1;
      end if;
   end In_File_Col;

   function Out_File_Col (File : File_Type) return Positive
   is
   begin
      if Is_Out (File) then
         return Col (File);
      else
         return 1;
      end if;
   end Out_File_Col;

   function Line (File : File_Type) return Positive;

   function Line (File : File_Type) return Positive
   is
      Posn : Positive;
      Line  : Text_IO.Positive_Count;
   begin
      if Is_Open (File) then
         Line := Text_IO.Line (File.File_Ref);
         Posn := PC_To_P (Line);
      else
         Posn := 1;
      end if;
      return Posn;
   exception
      when Text_IO.Status_Error => return 1;
      when Text_IO.Layout_Error => return PC_To_P (Text_IO.Count'Last);
      when Text_IO.Device_Error => return 1;
      when Standard.Storage_Error => return 1;
      when Standard.Program_Error => return 1;
   end Line;

   function In_File_Line (File : File_Type) return Positive
   is
   begin
      if Is_In (File) then
         return Line (File);
      else
         return 1;
      end if;
   end In_File_Line;

   function Out_File_Line (File : File_Type) return Positive
   is
   begin
      if Is_Out (File) then
         return Line (File);
      else
         return 1;
      end if;
   end Out_File_Line;

   --  Character IO

   procedure Get_Char (File : in     File_Type;
                       Item :    out Character)
   is
   begin
      if Is_In (File) then
         Text_IO.Get (File.File_Ref, Item);
      else
         Item := Character'First;
      end if;
   exception
      when others => null;
   end Get_Char;

   procedure Put_Char (File : in File_Type;
                       Item : in Character)
   is
   begin
      if Is_Out (File) then
         Text_IO.Put (File.File_Ref, Item);
      end if;
   exception
      when others => null;
   end Put_Char;

   procedure Get_Char_Immediate (File   : in     File_Type;
                                 Item   :    out Character;
                                 Status :    out File_Status)
   is
   begin
      if Is_In (File) then
         Text_IO.Get_Immediate (File.File_Ref, Item);
         Status := Ok;
      else
         Item := Character'First;
         Status := Mode_Error;
      end if;
   exception
      when others =>
         Item := Character'First;
         Status := End_Error;
   end Get_Char_Immediate;

   --  String IO

   procedure Get_String (File : in     File_Type;
                         Item :    out String;
                         Stop :    out Natural)
   is
      LSTP : Natural;
   begin
      if Is_In (File) then
         LSTP := Item'First - 1;
         loop
            exit when End_Of_File (File);
            LSTP := LSTP + 1;
            Get_Char (File, Item (LSTP));
            exit when LSTP = Item'Last;
         end loop;
         Stop := LSTP;
      else
         Stop := Item'First - 1;
      end if;
   end Get_String;

   --  CFR 718 The behaviour of Put_String is now as follows:
   --  If Stop is 0 then all characters in Item are output.
   --  If Stop <= Item'Last then output Item(Item'First .. Stop).
   --  If Stop > Item'Last then output all characters in Item, then pad with
   --  spaces to width specified by Stop.
   procedure Put_String (File : in File_Type;
                         Item : in String;
                         Stop : in Natural)
   is
      Pad : Natural;
   begin
      if Is_Out (File) then
         if Stop = 0 then
            Text_IO.Put (File.File_Ref, Item);
         elsif Stop <= Item'Last then
            Text_IO.Put (File.File_Ref, Item (Item'First .. Stop));
         else
            Pad := Stop - Item'Last;
            Text_IO.Put (File.File_Ref, Item);
            while Pad > 0 loop
               Text_IO.Put (File.File_Ref, ' ');
               Pad := Pad - 1;
            end loop;
         end if;
      end if;
   exception
      when others => null;
   end Put_String;

   procedure Get_Line (File : in     File_Type;
                       Item :    out String;
                       Stop :    out Natural)
   is
   begin
      if Is_In (File) then
         Text_IO.Get_Line (File.File_Ref, Item, Stop);
      else
         Stop := Item'First - 1;
      end if;
   exception
      when others => Stop := Item'First - 1;
   end Get_Line;

   procedure Put_Line (File : in File_Type;
                       Item : in String;
                       Stop : in Natural)
   is
      ES : Positive;
   begin
      if Stop = 0 then
         ES := Item'Last;
      else
         ES := Stop;
      end if;
      if Is_Out (File) then
         Text_IO.Put_Line (File.File_Ref, Item (Item'First .. ES));
      end if;
   exception
      when others => null;
   end Put_Line;


   --  Integer IO

   package Integer_IO is new Text_IO.Integer_IO (Integer);

   procedure Get_Integer (File  : in     File_Type;
                          Item  :    out Integer;
                          Width : in     Natural;
                          Read  :    out Boolean)
   is
   begin
      if Is_In (File) then
         Integer_IO.Get (File.File_Ref, Item, Width);
         Read := True;
      else
         Read := False;
      end if;
   exception
      when others => Read := False;
   end Get_Integer;

   procedure Put_Integer (File  : in File_Type;
                          Item  : in Integer;
                          Width : in Natural;
                          Base  : in Number_Base)
   is
   begin
      if Is_Out (File) then
         Integer_IO.Put (File.File_Ref, Item, Width, Base);
      end if;
   exception
      when others => null;
   end Put_Integer;

   procedure Get_Int_From_String (Source    : in     String;
                                  Item      :    out Integer;
                                  Start_Pos : in     Positive;
                                  Stop      :    out Natural)
   is
   begin
      Integer_IO.Get (Source (Start_Pos .. Source'Last), Item, Stop);
   exception
      when others => Stop := Start_Pos - 1;
   end Get_Int_From_String;

   procedure Put_Int_To_String (Dest      : in out String;
                                Item      : in     Integer;
                                Start_Pos : in     Positive;
                                Base      : in     Number_Base)
   is
   begin
      Integer_IO.Put (Dest (Start_Pos .. Dest'Last), Item, Base);
   exception
      when others => null;
   end Put_Int_To_String;


   --  Float IO

   package Real_IO is new Text_IO.Float_IO (Float);

   procedure Get_Float (File  : in     File_Type;
                        Item  :    out Float;
                        Width : in     Natural;
                        Read  :    out Boolean)
   is
   begin
      if Is_In (File) then
         Real_IO.Get (File.File_Ref, Item, Width);
         Read := True;
      else
         Read := False;
      end if;
   exception
      when others => Read := False;
   end Get_Float;

   procedure Put_Float (File : in File_Type;
                        Item : in Float;
                        Fore : in Natural;
                        Aft  : in Natural;
                        Exp  : in Natural)
   is
   begin
      if Is_Out (File) then
         Real_IO.Put (File.File_Ref, Item, Fore, Aft, Exp);
      end if;
   exception
      when others => null;
   end Put_Float;

   procedure Get_Float_From_String (Source    : in     String;
                                    Item      :    out Float;
                                    Start_Pos : in     Positive;
                                    Stop      :    out Natural)
   is
   begin
      Real_IO.Get (Source (Start_Pos .. Source'Last), Item, Stop);
   exception
      when others => Stop := Start_Pos - 1;
   end Get_Float_From_String;

   procedure Put_Float_To_String (Dest      : in out String;
                                  Item      : in     Float;
                                  Start_Pos : in     Positive;
                                  Aft       : in     Natural;
                                  Exp       : in     Natural)
   is
   begin
      Real_IO.Put (Dest (Start_Pos .. Dest'Last), Item, Aft, Exp);
   exception
      when others => null;
   end Put_Float_To_String;



end SPARK_IO_05;
