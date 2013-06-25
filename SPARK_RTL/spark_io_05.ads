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

-------------------------------------------------------------------------------
--                                                                           --
-- SPARK_IO                                                                  --
--                                                                           --
-- Description                                                               --
--   This is a thick binding to package Ada.Text_IO                          --
--                                                                           --
-- Language                                                                  --
--   Specification : SPARK                                                   --
--   Private Part  : Ada 2005                                                --
--   Body          : Ada 2005                                                --
--                                                                           --
-- Runtime Requirements and Dependencies                                     --
--   Full Ada Runtime                                                        --
--                                                                           --
-- Verification                                                              --
--   N/A                                                                     --
--                                                                           --
-- Exceptions                                                                --
--   None                                                                    --
--                                                                           --
-------------------------------------------------------------------------------

package SPARK_IO_05
--# own State   : State_Type;
--#     Inputs  : Inputs_Type;
--#     Outputs : Outputs_Type;
--# initializes State,
--#             Inputs,
--#             Outputs;
is
   --# type State_Type is abstract;
   --# type Inputs_Type is abstract;
   --# type Outputs_Type is abstract;

   type File_Type is private;
   type File_Mode is (In_File, Out_File, Append_File);
   type File_Status is (Ok, Status_Error, Mode_Error, Name_Error, Use_Error,
                        Device_Error, End_Error,  Data_Error, Layout_Error,
                        Storage_Error, Program_Error);

   subtype Number_Base is Integer range 2 .. 16;

   function Standard_Input return File_Type;
   --# global in Inputs;
   function Standard_Output return File_Type;
   --# global in Outputs;
   Null_File : constant File_Type;

   ---------------------
   -- File Management --
   ---------------------

   procedure Create (File         :    out File_Type;
                     Name_Of_File : in     String;
                     Form_Of_File : in     String;
                     Status       :    out File_Status);
   --# global in out State;
   --# derives File,
   --#         State,
   --#         Status from Form_Of_File,
   --#                     Name_Of_File,
   --#                     State;
   --# declare delay;

   procedure Create_Flex (File         :    out File_Type;
                          Name_Length  : in     Natural;
                          Name_Of_File : in     String;
                          Form_Of_File : in     String;
                          Status       :    out File_Status);
   --# global in out State;
   --# derives File,
   --#         State,
   --#         Status from Form_Of_File,
   --#                     Name_Length,
   --#                     Name_Of_File,
   --#                     State;
   --# declare delay;

   procedure Open (File         :    out File_Type;
                   Mode_Of_File : in     File_Mode;
                   Name_Of_File : in     String;
                   Form_Of_File : in     String;
                   Status       :    out File_Status);
   --# global in out State;
   --# derives File,
   --#         State,
   --#         Status from Form_Of_File,
   --#                     Mode_Of_File,
   --#                     Name_Of_File,
   --#                     State;
   --# declare delay;

   procedure Open_Flex (File         :    out File_Type;
                        Mode_Of_File : in     File_Mode;
                        Name_Length  : in     Natural;
                        Name_Of_File : in     String;
                        Form_Of_File : in     String;
                        Status       :    out File_Status);
   --# global in out State;
   --# derives File,
   --#         State,
   --#         Status from Form_Of_File,
   --#                     Mode_Of_File,
   --#                     Name_Length,
   --#                     Name_Of_File,
   --#                     State;
   --# declare delay;

   procedure Close (File   : in out File_Type;
                    Status :    out File_Status);
   --# global in out State;
   --# derives State,
   --#         Status from File,
   --#                     State &
   --#         File   from ;
   --# declare delay;

   procedure Delete (File   : in out File_Type;
                     Status :    out File_Status);
   --# global in out State;
   --# derives State,
   --#         Status from File,
   --#                     State &
   --#         File   from ;
   --# declare delay;

   procedure Reset (File         : in out File_Type;
                    Mode_Of_File : in     File_Mode;
                    Status       :    out File_Status);
   --# derives File,
   --#         Status from File,
   --#                     Mode_Of_File;
   --# declare delay;

   function Valid_File (File : File_Type) return Boolean;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   function Mode (File : File_Type) return File_Mode;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   procedure Name (File         : in     File_Type;
                   Name_Of_File :    out String;
                   Stop         :    out Natural);
   --# derives Name_Of_File,
   --#         Stop         from File;
   --# declare delay;

   procedure Form (File         : in     File_Type;
                   Form_Of_File :    out String;
                   Stop         :    out Natural);
   --# derives Form_Of_File,
   --#         Stop             from File;
   --# declare delay;

   function Is_Open (File : File_Type) return Boolean;
   --# global State;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   -----------------------------------------------
   -- Control of default input and output files --
   -----------------------------------------------

   --
   --  Not supported in SPARK_IO
   --

   --------------------------------------------
   -- Specification of line and page lengths --
   --------------------------------------------

   --
   --  Not supported in SPARK_IO
   --

   -----------------------------------
   -- Column, Line and Page Control --
   -----------------------------------

   procedure New_Line (File    : in File_Type;
                       Spacing : in Positive);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Spacing;
   --# declare delay;

   procedure Skip_Line (File    : in File_Type;
                        Spacing : in Positive);
   --# global in out Inputs;
   --# derives Inputs from *,
   --#                     File,
   --#                     Spacing;
   --# declare delay;

   procedure New_Page (File : in File_Type);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File;
   --# declare delay;

   function End_Of_Line (File : File_Type) return Boolean;
   --# global Inputs;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   function End_Of_File (File : File_Type) return Boolean;
   --# global Inputs;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   procedure Set_In_File_Col (File : in File_Type;
                              Posn : in Positive);
   --# global in out Inputs;
   --# derives Inputs from *,
   --#                     File,
   --#                     Posn;
   --# declare delay;
   --# pre Mode (File) = In_File;

   procedure Set_Out_File_Col (File : in File_Type;
                               Posn : in Positive);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Posn;
   --# declare delay;
   --# pre Mode( File ) = Out_File or
   --#     Mode (File) = Append_File;

   function In_File_Col (File : File_Type) return Positive;
   --# global Inputs;
   --# pre Mode (File) = In_File;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   function Out_File_Col (File : File_Type) return Positive;
   --# global Outputs;
   --# pre Mode (File) = Out_File or
   --#     Mode (File) = Append_File;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   function In_File_Line (File : File_Type) return Positive;
   --# global Inputs;
   --# pre Mode (File) = In_File;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   function Out_File_Line (File : File_Type) return Positive;
   --# global Outputs;
   --# pre Mode (File) = Out_File or
   --#     Mode (File) = Append_File;
   --  This is a potentially blocking function.
   --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

   ----------------------------
   -- Character Input-Output --
   ----------------------------

   procedure Get_Char (File : in     File_Type;
                       Item :    out Character);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item   from File,
   --#                     Inputs;
   --# declare delay;

   procedure Put_Char (File : in File_Type;
                       Item : in Character);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Item;
   --# declare delay;

   procedure Get_Char_Immediate (File   : in     File_Type;
                                 Item   :    out Character;
                                 Status :    out File_Status);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item,
   --#         Status from File,
   --#                     Inputs;
   --# declare delay;
   --  NOTE.  Only the variant of Get_Immediate that waits for a character to
   --  become available is supported.
   --  On return Status is one of Ok, Mode_Error or End_Error. See ALRM A.10.7
   --  Item is Character'First if Status /= Ok

   -------------------------
   -- String Input-Output --
   -------------------------

   procedure Get_String (File : in     File_Type;
                         Item :    out String;
                         Stop :    out Natural);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item,
   --#         Stop   from File,
   --#                     Inputs;
   --# declare delay;

   procedure Put_String (File : in File_Type;
                         Item : in String;
                         Stop : in Natural);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Item,
   --#                      Stop;
   --# declare delay;

   procedure Get_Line (File : in     File_Type;
                       Item :    out String;
                       Stop :    out Natural);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item,
   --#         Stop   from File,
   --#                     Inputs;
   --# declare delay;

   procedure Put_Line (File : in File_Type;
                       Item : in String;
                       Stop : in Natural);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Item,
   --#                      Stop;
   --# declare delay;


   --------------------------
   -- Integer Input-Output --
   --------------------------

   --  SPARK_IO only supports input-output of
   --  the built-in integer type Integer

   procedure Get_Integer (File  : in     File_Type;
                          Item  :    out Integer;
                          Width : in     Natural;
                          Read  :    out Boolean);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item,
   --#         Read   from File,
   --#                     Inputs,
   --#                     Width;
   --# declare delay;

   procedure Put_Integer (File  : in File_Type;
                          Item  : in Integer;
                          Width : in Natural;
                          Base  : in Number_Base);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      Base,
   --#                      File,
   --#                      Item,
   --#                      Width;
   --# declare delay;

   procedure Get_Int_From_String (Source    : in     String;
                                  Item      :    out Integer;
                                  Start_Pos : in     Positive;
                                  Stop      :    out Natural);
   --# derives Item,
   --#         Stop from Source,
   --#                   Start_Pos;
   --# declare delay;

   procedure Put_Int_To_String (Dest      : in out String;
                                Item      : in     Integer;
                                Start_Pos : in     Positive;
                                Base      : in     Number_Base);
   --# derives Dest from *,
   --#                   Base,
   --#                   Item,
   --#                   Start_Pos;
   --# declare delay;

   ------------------------
   -- Float Input-Output --
   ------------------------

   --  SPARK_IO only supports input-output of
   --  the built-in real type Float

   procedure Get_Float (File  : in     File_Type;
                        Item  :    out Float;
                        Width : in     Natural;
                        Read  :    out Boolean);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item,
   --#         Read   from File,
   --#                     Inputs,
   --#                     Width;
   --# declare delay;

   procedure Put_Float (File : in File_Type;
                        Item : in Float;
                        Fore : in Natural;
                        Aft  : in Natural;
                        Exp  : in Natural);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      Aft,
   --#                      Exp,
   --#                      File,
   --#                      Fore,
   --#                      Item;
   --# declare delay;

   procedure Get_Float_From_String (Source    : in     String;
                                    Item      :    out Float;
                                    Start_Pos : in     Positive;
                                    Stop      :    out Natural);
   --# derives Item,
   --#         Stop from Source,
   --#                   Start_Pos;
   --# declare delay;

   procedure Put_Float_To_String (Dest      : in out String;
                                  Item      : in     Float;
                                  Start_Pos : in     Positive;
                                  Aft       : in     Natural;
                                  Exp       : in     Natural);
   --# derives Dest from *,
   --#                   Aft,
   --#                   Exp,
   --#                   Item,
   --#                   Start_Pos;
   --# declare delay;




private
   --# hide SPARK_IO_05;

   type File_Descriptor;
   type File_Type is access all File_Descriptor;

   Null_File : constant File_Type := null;

end SPARK_IO_05;
