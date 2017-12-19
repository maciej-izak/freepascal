{
    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2000 by Michael Van Canneyt
    member of the Free Pascal development team

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

{ Run-Time type information routines }

type
  PArrayInfo=^TArrayInfo;
  TArrayInfo=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Size: SizeInt;
    ElCount: SizeInt;
{$ifdef VER3_0}
    ElInfo: Pointer;
{$else}
    ElInfo: PPointer;
{$endif}
    DimCount: Byte;
    Dims:array[0..255] of Pointer;
  end;

function RTTIArraySize(typeInfo: Pointer): SizeInt;
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
  {$ifdef VER2_6}
  result:=PArrayInfo(typeInfo)^.Size*PArrayInfo(typeInfo)^.ElCount;
  {$else}
  result:=PArrayInfo(typeInfo)^.Size;
  {$endif}
end;

function RTTIRecordSize(typeInfo: Pointer): SizeInt;
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
  { for size field init table is compatible with rtti table }
  result:=PRecordInfoFull(typeInfo)^.Size;
end;

{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
function RTTIRecordOp(typeInfo: Pointer; var initrtti: Pointer): PRecordInfoInit; inline;
begin
  { find init table and management operators }
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
  result:=typeInfo;

  { check terminator, maybe we are already in init table }
  if Assigned(result^.Terminator) then
  begin
    { point to more optimal initrtti }
    initrtti:=PRecordInfoFull(result)^.InitTable;
    { and point to management operators in our init table }
    result:=aligntoqword(initrtti+2+PByte(initrtti)[1]);
  end
end;
{$endif FPC_HAS_MANAGEMENT_OPERATORS}

function RTTIRecordRttiInfoToInitInfo(typeInfo: Pointer): Pointer; inline;
begin
  result:=typeInfo;
{$ifndef VER3_0}
  { find init table }
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);

  { check terminator, maybe we are already in init table }
  if Assigned(PRecordInfoInit(typeInfo)^.Terminator) then
    { point to more optimal initrtti }
    result:=PRecordInfoFull(typeInfo)^.InitTable;
{$endif VER3_0}
end;

{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
function RTTISizeAndOp(typeInfo: Pointer;
  const expectedManagementOp: TRTTIRecOpType; out hasManagementOp: boolean): SizeInt;
begin
  hasManagementOp:=false;
{$else FPC_HAS_MANAGEMENT_OPERATORS}
function RTTISize(typeInfo: Pointer): SizeInt;
begin
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
  case PTypeKind(typeinfo)^ of
    tkAString,tkWString,tkUString,
    tkInterface,tkDynarray:
      result:=sizeof(Pointer);
{$ifdef FPC_HAS_FEATURE_VARIANTS}
    tkVariant:
      result:=sizeof(TVarData);
{$endif FPC_HAS_FEATURE_VARIANTS}
    tkArray:
      result:=RTTIArraySize(typeinfo);
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    tkObject:
      result:=RTTIRecordSize(typeinfo);
    tkRecord:
      with RTTIRecordOp(typeInfo,typeInfo)^ do
        begin
          result:=Size;
          hasManagementOp := Assigned(RecordOp);
          if hasManagementOp then
            case expectedManagementOp of
              rotInitialize: hasManagementOp:=Assigned(RecordOp^.Initialize);
              rotFinalize: hasManagementOp:=Assigned(RecordOp^.Finalize);
              rotAddRef: hasManagementOp:=Assigned(RecordOp^.AddRef);
              rotCopy: hasManagementOp:=Assigned(RecordOp^.Copy);
            end;
        end;
{$else FPC_HAS_MANAGEMENT_OPERATORS}
    tkObject,tkRecord:
      result:=RTTIRecordSize(typeinfo);
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
  else
    result:=-1;
  end;
end;

{ if you modify this procedure, fpc_copy must be probably modified as well }

procedure fpc_Initialize_Record(Data,TypeInfo:Pointer);[Public,Alias : 'FPC_INITIALIZE_RECORD'];  compilerproc;
var
  i: longint;
{$ifndef VER3_0}
  item : PFastRTTIItem;
  offset: PSizeInt absolute item;
{$endif}
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
{$ifndef VER3_0}
  if Assigned(PRecordInfoInit(typeInfo)^.FastRTTI)and assigned(PRecordInfoInit(typeInfo)^.FastRTTI^.InitializationRTTI) then
    with PRecordInfoInit(typeInfo)^.FastRTTI^,PRecordInfoInit(typeInfo)^.FastRTTI^.InitializationRTTI^ do
    begin
      item:=aligntoqword(Pointer(InitializationRTTI)+1);

      if friPointer in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          PPchar(Data+offset^)^:=Nil;
          inc(offset);
        end;
      end;
      if friVariant in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          variant_init(PVarData(Data+offset^)^);
          inc(offset);
        end;
      end;
      InitializeOpCall(Data, TypeInfo);
    end
  else
{$endif VER3_0}
    with PRecordInfoInit(typeInfo)^ do
    begin
      Inc(PRecordInfoInit(typeInfo));
      { Process elements }
      for i:=1 to count Do
        begin
          fpc_Initialize(Data+PRecordElement(typeInfo)^.Offset,PRecordElement(typeInfo)^.TypeInfo{$ifndef VER3_0}^{$endif});
          Inc(PRecordElement(typeInfo));
        end;
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
      if Assigned(recordop) and Assigned(recordop^.Initialize) then
        recordop^.Initialize(data);
{$endif}
    end;
end;


procedure fpc_Finalize_Record(Data,TypeInfo:Pointer);[Public,Alias : 'FPC_FINALIZE_RECORD'];  compilerproc;
var
  i : longint;
{$ifndef VER3_0}
  item : PFastRTTIItem;
  offset: PSizeInt absolute item;
  field: PRecordElement absolute item;
{$endif}
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
{$ifndef VER3_0}
  if Assigned(PRecordInfoInit(typeInfo)^.FastRTTI) and assigned(PRecordInfoInit(typeInfo)^.FastRTTI^.GeneralRTTI) then
    with PRecordInfoInit(typeInfo)^.FastRTTI^,PRecordInfoInit(typeInfo)^.FastRTTI^.GeneralRTTI^ do
    begin
      FinalizeOpCall(Data, TypeInfo);
      item:=aligntoqword(Pointer(GeneralRTTI)+1);
      if frgAString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_AnsiStr_Decr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
  {$ifndef FPC_WIDESTRING_EQUAL_UNICODESTRING}
      if frgWString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_WideStr_Decr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
  {$endif FPC_WIDESTRING_EQUAL_UNICODESTRING}
      if frgUString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_UnicodeStr_Decr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
      if frgInterface in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          Intf_Decr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
      if frgVariant in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          variant_clear(PVarData(Data+offset^)^);
          inc(offset);
        end;
      end;
      if frgDynarray in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_dynarray_clear(PPointer(Data+field^.offset)^,field^.TypeInfo^);
          inc(field);
        end;
      end;
    end
  else
{$endif VER3_0}
    with PRecordInfoInit(typeInfo)^ do
    begin
      {$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
      if Assigned(recordop) and Assigned(recordop^.Finalize) then
        recordop^.Finalize(data);
      {$endif}
      Inc(PRecordInfoInit(typeInfo));
      { Process elements }
      for i:=1 to Count Do
        begin
          fpc_Finalize(Data+PRecordElement(typeInfo)^.Offset,PRecordElement(typeInfo)^.TypeInfo{$ifndef VER3_0}^{$endif});
          Inc(PRecordElement(typeInfo));
        end;
    end;
end;


procedure fpc_Addref_Record(Data,TypeInfo:Pointer);[Public,Alias : 'FPC_ADDREF_RECORD'];  compilerproc;
var
  i : longint;
{$ifndef VER3_0}
  item : PFastRTTIItem;
  offset: PSizeInt absolute item;
  field: PRecordElement absolute item;
{$endif}
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
{$ifndef VER3_0}
  if Assigned(PRecordInfoInit(typeInfo)^.FastRTTI) and assigned(PRecordInfoInit(typeInfo)^.FastRTTI^.GeneralRTTI) then
    with PRecordInfoInit(typeInfo)^.FastRTTI^,PRecordInfoInit(typeInfo)^.FastRTTI^.GeneralRTTI^ do
    begin
      item:=aligntoqword(Pointer(GeneralRTTI)+1);
      if frgAString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_AnsiStr_Incr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
  {$ifndef FPC_WIDESTRING_EQUAL_UNICODESTRING}
      if frgWString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_WideStr_Incr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
  {$endif FPC_WIDESTRING_EQUAL_UNICODESTRING}
      if frgUString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_UnicodeStr_Incr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
      if frgInterface in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          Intf_Incr_Ref(PPointer(Data+offset^)^);
          inc(offset);
        end;
      end;
      if frgVariant in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          variant_addref(PVarData(Data+offset^)^);
          inc(offset);
        end;
      end;
      if frgDynarray in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_dynarray_incr_ref(PPointer(Data+field^.offset)^);
          inc(field);
        end;
      end;
      AddRefOpCall(Data, TypeInfo);
    end
  else
{$endif VER3_0}
    with PRecordInfoInit(typeInfo)^ do
    begin
      Inc(PRecordInfoInit(typeInfo));
      { Process elements }
      for i:=1 to Count Do
        begin
          fpc_Addref(Data+PRecordElement(typeInfo)^.Offset,PRecordElement(typeInfo)^.TypeInfo{$ifndef VER3_0}^{$endif});
          Inc(PRecordElement(typeInfo));
        end;
      {$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
      if Assigned(recordop) and Assigned(recordop^.AddRef) then
        recordop^.AddRef(data);
      {$endif}
    end;
end;

{ define alias for internal use in the system unit }
Function fpc_Copy_internal (Src, Dest, TypeInfo : Pointer) : SizeInt;[external name 'FPC_COPY'];


function fpc_Copy_Record(Src,Dest,TypeInfo:Pointer): SizeInt;[Public,Alias : 'FPC_COPY_RECORD'];  compilerproc;
var
  i : longint;
{$ifndef VER3_0}
  item : PFastRTTIItem;
  offset: PSizeInt absolute item;
  field: PRecordElement absolute item;
  hole: PRTTIHoleItem absolute item;
{$endif}
  temp: pbyte;
  copiedsize,
  expectedoffset,
  fieldoffset: sizeint;
  info: pointer;
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
  temp:=typeInfo;
  Result:=PRecordInfoInit(typeInfo)^.Size;
{$ifndef VER3_0}
  if Assigned(PRecordInfoInit(typeInfo)^.FastRTTI) and assigned(PRecordInfoInit(typeInfo)^.FastRTTI^.GeneralRTTI) then
    with PRecordInfoInit(typeInfo)^ do
    if Assigned(recordop) and Assigned(recordop^.Copy) then
      recordop^.Copy(Src,Dest)
    else
    with PRecordInfoInit(typeInfo)^.FastRTTI^,PRecordInfoInit(typeInfo)^.FastRTTI^.GeneralRTTI^ do
    begin
      item:=aligntoqword(Pointer(GeneralRTTI)+1);
      if frgAString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_AnsiStr_Assign(PPointer(Dest+offset^)^,PPointer(Src+offset^)^);
          inc(offset);
        end;
      end;
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
  {$ifndef FPC_WIDESTRING_EQUAL_UNICODESTRING}
      if frgWString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_WideStr_Assign(PPointer(Dest+offset^)^,PPointer(Src+offset^)^);
          inc(offset);
        end;
      end;
  {$endif FPC_WIDESTRING_EQUAL_UNICODESTRING}
      if frgUString in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_UnicodeStr_Assign(PPointer(Dest+offset^)^,PPointer(Src+offset^)^);
          inc(offset);
        end;
      end;
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
      if frgInterface in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_intf_assign(PPointer(Dest+offset^)^,PPointer(Src+offset^)^);
          inc(offset);
        end;
      end;
      if frgVariant in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          VarCopyProc(PVarData(Dest+offset^)^,PVarData(Src+offset^)^);
          inc(offset);
        end;
      end;
      if frgDynarray in Flags then
      with item^ do
      begin
        inc(item);
        for i := 1 to Count do
        begin
          fpc_dynarray_assign(PPointer(Dest+field^.offset)^,PPointer(Src+field^.offset)^,field^.TypeInfo^);
          inc(field);
        end;
      end;
      { holes / non managed data }
      if assigned(HolesRTTI) then
      with HolesRTTI^ do
      begin
        hole:=Pointer(HolesRTTI);
        inc(PFastHolesRTTI(hole));
        for i := 1 to count do
        begin
          move((Src+hole^.offset)^,(Dest+hole^.offset)^,hole^.size);
          inc(hole);
        end;
      end;
    end
  else
{$endif VER3_0}
    with PRecordInfoInit(typeInfo)^ do
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    if Assigned(recordop) and Assigned(recordop^.Copy) then
      recordop^.Copy(Src,Dest)
    else
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
      begin
        Inc(PRecordInfoInit(Temp));
        expectedoffset:=0;
        { Process elements with rtti }
        for i:=1 to Count Do
          begin
            Info:=PRecordElement(Temp)^.TypeInfo{$ifndef VER3_0}^{$endif};
            fieldOffset:=PRecordElement(Temp)^.Offset;
            Inc(PRecordElement(Temp));
            if fieldOffset>expectedoffset then
              move((Src+expectedoffset)^,(Dest+expectedoffset)^,fieldOffset-expectedoffset);
            copiedsize:=fpc_Copy_internal(Src+fieldOffset,Dest+fieldOffset,Info);
            expectedoffset:=fieldOffset+copiedsize;
          end;
        { elements remaining? }
        if result>expectedoffset then
          move((Src+expectedoffset)^,(Dest+expectedoffset)^,Result-expectedoffset);
      end;
end;


procedure RecordRTTI(Data,TypeInfo:Pointer;rttiproc:TRTTIProc);
var
  count,
  i : longint;
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
  Count:=PRecordInfoInit(typeInfo)^.Count;
  Inc(PRecordInfoInit(typeInfo));
  { Process elements }
  for i:=1 to count Do
    begin
      rttiproc(Data+PRecordElement(typeInfo)^.Offset,PRecordElement(typeInfo)^.TypeInfo{$ifndef VER3_0}^{$endif});
      Inc(PRecordElement(typeInfo));
    end;
end;


{ if you modify this procedure, fpc_copy must be probably modified as well }
{$ifdef VER2_6}
procedure ArrayRTTI(Data,TypeInfo:Pointer;rttiproc:TRTTIProc);
var
  i: SizeInt;
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
  { Process elements }
  for I:=0 to PArrayInfo(typeInfo)^.ElCount-1 do
    rttiproc(Data+(I*PArrayInfo(typeInfo)^.Size),PArrayInfo(typeInfo)^.ElInfo);
end;
{$else}
procedure ArrayRTTI(Data,TypeInfo:Pointer;rttiproc:TRTTIProc);
var  
  i,Count,ElSize: SizeInt;
  Info: Pointer;
begin
{$ifdef VER3_0}
  typeInfo:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
  typeInfo:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
  Count:=PArrayInfo(typeInfo)^.ElCount;
  { no elements to process => exit }
  if Count = 0 then
    Exit;
  ElSize:=PArrayInfo(typeInfo)^.Size div Count;
  Info:=PArrayInfo(typeInfo)^.ElInfo{$ifndef VER3_0}^{$endif};
  { Process elements }
  for I:=0 to Count-1 do
    rttiproc(Data+(I*ElSize),Info);
end;
{$endif}

Procedure fpc_Initialize (Data,TypeInfo : pointer);[Public,Alias : 'FPC_INITIALIZE'];  compilerproc;
begin
  case PTypeKind(TypeInfo)^ of
{$ifdef FPC_HAS_FEATURE_DYNARRAYS}
    tkDynArray,
{$endif FPC_HAS_FEATURE_DYNARRAYS}
{$ifdef FPC_HAS_FEATURE_ANSISTRINGS}
    tkAstring,
{$endif FPC_HAS_FEATURE_ANSISTRINGS}
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
    tkWstring,tkUString,
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
    tkInterface:
      PPchar(Data)^:=Nil;
    tkArray:
      arrayrtti(data,typeinfo,@int_initialize);
{$ifdef FPC_HAS_FEATURE_OBJECTS}
    tkObject,
{$endif FPC_HAS_FEATURE_OBJECTS}
    tkRecord:
      int_InitializeRecord(data,RTTIRecordRttiInfoToInitInfo(typeinfo));
{$ifdef FPC_HAS_FEATURE_VARIANTS}
    tkVariant:
      variant_init(PVarData(Data)^);
{$endif FPC_HAS_FEATURE_VARIANTS}
  end;
end;


Procedure fpc_finalize (Data,TypeInfo: Pointer);[Public,Alias : 'FPC_FINALIZE'];  compilerproc;
begin
  case PTypeKind(TypeInfo)^ of
{$ifdef FPC_HAS_FEATURE_ANSISTRINGS}
    tkAstring :
      fpc_AnsiStr_Decr_Ref(PPointer(Data)^);
{$endif FPC_HAS_FEATURE_ANSISTRINGS}
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
    tkUstring :
      fpc_UnicodeStr_Decr_Ref(PPointer(Data)^);
  {$ifndef FPC_WIDESTRING_EQUAL_UNICODESTRING}
    tkWstring :
      fpc_WideStr_Decr_Ref(PPointer(Data)^);
  {$endif FPC_WIDESTRING_EQUAL_UNICODESTRING}
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
    tkArray :
      arrayrtti(data,typeinfo,@int_finalize);
{$ifdef FPC_HAS_FEATURE_OBJECTS}
    tkObject,
{$endif FPC_HAS_FEATURE_OBJECTS}
    tkRecord:
      int_FinalizeRecord(data,RTTIRecordRttiInfoToInitInfo(typeinfo));
    tkInterface:
      Intf_Decr_Ref(PPointer(Data)^);
{$ifdef FPC_HAS_FEATURE_DYNARRAYS}
    tkDynArray:
      fpc_dynarray_clear(PPointer(Data)^,TypeInfo);
{$endif FPC_HAS_FEATURE_DYNARRAYS}
{$ifdef FPC_HAS_FEATURE_VARIANTS}
    tkVariant:
      variant_clear(PVarData(Data)^);
{$endif FPC_HAS_FEATURE_VARIANTS}
  end;
end;


Procedure fpc_Addref (Data,TypeInfo : Pointer); [Public,alias : 'FPC_ADDREF'];  compilerproc;
begin
  case PTypeKind(TypeInfo)^ of
{$ifdef FPC_HAS_FEATURE_ANSISTRINGS}
    tkAstring :
      fpc_AnsiStr_Incr_Ref(PPointer(Data)^);
{$endif FPC_HAS_FEATURE_ANSISTRINGS}
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
  {$ifndef FPC_WIDESTRING_EQUAL_UNICODESTRING}
    tkWstring :
      fpc_WideStr_Incr_Ref(PPointer(Data)^);
  {$endif FPC_WIDESTRING_EQUAL_UNICODESTRING}
    tkUstring :
      fpc_UnicodeStr_Incr_Ref(PPointer(Data)^);
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
    tkArray :
      arrayrtti(data,typeinfo,@int_addref);
{$ifdef FPC_HAS_FEATURE_OBJECTS}
    tkobject,
{$endif FPC_HAS_FEATURE_OBJECTS}
    tkrecord :
      int_AddRefRecord(data,RTTIRecordRttiInfoToInitInfo(typeinfo));
{$ifdef FPC_HAS_FEATURE_DYNARRAYS}
    tkDynArray:
      fpc_dynarray_incr_ref(PPointer(Data)^);
{$endif FPC_HAS_FEATURE_DYNARRAYS}
    tkInterface:
      Intf_Incr_Ref(PPointer(Data)^);
{$ifdef FPC_HAS_FEATURE_VARIANTS}
    tkVariant:
      variant_addref(pvardata(Data)^);
{$endif FPC_HAS_FEATURE_DYNARRAYS}
  end;
end;


Function fpc_Copy (Src, Dest, TypeInfo : Pointer) : SizeInt;[Public,alias : 'FPC_COPY']; compilerproc;
var
  Temp: pbyte;
  copiedsize,
  expectedoffset,
  count,
  offset,
  i: SizeInt;
  info: pointer;
begin
  result:=sizeof(pointer);
  case PTypeKind(TypeInfo)^ of
{$ifdef FPC_HAS_FEATURE_ANSISTRINGS}
    tkAstring:
      fpc_AnsiStr_Assign(PPointer(Dest)^,PPointer(Src)^);
{$endif FPC_HAS_FEATURE_ANSISTRINGS}
{$ifdef FPC_HAS_FEATURE_WIDESTRINGS}
  {$ifndef FPC_WIDESTRING_EQUAL_UNICODESTRING}
    tkWstring:
      fpc_WideStr_Assign(PPointer(Dest)^,PPointer(Src)^);
  {$endif FPC_WIDESTRING_EQUAL_UNICODESTRING}
    tkUstring:
      fpc_UnicodeStr_Assign(PPointer(Dest)^,PPointer(Src)^);
{$endif FPC_HAS_FEATURE_WIDESTRINGS}
    tkArray:
      begin
{$ifdef VER3_0}
        Temp:=aligntoptr(typeInfo+2+PByte(typeInfo)[1]);
{$else VER3_0}
        Temp:=aligntoqword(typeInfo+2+PByte(typeInfo)[1]);
{$endif VER3_0}
      {$ifdef VER2_6}
        { Process elements }
        for I:=0 to PArrayInfo(Temp)^.ElCount-1 do
          fpc_Copy_internal(Src+(I*PArrayInfo(Temp)^.Size),Dest+(I*PArrayInfo(Temp)^.Size),PArrayInfo(Temp)^.ElInfo);
        Result:=PArrayInfo(Temp)^.Size*PArrayInfo(Temp)^.ElCount;
      {$else}
        Result:=PArrayInfo(Temp)^.Size;
        Count:=PArrayInfo(Temp)^.ElCount;
        { no elements to process => exit }
        if Count = 0 then
          Exit;
        Info:=PArrayInfo(Temp)^.ElInfo{$ifndef VER3_0}^{$endif};
        copiedsize:=Result div Count;
        Offset:=0;
        { Process elements }
        for I:=1 to Count do
          begin
            fpc_Copy_internal(Src+Offset,Dest+Offset,Info);
            inc(Offset,copiedsize);
          end;
      {$endif}
      end;
{$ifdef FPC_HAS_FEATURE_OBJECTS}
    tkobject,
{$endif FPC_HAS_FEATURE_OBJECTS}
    tkrecord:
      result:=int_CopyRecord(Src,Dest,RTTIRecordRttiInfoToInitInfo(typeInfo));
{$ifdef FPC_HAS_FEATURE_DYNARRAYS}
    tkDynArray:
      fpc_dynarray_assign(PPointer(Dest)^,PPointer(Src)^,typeinfo);
{$endif FPC_HAS_FEATURE_DYNARRAYS}
    tkInterface:
      fpc_intf_assign(PPointer(Dest)^,PPointer(Src)^);
{$ifdef FPC_HAS_FEATURE_VARIANTS}
    tkVariant:
      begin
        VarCopyProc(pvardata(dest)^,pvardata(src)^);
        result:=sizeof(tvardata);
      end;
{$endif FPC_HAS_FEATURE_VARIANTS}
  end;
end;


{ For internal use by the compiler, because otherwise $x- can cause trouble. }
{ Generally disabling extended syntax checking for all compilerprocs may     }
{ have unintended side-effects                                               }
procedure fpc_Copy_proc (Src, Dest, TypeInfo : Pointer);compilerproc; inline;
begin
  fpc_copy_internal(src,dest,typeinfo);
end;

procedure fpc_CopyRecord_proc (Src, Dest, TypeInfo : Pointer);compilerproc; inline;
begin
  int_CopyRecord(src,dest,typeinfo);
end;

procedure fpc_initialize_array(data,typeinfo : pointer;count : SizeInt); [public,alias:'FPC_INITIALIZE_ARRAY']; compilerproc;
  var
    i, size : SizeInt;
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    hasManagementOp: boolean;
  begin
    size:=RTTISizeAndOp(typeinfo, rotInitialize, hasManagementOp);
    if (size>0) or hasManagementOp then
{$else FPC_HAS_MANAGEMENT_OPERATORS}
  begin
    size:=RTTISize(typeInfo);
    if size>0 then
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
      for i:=0 to count-1 do
        int_initialize(data+size*i,typeinfo);
  end;


procedure fpc_finalize_array(data,typeinfo : pointer;count : SizeInt); [Public,Alias:'FPC_FINALIZE_ARRAY'];  compilerproc;
  var
     i, size: SizeInt;
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    hasManagementOp: boolean;
  begin
    size:=RTTISizeAndOp(typeinfo, rotFinalize, hasManagementOp);
    if (size>0) or hasManagementOp then
{$else FPC_HAS_MANAGEMENT_OPERATORS}
  begin
    size:=RTTISize(typeInfo);
    if size>0 then
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
      for i:=0 to count-1 do
        int_finalize(data+size*i,typeinfo);
  end;


procedure fpc_addref_array(data,typeinfo: pointer; count: SizeInt); [public,alias:'FPC_ADDREF_ARRAY']; compilerproc;
  var
    i, size: SizeInt;
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    hasManagementOp: boolean;
  begin
    size:=RTTISizeAndOp(typeinfo, rotAddRef, hasManagementOp);
    if (size>0) or hasManagementOp then
{$else FPC_HAS_MANAGEMENT_OPERATORS}
  begin
    size:=RTTISize(typeInfo);
    if size>0 then
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
      for i:=0 to count-1 do
        int_addref(data+size*i,typeinfo);
  end;

{ The following two procedures are now obsolete, needed only for bootstrapping }
procedure fpc_decref (Data, TypeInfo : Pointer);[Public,alias : 'FPC_DECREF'];  compilerproc;
  begin
    int_finalize(Data,TypeInfo);
  end;

procedure fpc_decref_array(data,typeinfo: pointer; count: SizeInt); [public,alias:'FPC_DECREF_ARRAY']; compilerproc;
  begin
    int_finalizeArray(data,typeinfo,count);
  end;

procedure InitializeArray(p, typeInfo: Pointer; count: SizeInt);
  external name 'FPC_INITIALIZE_ARRAY';

procedure FinalizeArray(p, typeInfo: Pointer; count: SizeInt);
  external name 'FPC_FINALIZE_ARRAY';

procedure CopyArray(dest, source, typeInfo: Pointer; count: SizeInt);
  var
    i, size: SizeInt;
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    hasManagementOp: boolean;
  begin
    size:=RTTISizeAndOp(typeinfo, rotCopy, hasManagementOp);
    if (size>0) or hasManagementOp then
{$else FPC_HAS_MANAGEMENT_OPERATORS}
  begin
    size:=RTTISize(typeInfo);
    if size>0 then
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
      for i:=0 to count-1 do
        fpc_Copy_internal(source+size*i, dest+size*i, typeInfo);
  end;

