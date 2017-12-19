{
    This file is part of the Free Pascal run time library.
    Copyright (c) 1999-2017 by Maciej Izak

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

{$ifndef FPC_REQUIRES_PROPER_ALIGNMENT}
  {$define USE_PACKED}
{$endif}
{$ifdef VER2_6}
  {$define USE_PACKED}
{$endif}

type
  PRecordElement=^TRecordElement;
  TRecordElement=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    {$ifdef VER3_0}
    TypeInfo: Pointer;
    {$else}
    TypeInfo: PPointer;
    {$endif}
    {$ifdef VER2_6}
    Offset: Longint;
    {$else}
    Offset: SizeInt;
    {$endif}
  end;

  PRecordInfoFull=^TRecordInfoFull;
  TRecordInfoFull=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
{$ifndef VER3_0}
    InitTable: Pointer;
{$endif VER3_0}
    Size: Longint;
    Count: Longint;
    { Elements: array[count] of TRecordElement }
  end;

  PRecordInfoInit=^TRecordInfoInit;
{$ifndef VER3_0}
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
  TRTTIRecVarOp=procedure(ARec: Pointer);
  PRTTIRecVarOpEntry=^TRTTIRecVarOpEntry;
  TRTTIRecVarOpEntry=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Op: TRTTIRecVarOp;
    Offset: SizeInt;
  end;
  TRTTIRecCopyOp=procedure(ASrc, ADest: Pointer);
  PRTTIRecCopyOpEntry=^TRTTIRecCopyOpEntry;
  TRTTIRecCopyOpEntry=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Op: TRTTIRecCopyOp;
    Offset: SizeInt;
  end;
  PFastRTTIItem=^TFastRTTIItem;
  TFastRTTIItem=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Count: Longint;
    { Elements: array[count] of TRecordElement }
  end;
  TFastRTTIGeneralFlag=(frgAString, frgWString, frgUString, frgInterface, frgVariant, frgDynarray);
  TFastRTTIInitializationFlag=(friPointer, friVariant);
  {$push}
  {$packset 1}
  TFastRTTIGeneralFlags=set of TFastRTTIGeneralFlag;
  TFastRTTIInitializationFlags=set of TFastRTTIInitializationFlag;
  {$pop}
  PVarOpList=^TVarOpList;
  TVarOpList=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Count: Longint;
    { Elements: array[count] of TRTTIRecVarOpEntry }
  end;
  PCopyOpList=^TCopyOpList;
  TCopyOpList=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Count: Longint;
    { Elements: array[count] of TRTTIRecCopyOpentry }
  end;
  PFastInitializationRTTI=^TFastInitializationRTTI;
  TFastInitializationRTTI=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Flags: TFastRTTIInitializationFlags;
    { elements depnding on Flags }
  end;

  PFastGeneralRTTI=^TFastGeneralRTTI;
  TFastGeneralRTTI=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Flags: TFastRTTIGeneralFlags;
    { elements depnding on Flags }
  end;

  PRTTIHoleItem=^TRTTIHoleItem;
  TRTTIHoleItem=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Size: SizeInt;
    Offset: SizeInt;
  end;

  PFastHolesRTTI=^TFastHolesRTTI;
  TFastHolesRTTI=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Count: Longint;
    { Elements: array[count] of TRTTIHole }
  end;

  PFastRTTI=^TFastRTTI;
  TFastRTTI=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    FinalizeOpList: PVarOpList;
    AddRefOpList: PVarOpList;
    //CopyOpList: PCopyOpList;
    InitializationRTTI: PFastInitializationRTTI;
    GeneralRTTI: PFastGeneralRTTI;
    HolesRTTI: PFastHolesRTTI;
  end;

  TRTTIRecOpType=(rotAny, rotInitialize, rotFinalize, rotAddRef, rotCopy);
  PRTTIRecordOpVMT=^TRTTIRecordOpVMT;
  TRTTIRecordOpVMT=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Initialize: TRTTIRecVarOp;
    Finalize: TRTTIRecVarOp;
    AddRef: TRTTIRecVarOp;
    Copy: TRTTIRecCopyOp;
  end;
{$endif FPC_HAS_MANAGEMENT_OPERATORS}

  TRecordInfoInit=
{$ifdef USE_PACKED}
  packed
{$endif USE_PACKED}
  record
    Terminator: Pointer;
    Size: Longint;
{$ifdef FPC_HAS_MANAGEMENT_OPERATORS}
    RecordOp: PRTTIRecordOpVMT;
    InitializeOpList: PVarOpList;
    FastRTTI: PFastRTTI;
{$endif FPC_HAS_MANAGEMENT_OPERATORS}
    Count: Longint;
    { Elements: array[count] of TRecordElement }
  end;
{$else VER3_0}
  TRecordInfoInit=TRecordInfoFull;
{$endif VER3_0}

{$ifndef VER3_0}
procedure InitializeOpCall(instance: pointer; recinfo: PRecordInfoInit); inline;
var
  oplist: PVarOpList;
  i : longint;
  initializeopentry : PRTTIRecVarOpEntry absolute oplist;
begin
  if assigned(recinfo^.InitializeOpList) then
  with recinfo^.InitializeOpList^ do
  begin
    oplist:=recinfo^.InitializeOpList;
    inc(oplist);
    for i := 1 to count do
    begin
      initializeopentry^.op(instance+initializeopentry^.offset);
      inc(initializeopentry);
    end;
  end;
end;

procedure FinalizeOpCall(instance: pointer; recinfo: PRecordInfoInit); inline;
var
  oplist: PVarOpList;
  i : longint;
  finalizeopentry : PRTTIRecVarOpEntry absolute oplist;
begin
  if assigned(recinfo^.FastRTTI) and assigned(recinfo^.FastRTTI^.FinalizeOpList) then
  with recinfo^.FastRTTI^.FinalizeOpList^ do
  begin
    oplist:=recinfo^.FastRTTI^.FinalizeOpList;
    inc(oplist);
    for i := 1 to count do
    begin
      finalizeopentry^.op(instance+finalizeopentry^.offset);
      inc(finalizeopentry);
    end;
  end;
end;

procedure AddRefOpCall(instance: pointer; recinfo: PRecordInfoInit); inline;
var
  oplist: PVarOpList;
  i : longint;
  addrefopentry : PRTTIRecVarOpEntry absolute oplist;
begin
  if assigned(recinfo^.FastRTTI) and assigned(recinfo^.FastRTTI^.AddRefOpList) then
  with recinfo^.FastRTTI^.AddRefOpList^ do
  begin
    oplist:=recinfo^.FastRTTI^.AddRefOpList;
    inc(oplist);
    for i := 1 to count do
    begin
      addrefopentry^.op(instance+addrefopentry^.offset);
      inc(addrefopentry);
    end;
  end;
end;
{$endif}
