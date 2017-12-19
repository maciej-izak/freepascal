{ Author: Mattias Gaertner  2017  mattias@freepascal.org

  Abstract:
    Command line interface for the pas2js compiler.
}
program pas2js;

{$mode objfpc}{$H+}

uses
  {$IFDEF UNIX}
  cthreads, cwstring,
  {$ENDIF}
  Pas2jsFileUtils, Classes, SysUtils, CustApp,
  Pas2jsCompiler;

Type

  { TPas2jsCLI }

  TPas2jsCLI = class(TCustomApplication)
  private
    FCompiler: TPas2jsCompiler;
    FWriteOutputToStdErr: Boolean;
  protected
    procedure DoRun; override;
  public
    constructor Create(TheOwner: TComponent); override;
    destructor Destroy; override;
    property Compiler: TPas2jsCompiler read FCompiler;
    property WriteOutputToStdErr: Boolean read FWriteOutputToStdErr write FWriteOutputToStdErr;
  end;

procedure TPas2jsCLI.DoRun;
var
  ParamList: TStringList;
  i: Integer;
begin
  ParamList:=TStringList.Create;
  try
    for i:=1 to ParamCount do
      ParamList.Add(Params[i]);
    try
      Compiler.Run(ParamStr(0),GetCurrentDirUTF8,ParamList);
    except
      on E: ECompilerTerminate do ;
    end;
  finally
    ParamList.Free;
    Compiler.Log.CloseOutputFile;
  end;

  // stop program loop
  Terminate; // Keep ExitCode!
end;

constructor TPas2jsCLI.Create(TheOwner: TComponent);
begin
  inherited Create(TheOwner);
  StopOnException:=True;
  FCompiler:=TPas2jsCompiler.Create;
end;

destructor TPas2jsCLI.Destroy;
begin
  FreeAndNil(FCompiler);
  inherited Destroy;
end;

var
  Application: TPas2jsCLI;
begin
  Application:=TPas2jsCLI.Create(nil);
  Application.Run;
  Application.Free;
end.

