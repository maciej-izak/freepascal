{
    This file is part of the Free Component Library

    Pascal source parser
    Copyright (c) 2000-2005 by
      Areca Systems GmbH / Sebastian Guenther, sg@freepascal.org

    See the file COPYING.FPC, included in this distribution,
    for details about the copyright.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

 **********************************************************************}

{$mode objfpc}
{$h+}

unit PParser;

interface

uses SysUtils, Classes, PasTree, PScanner;

// message numbers
const
  nErrNoSourceGiven = 2001;
  nErrMultipleSourceFiles = 2002;
  nParserError = 2003;
  nParserErrorAtToken = 2004;
  nParserUngetTokenError = 2005;
  nParserExpectTokenError = 2006;
  nParserForwardNotInterface = 2007;
  nParserExpectVisibility = 2008;
  nParserStrangeVisibility = 2009;
  nParserExpectToken2Error = 2010;
  nParserExpectedCommaRBracket = 2011;
  nParserExpectedCommaSemicolon = 2012;
  nParserExpectedAssignIn = 2013;
  nParserExpectedCommaColon = 2014;
  nErrUnknownOperatorType = 2015;
  nParserOnlyOneArgumentCanHaveDefault = 2016;
  nParserExpectedLBracketColon = 2017;
  nParserExpectedSemiColonEnd = 2018;
  nParserExpectedConstVarID = 2019;
  nParserExpectedNested = 2020;
  nParserExpectedColonID = 2021;
  nParserSyntaxError = 2022;
  nParserTypeSyntaxError = 2023;
  nParserArrayTypeSyntaxError = 2024;
  nParserExpectedIdentifier = 2026;
  nParserNotAProcToken = 2026;
  nRangeExpressionExpected = 2027;
  nParserExpectCase = 2028;
  nParserHelperNotAllowed = 2029;
  nLogStartImplementation = 2030;
  nLogStartInterface = 2031;
  nParserNoConstructorAllowed = 2032;
  nParserNoFieldsAllowed = 2033;
  nParserInvalidRecordVisibility = 2034;
  nErrRecordConstantsNotAllowed = 2035;
  nErrRecordMethodsNotAllowed = 2036;
  nErrRecordPropertiesNotAllowed = 2037;
  nErrRecordVisibilityNotAllowed = 2038;
  nParserTypeNotAllowedHere = 2039;
  nParserNotAnOperand = 2040;
  nParserArrayPropertiesCannotHaveDefaultValue = 2041;
  nParserDefaultPropertyMustBeArray = 2042;
  nParserUnknownProcedureType = 2043;
  nParserGenericArray1Element = 2044;
  nParserGenericClassOrArray = 2045;
  nParserDuplicateIdentifier = 2046;
  nParserDefaultParameterRequiredFor = 2047;
  nParserOnlyOneVariableCanBeInitialized = 2048;
  nParserExpectedTypeButGot = 2049;


// resourcestring patterns of messages
resourcestring
  SErrNoSourceGiven = 'No source file specified';
  SErrMultipleSourceFiles = 'Please specify only one source file';
  SParserError = 'Error';
  SParserErrorAtToken = '%s at token "%s" in file %s at line %d column %d';
  SParserUngetTokenError = 'Internal error: Cannot unget more tokens, history buffer is full';
  SParserExpectTokenError = 'Expected "%s"';
  SParserForwardNotInterface = 'The use of a FORWARD procedure modifier is not allowed in the interface';
  SParserExpectVisibility = 'Expected visibility specifier';
  SParserStrangeVisibility = 'Strange strict visibility encountered : "%s"';
  SParserExpectToken2Error = 'Expected "%s" or "%s"';
  SParserExpectedCommaRBracket = 'Expected "," or ")"';
  SParserExpectedCommaSemicolon = 'Expected "," or ";"';
  SParserExpectedAssignIn = 'Expected := or in';
  SParserExpectedCommaColon = 'Expected "," or ":"';
  SErrUnknownOperatorType = 'Unknown operator type: %s';
  SParserOnlyOneArgumentCanHaveDefault = 'A default value can only be assigned to 1 parameter';
  SParserExpectedLBracketColon = 'Expected "(" or ":"';
  SParserExpectedSemiColonEnd = 'Expected ";" or "End"';
  SParserExpectedConstVarID = 'Expected "const", "var" or identifier';
  SParserExpectedNested = 'Expected nested keyword';
  SParserExpectedColonID = 'Expected ":" or identifier';
  SParserSyntaxError = 'Syntax error';
  SParserTypeSyntaxError = 'Syntax error in type';
  SParserArrayTypeSyntaxError = 'Syntax error in array type';
  SParserExpectedIdentifier = 'Identifier expected';
  SParserNotAProcToken = 'Not a procedure or function token';
  SRangeExpressionExpected = 'Range expression expected';
  SParserExpectCase = 'Case label expression expected';
  SParserHelperNotAllowed = 'Helper objects not allowed for "%s"';
  SLogStartImplementation = 'Start parsing implementation section.';
  SLogStartInterface = 'Start parsing interface section';
  SParserNoConstructorAllowed = 'Constructors or Destructors are not allowed in Interfaces or Record helpers';
  SParserNoFieldsAllowed = 'Fields are not allowed in Interfaces';
  SParserInvalidRecordVisibility = 'Records can only have public and (strict) private as visibility specifiers';
  SErrRecordConstantsNotAllowed = 'Record constants not allowed at this location.';
  SErrRecordMethodsNotAllowed = 'Record methods not allowed at this location.';
  SErrRecordPropertiesNotAllowed = 'Record properties not allowed at this location.';
  SErrRecordVisibilityNotAllowed = 'Record visibilities not allowed at this location.';
  SParserTypeNotAllowedHere = 'Type "%s" not allowed here';
  SParserNotAnOperand = 'Not an operand: (%d : %s)';
  SParserArrayPropertiesCannotHaveDefaultValue = 'Array properties cannot have default value';
  SParserDefaultPropertyMustBeArray = 'The default property must be an array property';
  SParserUnknownProcedureType = 'Unknown procedure type "%d"';
  SParserGenericArray1Element = 'Generic arrays can have only 1 template element';
  SParserGenericClassOrArray = 'Generic can only be used with classes or arrays';
  SParserDuplicateIdentifier = 'Duplicate identifier "%s"';
  SParserDefaultParameterRequiredFor = 'Default parameter required for "%s"';
  SParserOnlyOneVariableCanBeInitialized = 'Only one variable can be initialized';
  SParserExpectedTypeButGot = 'Expected type, but got %s';

type
  TPasScopeType = (
    stModule,  // e.g. unit, program, library
    stUsesList,
    stTypeSection,
    stTypeDef, // e.g. the B in 'type A=B;'
    stConstDef, // e.g. the B in 'const A=B;'
    stProcedure, // also method, procedure, constructor, destructor, ...
    stProcedureHeader,
    stExceptOnExpr,
    stExceptOnStatement,
    stDeclaration, // e.g. a TPasType, TPasProperty
    //stStatement,
    stAncestors // the list of ancestors and interfaces of a class
    );
  TPasScopeTypes = set of TPasScopeType;

  TPasParserLogHandler = Procedure (Sender : TObject; Const Msg : String) of object;
  TPParserLogEvent = (pleInterface,pleImplementation);
  TPParserLogEvents = set of TPParserLogEvent;
  TPasParser = Class;

  { TPasTreeContainer }

  TPasTreeContainer = class
  private
    FCurrentParser: TPasParser;
    FNeedComments: Boolean;
    FOnLog: TPasParserLogHandler;
    FPParserLogEvents: TPParserLogEvents;
    FScannerLogEvents: TPScannerLogEvents;
  protected
    FPackage: TPasPackage;
    FInterfaceOnly : Boolean;
    procedure SetCurrentParser(AValue: TPasParser); virtual;
  public
    function CreateElement(AClass: TPTreeElement; const AName: String;
      AParent: TPasElement; const ASourceFilename: String;
      ASourceLinenumber: Integer): TPasElement;overload;
    function CreateElement(AClass: TPTreeElement; const AName: String;
      AParent: TPasElement; AVisibility: TPasMemberVisibility;
      const ASourceFilename: String; ASourceLinenumber: Integer): TPasElement;overload;
      virtual; abstract;
    function CreateElement(AClass: TPTreeElement; const AName: String;
      AParent: TPasElement; AVisibility: TPasMemberVisibility;
      const ASrcPos: TPasSourcePos): TPasElement; overload;
      virtual;
    function CreateFunctionType(const AName, AResultName: String; AParent: TPasElement;
      UseParentAsResultParent: Boolean; const ASrcPos: TPasSourcePos): TPasFunctionType;
    function FindElement(const AName: String): TPasElement; virtual; abstract;
    procedure FinishScope(ScopeType: TPasScopeType; El: TPasElement); virtual;
    function FindModule(const AName: String): TPasModule; virtual;
    property Package: TPasPackage read FPackage;
    property InterfaceOnly : Boolean Read FInterfaceOnly Write FInterFaceOnly;
    property ScannerLogEvents : TPScannerLogEvents Read FScannerLogEvents Write FScannerLogEvents;
    property ParserLogEvents : TPParserLogEvents Read FPParserLogEvents Write FPParserLogEvents;
    property OnLog : TPasParserLogHandler Read FOnLog Write FOnLog;
    property CurrentParser : TPasParser Read FCurrentParser Write SetCurrentParser;
    property NeedComments : Boolean Read FNeedComments Write FNeedComments;
  end;

  EParserError = class(Exception)
  private
    FFilename: String;
    FRow, FColumn: Integer;
  public
    constructor Create(const AReason, AFilename: String;
      ARow, AColumn: Integer);
    property Filename: String read FFilename;
    property Row: Integer read FRow;
    property Column: Integer read FColumn;
  end;

  TProcType = (ptProcedure, ptFunction, ptOperator, ptClassOperator, ptConstructor, ptDestructor,
               ptClassProcedure, ptClassFunction, ptClassConstructor, ptClassDestructor);


  TExprKind = (ek_Normal, ek_PropertyIndex);
  TIndentAction = (iaNone,iaIndent,iaUndent);

  { TPasParser }

  TPasParser = class
  private
    FCurModule: TPasModule;
    FFileResolver: TBaseFileResolver;
    FImplicitUses: TStrings;
    FLastMsg: string;
    FLastMsgArgs: TMessageArgs;
    FLastMsgNumber: integer;
    FLastMsgPattern: string;
    FLastMsgType: TMessageType;
    FLogEvents: TPParserLogEvents;
    FOnLog: TPasParserLogHandler;
    FOptions: TPOptions;
    FScanner: TPascalScanner;
    FEngine: TPasTreeContainer;
    FCurToken: TToken;
    FCurTokenString: String;
    FCurComments : TStrings;
    FSavedComments : String;
    // UngetToken support:
    FTokenBuffer: array[0..1] of TToken;
    FTokenStringBuffer: array[0..1] of String;
    FCommentsBuffer: array[0..1] of TStrings;
    FTokenBufferIndex: Integer; // current index in FTokenBuffer
    FTokenBufferSize: Integer; // maximum valid index in FTokenBuffer
    FDumpIndent : String;
    function CheckOverloadList(AList: TFPList; AName: String; out OldMember: TPasElement): TPasOverloadedProc;
    procedure DumpCurToken(Const Msg : String; IndentAction : TIndentAction = iaNone);
    function GetVariableModifiers(Out VarMods : TVariableModifiers; Out Libname,ExportName : string): string;
    function GetVariableValueAndLocation(Parent : TPasElement; Out Value : TPasExpr; Out Location: String): Boolean;
    procedure HandleProcedureModifier(Parent: TPasElement; pm : TProcedureModifier);
    procedure ParseClassLocalConsts(AType: TPasClassType; AVisibility: TPasMemberVisibility);
    procedure ParseClassLocalTypes(AType: TPasClassType; AVisibility: TPasMemberVisibility);
    procedure ParseVarList(Parent: TPasElement; VarList: TFPList; AVisibility: TPasMemberVisibility; Full: Boolean);
    procedure SetOptions(AValue: TPOptions);
  protected
    Function SaveComments : String;
    Function SaveComments(Const AValue : String) : String;
    function LogEvent(E : TPParserLogEvent) : Boolean; inline;
    Procedure DoLog(MsgType: TMessageType; MsgNumber: integer; Const Msg : String; SkipSourceInfo : Boolean = False);overload;
    Procedure DoLog(MsgType: TMessageType; MsgNumber: integer; Const Fmt : String; Args : Array of const;SkipSourceInfo : Boolean = False);overload;
    function GetProcTypeFromToken(tk: TToken; IsClass: Boolean=False ): TProcType;
    procedure ParseAsmBlock(AsmBlock: TPasImplAsmStatement); virtual;
    procedure ParseRecordFieldList(ARec: TPasRecordType; AEndToken: TToken; AllowMethods : Boolean);
    procedure ParseRecordVariantParts(ARec: TPasRecordType; AEndToken: TToken);
    function GetProcedureClass(ProcType : TProcType): TPTreeElement;
    procedure ParseClassFields(AType: TPasClassType; const AVisibility: TPasMemberVisibility; IsClassField : Boolean);
    procedure ParseClassMembers(AType: TPasClassType);
    procedure ProcessMethod(AType: TPasClassType; IsClass : Boolean; AVisibility : TPasMemberVisibility);
    procedure ReadGenericArguments(List : TFPList;Parent : TPasElement);
    function CheckProcedureArgs(Parent: TPasElement;
      Args: TFPList; // list of TPasArgument
      Mandatory: Boolean): boolean;
    function CheckVisibility(S: String; var AVisibility: TPasMemberVisibility): Boolean;
    procedure ParseExc(MsgNumber: integer; const Msg: String);
    procedure ParseExc(MsgNumber: integer; const Fmt: String; Args : Array of const);
    procedure ParseExcExpectedIdentifier;
    procedure ParseExcSyntaxError;
    procedure ParseExcTokenError(const Arg: string);
    function OpLevel(t: TToken): Integer;
    Function TokenToExprOp (AToken : TToken) : TExprOpCode;
    function CreateElement(AClass: TPTreeElement; const AName: String; AParent: TPasElement): TPasElement;overload;
    function CreateElement(AClass: TPTreeElement; const AName: String; AParent: TPasElement; const ASrcPos: TPasSourcePos): TPasElement;overload;
    function CreateElement(AClass: TPTreeElement; const AName: String; AParent: TPasElement; AVisibility: TPasMemberVisibility): TPasElement;overload;
    function CreateElement(AClass: TPTreeElement; const AName: String; AParent: TPasElement; AVisibility: TPasMemberVisibility; const ASrcPos: TPasSourcePos): TPasElement;overload;
    function CreatePrimitiveExpr(AParent: TPasElement; AKind: TPasExprKind; const AValue: String): TPrimitiveExpr;
    function CreateBoolConstExpr(AParent: TPasElement; AKind: TPasExprKind; const ABoolValue : Boolean): TBoolConstExpr;
    function CreateBinaryExpr(AParent : TPasElement; xleft, xright: TPasExpr; AOpCode: TExprOpCode): TBinaryExpr;
    procedure AddToBinaryExprChain(var ChainFirst, ChainLast: TPasExpr;
      Element: TPasExpr; AOpCode: TExprOpCode);
    procedure AddParamsToBinaryExprChain(var ChainFirst, ChainLast: TPasExpr;
      Params: TParamsExpr);
    function CreateUnaryExpr(AParent : TPasElement; AOperand: TPasExpr; AOpCode: TExprOpCode): TUnaryExpr;
    function CreateArrayValues(AParent : TPasElement): TArrayValues;
    function CreateFunctionType(const AName, AResultName: String; AParent: TPasElement;
             UseParentAsResultParent: Boolean): TPasFunctionType;
    function CreateInheritedExpr(AParent : TPasElement): TInheritedExpr;
    function CreateSelfExpr(AParent : TPasElement): TSelfExpr;
    function CreateNilExpr(AParent : TPasElement): TNilExpr;
    function CreateRecordValues(AParent : TPasElement): TRecordValues;
    Function IsCurTokenHint(out AHint : TPasMemberHint) : Boolean; overload;
    Function IsCurTokenHint: Boolean; overload;
    Function TokenIsCallingConvention(S : String; out CC : TCallingConvention) : Boolean; virtual;
    Function TokenIsProcedureModifier(Parent : TPasElement; S : String; Out Pm : TProcedureModifier) : Boolean; virtual;
    Function CheckHint(Element : TPasElement; ExpectSemiColon : Boolean) : TPasMemberHints;
    function ParseParams(AParent : TPasElement;paramskind: TPasExprKind): TParamsExpr;
    function ParseExpIdent(AParent : TPasElement): TPasExpr;
    procedure DoParseClassType(AType: TPasClassType);
    function DoParseExpression(AParent: TPaselement;InitExpr: TPasExpr=nil): TPasExpr;
    function DoParseConstValueExpression(AParent: TPasElement): TPasExpr;
    function CheckPackMode: TPackMode;
    function CheckUseUnit(ASection: TPasSection; AUnitName : string): TPasElement;
    procedure CheckImplicitUsedUnits(ASection: TPasSection);
    // Overload handling
    procedure AddProcOrFunction(Decs: TPasDeclarations; AProc: TPasProcedure);
    function  CheckIfOverloaded(AParent: TPasElement; const AName: String): TPasElement;
  public
    constructor Create(AScanner: TPascalScanner; AFileResolver: TBaseFileResolver;  AEngine: TPasTreeContainer);
    Destructor Destroy; override;
    procedure SetLastMsg(MsgType: TMessageType; MsgNumber: integer; Const Fmt : String; Args : Array of const);
    // General parsing routines
    function CurTokenName: String;
    function CurTokenText: String;
    Function CurComments : TStrings;
    Function SavedComments : String;
    procedure NextToken; // read next non whitespace, non space
    procedure UngetToken;
    procedure CheckToken(tk: TToken);
    procedure ExpectToken(tk: TToken);
    function ExpectIdentifier: String;
    Function CurTokenIsIdentifier(Const S : String) : Boolean;
    // Expression parsing
    function isEndOfExp: Boolean;
    // Type declarations
    function ParseComplexType(Parent : TPasElement = Nil): TPasType;
    function ParseTypeDecl(Parent: TPasElement): TPasType;
    function ParseType(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName : String = ''; Full : Boolean = False): TPasType;
    function ParseProcedureType(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName: String; const PT: TProcType): TPasProcedureType;
    function ParseStringType(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName: String): TPasAliasType;
    function ParseSimpleType(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName: String; IsFull : Boolean = False): TPasType;
    function ParseAliasType(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName: String): TPasTypeAliasType;
    function ParsePointerType(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName: String): TPasPointerType;
    Function ParseArrayType(Parent : TPasElement; Const NamePos: TPasSourcePos; Const TypeName : String; PackMode : TPackMode) : TPasArrayType;
    Function ParseFileType(Parent : TPasElement; Const NamePos: TPasSourcePos; Const TypeName  : String) : TPasFileType;
    Function ParseRecordDecl(Parent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName : string; const Packmode : TPackMode = pmNone) : TPasRecordType;
    function ParseEnumType(Parent: TPasElement; Const NamePos: TPasSourcePos; const TypeName: String): TPasEnumType;
    function ParseSetType(Parent: TPasElement; Const NamePos: TPasSourcePos; const TypeName: String ): TPasSetType;
    function ParseSpecializeType(Parent: TPasElement; Const TypeName: String): TPasClassType;
    Function ParseClassDecl(Parent: TPasElement; Const NamePos: TPasSourcePos; Const AClassName: String; AObjKind: TPasObjKind; PackMode : TPackMode= pmNone): TPasType;
    Function ParseProperty(Parent : TPasElement; Const AName : String; AVisibility : TPasMemberVisibility) : TPasProperty;
    function ParseRangeType(AParent: TPasElement; Const NamePos: TPasSourcePos; Const TypeName: String; Full: Boolean = True): TPasRangeType;
    procedure ParseExportDecl(Parent: TPasElement; List: TFPList);
    // Constant declarations
    function ParseConstDecl(Parent: TPasElement): TPasConst;
    function ParseResourcestringDecl(Parent: TPasElement): TPasResString;
    // Variable handling. This includes parts of records
    procedure ParseVarDecl(Parent: TPasElement; List: TFPList);
    procedure ParseInlineVarDecl(Parent: TPasElement; List: TFPList;  AVisibility : TPasMemberVisibility  = visDefault; ClosingBrace: Boolean = False);
    // Main scope parsing
    procedure ParseMain(var Module: TPasModule);
    procedure ParseUnit(var Module: TPasModule);
    procedure ParseProgram(var Module: TPasModule; SkipHeader : Boolean = False);
    procedure ParseLibrary(var Module: TPasModule);
    procedure ParseOptionalUsesList(ASection: TPasSection);
    procedure ParseUsesList(ASection: TPasSection);
    procedure ParseInterface;
    procedure ParseImplementation;
    procedure ParseInitialization;
    procedure ParseFinalization;
    procedure ParseDeclarations(Declarations: TPasDeclarations);
    procedure ParseStatement(Parent: TPasImplBlock;  out NewImplElement: TPasImplElement);
    procedure ParseLabels(AParent: TPasElement);
    procedure ParseProcBeginBlock(Parent: TProcedureBody);
    // Function/Procedure declaration
    function  ParseProcedureOrFunctionDecl(Parent: TPasElement; ProcType: TProcType;AVisibility : TPasMemberVisibility = VisDefault): TPasProcedure;
    procedure ParseArgList(Parent: TPasElement;
      Args: TFPList; // list of TPasArgument
      EndToken: TToken);
    procedure ParseProcedureOrFunctionHeader(Parent: TPasElement; Element: TPasProcedureType; ProcType: TProcType; OfObjectPossible: Boolean);
    procedure ParseProcedureBody(Parent: TPasElement);
    // Properties for external access
    property FileResolver: TBaseFileResolver read FFileResolver;
    property Scanner: TPascalScanner read FScanner;
    property Engine: TPasTreeContainer read FEngine;
    property CurToken: TToken read FCurToken;
    property CurTokenString: String read FCurTokenString;
    Property Options : TPOptions Read FOptions Write SetOptions;
    Property CurModule : TPasModule Read FCurModule;
    Property LogEvents : TPParserLogEvents Read FLogEvents Write FLogEvents;
    Property OnLog : TPasParserLogHandler Read FOnLog Write FOnLog;
    property ImplicitUses: TStrings read FImplicitUses;
    property LastMsg: string read FLastMsg write FLastMsg;
    property LastMsgNumber: integer read FLastMsgNumber write FLastMsgNumber;
    property LastMsgType: TMessageType read FLastMsgType write FLastMsgType;
    property LastMsgPattern: string read FLastMsgPattern write FLastMsgPattern;
    property LastMsgArgs: TMessageArgs read FLastMsgArgs write FLastMsgArgs;
  end;

function ParseSource(AEngine: TPasTreeContainer;
                     const FPCCommandLine, OSTarget, CPUTarget: String;
                     UseStreams  : Boolean = False): TPasModule;
Function IsHintToken(T : String; Out AHint : TPasMemberHint) : boolean;
Function IsModifier(S : String; Out Pm : TProcedureModifier) : Boolean;
Function IsCallingConvention(S : String; out CC : TCallingConvention) : Boolean;
Function TokenToAssignKind( tk : TToken) : TAssignKind;

implementation

const
  WhitespaceTokensToIgnore = [tkWhitespace, tkComment, tkLineEnding, tkTab];

type
  TDeclType = (declNone, declConst, declResourcestring, declType,
               declVar, declThreadvar, declProperty, declExports);

Function IsHintToken(T : String; Out AHint : TPasMemberHint) : boolean;

Const
   MemberHintTokens : Array[TPasMemberHint] of string =
     ('deprecated','library','platform','experimental','unimplemented');
Var
  I : TPasMemberHint;

begin
  t:=LowerCase(t);
  Result:=False;
  For I:=Low(TPasMemberHint) to High(TPasMemberHint) do
    begin
    result:=(t=MemberHintTokens[i]);
    if Result then
      begin
      aHint:=I;
      exit;
      end;
    end;
end;


Function IsCallingConvention(S : String; out CC : TCallingConvention) : Boolean;

Var
  CCNames : Array[TCallingConvention] of String
         = ('','register','pascal','cdecl','stdcall','oldfpccall','safecall','syscall');
Var
  C : TCallingConvention;

begin
  S:=Lowercase(s);
  Result:=False;
  for C:=Low(TCallingConvention) to High(TCallingConvention) do
    begin
    Result:=(CCNames[c]<>'') and (s=CCnames[c]);
    If Result then
      begin
      CC:=C;
      exit;
      end;
    end;
end;


Function IsModifier(S : String; Out Pm : TProcedureModifier) : Boolean;


Var
  P : TProcedureModifier;

begin
  S:=LowerCase(S);
  Result:=False;
  For P:=Low(TProcedureModifier) to High(TProcedureModifier) do
    begin
    Result:=s=ModifierNames[P];
    If Result then
      begin
      PM:=P;
      exit;
      end;
    end;
end;

Function TokenToAssignKind( tk : TToken) : TAssignKind;

begin
  case tk of
    tkAssign         : Result:=akDefault;
    tkAssignPlus     : Result:=akAdd;
    tkAssignMinus    : Result:=akMinus;
    tkAssignMul      : Result:=akMul;
    tkAssignDivision : Result:=akDivision;
  else
    Raise Exception.CreateFmt('Not an assignment token : %s',[TokenInfos[tk]]);
  end;
end;

function ParseSource(AEngine: TPasTreeContainer;
  const FPCCommandLine, OSTarget, CPUTarget: String;
  UseStreams  : Boolean = False): TPasModule;
var
  FileResolver: TFileResolver;
  Parser: TPasParser;
  Start, CurPos: PChar;
  Filename: String;
  Scanner: TPascalScanner;

  procedure ProcessCmdLinePart;
  var
    l: Integer;
    s: String;
  begin
    l := CurPos - Start;
    SetLength(s, l);
    if l > 0 then
      Move(Start^, s[1], l)
    else
      exit;
    if (s[1] = '-') and (length(s)>1) then
    begin
      case s[2] of
        'd': // -d define
          Scanner.AddDefine(UpperCase(Copy(s, 3, Length(s))));
        'F': // -F
          if (length(s)>2) and (s[3] = 'i') then // -Fi include path
            FileResolver.AddIncludePath(Copy(s, 4, Length(s)));
        'I': // -I include path
          FileResolver.AddIncludePath(Copy(s, 3, Length(s)));
        'S': // -S mode
          if  (length(s)>2) then
            case S[3] of
              'c' : Scanner.Options:=Scanner.Options+[po_cassignments];
              'd','2' : Parser.Options:=Parser.Options+[po_delphi];
            end;
      end;
    end else
      if Filename <> '' then
        raise Exception.Create(SErrMultipleSourceFiles)
      else
        Filename := s;
  end;

var
  s: String;
begin
  Result := nil;
  FileResolver := nil;
  Scanner := nil;
  Parser := nil;
  try
    FileResolver := TFileResolver.Create;
    FileResolver.UseStreams:=UseStreams;
    Scanner := TPascalScanner.Create(FileResolver);
    Scanner.AddDefine('FPK');
    Scanner.AddDefine('FPC');
    SCanner.LogEvents:=AEngine.ScannerLogEvents;
    SCanner.OnLog:=AEngine.Onlog;

    // TargetOS
    s := UpperCase(OSTarget);
    Scanner.AddDefine(s);
    if s = 'LINUX' then
      Scanner.AddDefine('UNIX')
    else if s = 'FREEBSD' then
    begin
      Scanner.AddDefine('BSD');
      Scanner.AddDefine('UNIX');
    end else if s = 'NETBSD' then
    begin
      Scanner.AddDefine('BSD');
      Scanner.AddDefine('UNIX');
    end else if s = 'SUNOS' then
    begin
      Scanner.AddDefine('SOLARIS');
      Scanner.AddDefine('UNIX');
    end else if s = 'GO32V2' then
      Scanner.AddDefine('DPMI')
    else if s = 'BEOS' then
      Scanner.AddDefine('UNIX')
    else if s = 'QNX' then
      Scanner.AddDefine('UNIX')
    else if s = 'AROS' then
      Scanner.AddDefine('HASAMIGA')
    else if s = 'MORPHOS' then
      Scanner.AddDefine('HASAMIGA')
    else if s = 'AMIGA' then
      Scanner.AddDefine('HASAMIGA');

    // TargetCPU
    s := UpperCase(CPUTarget);
    Scanner.AddDefine('CPU'+s);
    if (s='x86_64') then
      Scanner.AddDefine('CPU64')
    else
      Scanner.AddDefine('CPU32');

    Parser := TPasParser.Create(Scanner, FileResolver, AEngine);
    Filename := '';
    Parser.LogEvents:=AEngine.ParserLogEvents;
    Parser.OnLog:=AEngine.Onlog;

    if FPCCommandLine<>'' then
      begin
        Start := @FPCCommandLine[1];
        CurPos := Start;
        while CurPos[0] <> #0 do
        begin
          if CurPos[0] = ' ' then
          begin
            ProcessCmdLinePart;
            Start := CurPos + 1;
          end;
          Inc(CurPos);
        end;
        ProcessCmdLinePart;
      end;

    if Filename = '' then
      raise Exception.Create(SErrNoSourceGiven);
    FileResolver.AddIncludePath(ExtractFilePath(FileName));
    Scanner.OpenFile(Filename);
    Parser.ParseMain(Result);
  finally
    Parser.Free;
    Scanner.Free;
    FileResolver.Free;
  end;
end;

{ ---------------------------------------------------------------------
  TPasTreeContainer
  ---------------------------------------------------------------------}

procedure TPasTreeContainer.SetCurrentParser(AValue: TPasParser);
begin
  if FCurrentParser=AValue then Exit;
  FCurrentParser:=AValue;
end;

function TPasTreeContainer.CreateElement(AClass: TPTreeElement;
  const AName: String; AParent: TPasElement; const ASourceFilename: String;
  ASourceLinenumber: Integer): TPasElement;
begin
  Result := CreateElement(AClass, AName, AParent, visDefault, ASourceFilename,
    ASourceLinenumber);
end;

function TPasTreeContainer.CreateElement(AClass: TPTreeElement;
  const AName: String; AParent: TPasElement; AVisibility: TPasMemberVisibility;
  const ASrcPos: TPasSourcePos): TPasElement;
begin
  Result := CreateElement(AClass, AName, AParent, AVisibility, ASrcPos.FileName,
    ASrcPos.Row);
end;

function TPasTreeContainer.CreateFunctionType(const AName, AResultName: String;
  AParent: TPasElement; UseParentAsResultParent: Boolean;
  const ASrcPos: TPasSourcePos): TPasFunctionType;
var
  ResultParent: TPasElement;
begin
  Result := TPasFunctionType(CreateElement(TPasFunctionType, AName, AParent,
    visDefault, ASrcPos));

  if UseParentAsResultParent then
    ResultParent := AParent
  else
    ResultParent := Result;

  TPasFunctionType(Result).ResultEl :=
    TPasResultElement(CreateElement(TPasResultElement, AResultName, ResultParent,
    visDefault, ASrcPos));
end;

procedure TPasTreeContainer.FinishScope(ScopeType: TPasScopeType;
  El: TPasElement);
begin
  if ScopeType=stModule then ;
  if El=nil then ;
end;

function TPasTreeContainer.FindModule(const AName: String): TPasModule;
begin
  if AName='' then ;
  Result := nil;
end;

{ ---------------------------------------------------------------------
  EParserError
  ---------------------------------------------------------------------}

constructor EParserError.Create(const AReason, AFilename: String;
  ARow, AColumn: Integer);
begin
  inherited Create(AReason);
  FFilename := AFilename;
  FRow := ARow;
  FColumn := AColumn;
end;

{ ---------------------------------------------------------------------
  TPasParser
  ---------------------------------------------------------------------}

procedure TPasParser.ParseExc(MsgNumber: integer; const Msg: String);
begin
  ParseExc(MsgNumber,Msg,[]);
end;

procedure TPasParser.ParseExc(MsgNumber: integer; const Fmt: String;
  Args: array of const);
begin
  SetLastMsg(mtError,MsgNumber,Fmt,Args);
  raise EParserError.Create(Format(SParserErrorAtToken,
    [FLastMsg, CurTokenName, Scanner.CurFilename, Scanner.CurRow, Scanner.CurColumn])
    {$ifdef addlocation}+' ('+inttostr(scanner.currow)+' '+inttostr(scanner.curcolumn)+')'{$endif},
    Scanner.CurFilename, Scanner.CurRow, Scanner.CurColumn);
end;

procedure TPasParser.ParseExcExpectedIdentifier;
begin
  ParseExc(nParserExpectedIdentifier,SParserExpectedIdentifier);
end;

procedure TPasParser.ParseExcSyntaxError;
begin
  ParseExc(nParserSyntaxError,SParserSyntaxError);
end;

procedure TPasParser.ParseExcTokenError(const Arg: string);
begin
  ParseExc(nParserExpectTokenError,SParserExpectTokenError,[Arg]);
end;

constructor TPasParser.Create(AScanner: TPascalScanner;
  AFileResolver: TBaseFileResolver; AEngine: TPasTreeContainer);
begin
  inherited Create;
  FScanner := AScanner;
  FFileResolver := AFileResolver;
  FEngine := AEngine;
  FCommentsBuffer[0]:=TStringList.Create;
  FCommentsBuffer[1]:=TStringList.Create;
  if Assigned(FEngine) then
    begin
    FEngine.CurrentParser:=Self;
    If FEngine.NeedComments then
      FScanner.SkipComments:=Not FEngine.NeedComments;
    end;
  FImplicitUses := TStringList.Create;
  FImplicitUses.Add('System'); // system always implicitely first.
end;

destructor TPasParser.Destroy;
begin
  if Assigned(FEngine) then
    begin
    FEngine.CurrentParser:=Nil;
    FEngine:=nil;
    end;
  FreeAndNil(FImplicitUses);
  FreeAndNil(FCommentsBuffer[0]);
  FreeAndNil(FCommentsBuffer[1]);
  inherited Destroy;
end;

function TPasParser.CurTokenName: String;
begin
  if CurToken = tkIdentifier then
    Result := 'Identifier ' + FCurTokenString
  else
    Result := TokenInfos[CurToken];
end;

function TPasParser.CurTokenText: String;
begin
  case CurToken of
    tkIdentifier, tkString, tkNumber, tkChar:
      Result := FCurTokenString;
    else
      Result := TokenInfos[CurToken];
  end;
end;

function TPasParser.CurComments: TStrings;
begin
  Result:=FCurComments;
end;

function TPasParser.SavedComments: String;
begin
  Result:=FSavedComments;
end;

procedure TPasParser.NextToken;

Var
  T : TStrings;
begin
  if FTokenBufferIndex < FTokenBufferSize then
  begin
    // Get token from buffer
    FCurToken := FTokenBuffer[FTokenBufferIndex];
    FCurTokenString := FTokenStringBuffer[FTokenBufferIndex];
    FCurComments:=FCommentsBuffer[FTokenBufferIndex];
    Inc(FTokenBufferIndex);
    //writeln('TPasParser.NextToken From Buf ',CurTokenText,' id=',FTokenBufferIndex);
  end else
  begin
    { We have to fetch a new token. But first check, wether there is space left
      in the token buffer.}
    if FTokenBufferSize = 2 then
      begin
      FTokenBuffer[0] := FTokenBuffer[1];
      FTokenStringBuffer[0] := FTokenStringBuffer[1];
      T:=FCommentsBuffer[0];
      FCommentsBuffer[0]:=FCommentsBuffer[1];
      FCommentsBuffer[1]:=T;
      Dec(FTokenBufferSize);
      Dec(FTokenBufferIndex);
      end;
    // Fetch new token
    try
      FCommentsBuffer[FTokenBufferSize].Clear;
      repeat
        FCurToken := Scanner.FetchToken;
        if FCurToken=tkComment then
          FCommentsBuffer[FTokenBufferSize].Add(Scanner.CurTokenString);
      until not (FCurToken in WhitespaceTokensToIgnore);
    except
      on e: EScannerError do
        raise EParserError.Create(e.Message,
          Scanner.CurFilename, Scanner.CurRow, Scanner.CurColumn);
    end;
    FCurTokenString := Scanner.CurTokenString;
    FTokenBuffer[FTokenBufferSize] := FCurToken;
    FTokenStringBuffer[FTokenBufferSize] := FCurTokenString;
    FCurComments:=FCommentsBuffer[FTokenBufferSize];
    Inc(FTokenBufferSize);
    Inc(FTokenBufferIndex);
  //  writeln('TPasParser.NextToken New ',CurTokenText,' id=',FTokenBufferIndex,' comments = ',FCurComments.text);
  end;
end;

procedure TPasParser.UngetToken;

begin
  if FTokenBufferIndex = 0 then
    ParseExc(nParserUngetTokenError,SParserUngetTokenError)
  else begin
    Dec(FTokenBufferIndex);
    if FTokenBufferIndex>0 then
    begin
      FCurToken := FTokenBuffer[FTokenBufferIndex-1];
      FCurTokenString := FTokenStringBuffer[FTokenBufferIndex-1];
      FCurComments:=FCommentsBuffer[FTokenBufferIndex-1];
    end else begin
      FCurToken := tkWhitespace;
      FCurTokenString := '';
      FCurComments.Clear;
    end;
    //writeln('TPasParser.UngetToken ',CurTokenText,' id=',FTokenBufferIndex);
  end;
end;

procedure TPasParser.CheckToken(tk: TToken);
begin
  if (CurToken<>tk) then
    ParseExcTokenError(TokenInfos[tk]);
end;


procedure TPasParser.ExpectToken(tk: TToken);
begin
  NextToken;
  CheckToken(tk);
end;

function TPasParser.ExpectIdentifier: String;
begin
  ExpectToken(tkIdentifier);
  Result := CurTokenString;
end;

function TPasParser.CurTokenIsIdentifier(const S: String): Boolean;
begin
  Result:=(Curtoken=tkidentifier) and (CompareText(S,CurtokenText)=0);
end;


function TPasParser.IsCurTokenHint(out AHint: TPasMemberHint): Boolean;
begin
  Result:=CurToken=tklibrary;
  if Result then
    AHint:=hLibrary
  else if (CurToken=tkIdentifier) then
    Result:=IsHintToken(CurTokenString,ahint);
end;

function TPasParser.IsCurTokenHint: Boolean;
var
  dummy : TPasMemberHint;
begin
  Result:=IsCurTokenHint(dummy);
end;

function TPasParser.TokenIsCallingConvention(S: String; out
  CC: TCallingConvention): Boolean;
begin
  Result:=IsCallingConvention(S,CC);
end;

function TPasParser.TokenIsProcedureModifier(Parent: TPasElement; S: String;
  out Pm: TProcedureModifier): Boolean;
begin
  Result:=IsModifier(S,PM);
  if result and (pm in [pmPublic,pmForward]) then
    begin
    While (Parent<>Nil) and Not ((Parent is TPasClassType) or (Parent is TPasRecordType)) do
      Parent:=Parent.Parent;
    Result:=Not Assigned(Parent);
    end;
end;


function TPasParser.CheckHint(Element: TPasElement; ExpectSemiColon: Boolean
  ): TPasMemberHints;

Var
  Found : Boolean;
  h : TPasMemberHint;
  
begin
  Result:=[];
  Repeat
    NextToken;
    Found:=IsCurTokenHint(h);
    If Found then
      begin
      Include(Result,h);
      if (h=hDeprecated) then
        begin
        NextToken;
        if (Curtoken<>tkString) then
          UnGetToken
        else
          Element.HintMessage:=CurTokenString;
        end;
      end;
  Until Not Found;
  UnGetToken;
  If Assigned(Element) then
    Element.Hints:=Result;
  if ExpectSemiColon then
    ExpectToken(tkSemiColon);
end;

function TPasParser.CheckPackMode: TPackMode;

begin
  NextToken;
  Case CurToken of
    tkPacked    : Result:=pmPacked;
    tkbitpacked : Result:=pmBitPacked;
  else
    result:=pmNone;
  end;
  if (Result<>pmNone) then
     begin
     NextToken;
     if Not (CurToken in [tkArray, tkRecord, tkObject, tkClass]) then
       ParseExcTokenError('ARRAY, RECORD, OBJECT or CLASS');
     end;
end;

Function IsSimpleTypeToken(Var AName : String) : Boolean;

Const
   SimpleTypeCount = 15;
   SimpleTypeNames : Array[1..SimpleTypeCount] of string =
     ('byte','boolean','char','integer','int64','longint','longword','double',
      'shortint','smallint','string','word','qword','cardinal','widechar');
   SimpleTypeCaseNames : Array[1..SimpleTypeCount] of string =
     ('Byte','Boolean','Char','Integer','Int64','LongInt','LongWord','Double',
     'ShortInt','SmallInt','String','Word','QWord','Cardinal','WideChar');

Var
  S : String;
  I : Integer;

begin
  S:=LowerCase(AName);
  I:=SimpleTypeCount;
  While (I>0) and (s<>SimpleTypeNames[i]) do
    Dec(I);
  Result:=(I>0);
  if Result Then
    AName:=SimpleTypeCaseNames[I];
end;

function TPasParser.ParseStringType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String): TPasAliasType;

Var
  S : String;
  ok: Boolean;

begin
  Result := TPasAliasType(CreateElement(TPasAliasType, TypeName, Parent, NamePos));
  ok:=false;
  try
    If (Result.Name='') then
      Result.Name:='string';
    NextToken;
    if CurToken=tkSquaredBraceOpen then
      begin
      S:='';
      NextToken;
      While Not (Curtoken in [tkSquaredBraceClose,tkEOF]) do
        begin
        S:=S+CurTokenString;
        NextToken;
        end;
      end
    else
      UngetToken;
    Result.DestType:=TPasStringType(CreateElement(TPasStringType,'string',Parent));
    TPasStringType(Result.DestType).LengthExpr:=S;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.ParseSimpleType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String; IsFull: Boolean
  ): TPasType;

Type
  TSimpleTypeKind = (stkAlias,stkString,stkRange);

Var
  Ref: TPasElement;
  K : TSimpleTypeKind;
  Name : String;
  SS : Boolean;
begin
  Name := CurTokenString;
  NextToken;
  while CurToken=tkDot do
    begin
    ExpectIdentifier;
    Name := Name+'.'+CurTokenString;
    NextToken;
    end;
  // Current token is first token after identifier.
  if IsFull then
    begin
    if (CurToken=tkSemicolon) or isCurTokenHint then // Type A = B;
      K:=stkAlias
    else if (CurToken=tkSquaredBraceOpen) then
      begin
      // Todo: check via resolver
      if ((LowerCase(Name)='string') or (LowerCase(Name)='ansistring')) then // Type A = String[12];
        K:=stkString
      else
        ParseExcSyntaxError;
      end
    else if CurToken=tkDotDot then // Type A = A..B;
      K:=stkRange
    else
      ParseExcTokenError(';');
    UnGetToken;
    end
  else if (CurToken=tkDotDot) then // A: B..C;
    begin
    K:=stkRange;
    UnGetToken;
    end
  else
    begin
    UnGetToken;
    K:=stkAlias;
    if (not (po_resolvestandardtypes in Options)) and (LowerCase(Name)='string') then
      K:=stkString;
    end;
  Case K of
    stkString:
      begin
      Result:=ParseStringType(Parent,NamePos,TypeName);
      end;
    stkRange:
      begin
      UnGetToken;
      Result:=ParseRangeType(Parent,NamePos,TypeName,False);
      end;
    stkAlias:
      begin
      Ref:=Nil;
      SS:=(not (po_resolvestandardtypes in FOptions)) and isSimpleTypeToken(Name);
      if not SS then
        begin
        Ref:=Engine.FindElement(Name);
        if Ref=nil then
          begin
          {$IFDEF VerbosePasResolver}
          if po_resolvestandardtypes in FOptions then
            begin
            writeln('ERROR: TPasParser.ParseSimpleType resolver failed to raise an error');
            ParseExcExpectedIdentifier;
            end;
          {$ENDIF}
          end
        else if not (Ref is TPasType) then
          ParseExc(nParserExpectedTypeButGot,SParserExpectedTypeButGot,[Ref.ElementTypeName]);
        end;
      if (Ref=Nil) then
        Ref:=TPasUnresolvedTypeRef(CreateElement(TPasUnresolvedTypeRef,Name,Parent))
      else
        Ref.AddRef;
      if isFull then
        begin
        Result := TPasAliasType(CreateElement(TPasAliasType, TypeName, Parent, NamePos));
        TPasAliasType(Result).DestType:=Ref as TPasType;
        end
      else
        Result:=Ref as TPasType
      end;
  end;
end;

// On entry, we're on the TYPE token
function TPasParser.ParseAliasType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String): TPasTypeAliasType;
var
  ok: Boolean;
begin
  Result := TPasTypeAliasType(CreateElement(TPasTypeAliasType, TypeName, Parent, NamePos));
  ok:=false;
  try
    Result.DestType := ParseType(Result,NamePos,'');
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.ParsePointerType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String): TPasPointerType;

var
  ok: Boolean;
begin
  Result := TPasPointerType(CreateElement(TPasPointerType, TypeName, Parent, NamePos));
  ok:=false;
  Try
    TPasPointerType(Result).DestType := ParseType(Result,Scanner.CurSourcePos);
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.ParseEnumType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String): TPasEnumType;

Var
  EnumValue: TPasEnumValue;
  ok: Boolean;

begin
  Result := TPasEnumType(CreateElement(TPasEnumType, TypeName, Parent, NamePos));
  ok:=false;
  try
    while True do
      begin
      NextToken;
      SaveComments;
      EnumValue := TPasEnumValue(CreateElement(TPasEnumValue, CurTokenString, Result));
      Result.Values.Add(EnumValue);
      NextToken;
      if CurToken = tkBraceClose then
        break
      else if CurToken in [tkEqual,tkAssign] then
        begin
        NextToken;
        EnumValue.Value:=DoParseExpression(Result);
       // UngetToken;
        if CurToken = tkBraceClose then
          Break
        else if not (CurToken=tkComma) then
          ParseExc(nParserExpectedCommaRBracket,SParserExpectedCommaRBracket);
        end
      else if not (CurToken=tkComma) then
        ParseExc(nParserExpectedCommaRBracket,SParserExpectedCommaRBracket)
      end;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
  Engine.FinishScope(stTypeDef,Result);
end;

function TPasParser.ParseSetType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String): TPasSetType;

var
  ok: Boolean;
begin
  Result := TPasSetType(CreateElement(TPasSetType, TypeName, Parent, NamePos));
  ok:=false;
  try
    ExpectToken(tkOf);
    Result.EnumType := ParseType(Result,Scanner.CurSourcePos);
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
  Engine.FinishScope(stTypeDef,Result);
end;

function TPasParser.ParseType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String; Full: Boolean
  ): TPasType;

Const
  // These types are allowed only when full type declarations
  FullTypeTokens = [tkGeneric,{tkSpecialize,}tkClass,tkInterface,tkType];
  // Parsing of these types already takes care of hints
  NoHintTokens = [tkProcedure,tkFunction];
var
  PM : TPackMode;
  CH , ok: Boolean; // Check hint ?
begin
  Result := nil;
  // NextToken and check pack mode
  Pm:=CheckPackMode;
  if Full then
    CH:=Not (CurToken in NoHintTokens)
  else
    begin
    CH:=False;
    if (CurToken in FullTypeTokens) then
      ParseExc(nParserTypeNotAllowedHere,SParserTypeNotAllowedHere,[CurtokenText]);
    end;
  ok:=false;
  Try
    case CurToken of
      // types only allowed when full
      tkObject: Result := ParseClassDecl(Parent, NamePos, TypeName, okObject,PM);
      tkInterface: Result := ParseClassDecl(Parent, NamePos, TypeName, okInterface);
      tkSpecialize: Result:=ParseSpecializeType(Parent,TypeName);
      tkClass: Result := ParseClassDecl(Parent, NamePos, TypeName, okClass, PM);
      tkType: Result:=ParseAliasType(Parent,NamePos,TypeName);
      // Always allowed
      tkIdentifier: Result:=ParseSimpleType(Parent,NamePos,TypeName,Full);
      tkCaret: Result:=ParsePointerType(Parent,NamePos,TypeName);
      tkFile: Result:=ParseFileType(Parent,NamePos,TypeName);
      tkArray: Result:=ParseArrayType(Parent,NamePos,TypeName,pm);
      tkBraceOpen: Result:=ParseEnumType(Parent,NamePos,TypeName);
      tkSet: Result:=ParseSetType(Parent,NamePos,TypeName);
      tkProcedure: Result:=ParseProcedureType(Parent,NamePos,TypeName,ptProcedure);
      tkFunction: Result:=ParseProcedureType(Parent,NamePos,TypeName,ptFunction);
      tkRecord:
        begin
        NextToken;
        if (Curtoken=tkHelper) then
          begin
          UnGetToken;
          Result:=ParseClassDecl(Parent,NamePos,TypeName,okRecordHelper,PM);
          end
        else
          begin
          UnGetToken;
          Result := ParseRecordDecl(Parent,NamePos,TypeName,PM);
          end;
        end;
      tkNumber,tkMinus:
        begin
        UngetToken;
        Result:=ParseRangeType(Parent,NamePos,TypeName,Full);
        end;
    else
      ParseExcExpectedIdentifier;
    end;
    if CH then
      CheckHint(Result,True);
    ok:=true;
  finally
    if not ok then
      if Result<>nil then
        Result.Release;
  end;
end;

function TPasParser.ParseComplexType(Parent : TPasElement = Nil): TPasType;
begin
  NextToken;
  case CurToken of
    tkProcedure:
      begin
        Result := TPasProcedureType(CreateElement(TPasProcedureType, '', Parent));
        ParseProcedureOrFunctionHeader(Result, TPasProcedureType(Result), ptProcedure, True);
        if CurToken = tkSemicolon then
          UngetToken;        // Unget semicolon
      end;
    tkFunction:
      begin
        Result := CreateFunctionType('', 'Result', Parent, False);
        ParseProcedureOrFunctionHeader(Result, TPasFunctionType(Result), ptFunction, True);
        if CurToken = tkSemicolon then
          UngetToken;        // Unget semicolon
      end;
  else
    UngetToken;
    Result := ParseType(Parent,Scanner.CurSourcePos);
  end;
end;

function TPasParser.ParseArrayType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String; PackMode: TPackMode
  ): TPasArrayType;

Var
  S : String;
  ok: Boolean;

begin
  Result := TPasArrayType(CreateElement(TPasArrayType, TypeName, Parent, NamePos));
  ok:=false;
  try
    Result.PackMode:=PackMode;
    NextToken;
    S:='';
    case CurToken of
      tkSquaredBraceOpen:
        begin
          repeat
            NextToken;
            if CurToken<>tkSquaredBraceClose then
              S:=S+CurTokenText;
          until CurToken = tkSquaredBraceClose;
          Result.IndexRange:=S;
          ExpectToken(tkOf);
          Result.ElType := ParseType(Result,Scanner.CurSourcePos);
        end;
      tkOf:
        begin
          NextToken;
          if CurToken = tkConst then
          else
          begin
            UngetToken;
              Result.ElType := ParseType(Result,Scanner.CurSourcePos);
          end
        end
      else
        ParseExc(nParserArrayTypeSyntaxError,SParserArrayTypeSyntaxError);
    end;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.ParseFileType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String): TPasFileType;
begin
  Result:=TPasFileType(CreateElement(TPasFileType, TypeName, Parent, NamePos));
  NextToken;
  If CurToken=tkOf then
    Result.ElType := ParseType(Result,Scanner.CurSourcePos)
  else 
   ungettoken;
end;

function TPasParser.isEndOfExp:Boolean;
const
  EndExprToken = [
    tkEOF, tkBraceClose, tkSquaredBraceClose, tkSemicolon, tkComma, tkColon,
    tkdo, tkdownto, tkelse, tkend, tkof, tkthen, tkto
  ];
begin
  Result:=(CurToken in EndExprToken) or IsCurTokenHint;
end;

function TPasParser.ParseParams(AParent: TPasElement;paramskind: TPasExprKind): TParamsExpr;
var
  params  : TParamsExpr;
  p       : TPasExpr;
  PClose  : TToken;
begin
  Result:=nil;
  if paramskind in [pekArrayParams, pekSet] then begin
    if CurToken<>tkSquaredBraceOpen then Exit;
    PClose:=tkSquaredBraceClose;
  end else begin
    if CurToken<>tkBraceOpen then Exit;
    PClose:=tkBraceClose;
  end;

  params:=TParamsExpr(CreateElement(TParamsExpr,'',AParent));
  try
    params.Kind:=paramskind;
    NextToken;
    if not isEndOfExp then begin
      repeat
        p:=DoParseExpression(params);
        if not Assigned(p) then Exit; // bad param syntax
        params.AddParam(p);

        if not (CurToken in [tkComma, PClose]) then begin
          Exit;
        end;

        if CurToken = tkComma then begin
          NextToken;
          if CurToken = PClose then begin
            //ErrorExpected(parser, 'identifier');
            Exit;
          end;
        end;
      until CurToken=PClose;
    end;
    NextToken;
    Result:=params;
  finally
    if not Assigned(Result) then params.Release;
  end;
end;

function TPasParser.TokenToExprOp(AToken: TToken): TExprOpCode;

begin
  Case AToken of
    tkMul                   : Result:=eopMultiply;
    tkPlus                  : Result:=eopAdd;
    tkMinus                 : Result:=eopSubtract;
    tkDivision              : Result:=eopDivide;
    tkLessThan              : Result:=eopLessThan;
    tkEqual                 : Result:=eopEqual;
    tkGreaterThan           : Result:=eopGreaterThan;
    tkAt                    : Result:=eopAddress;
    tkNotEqual              : Result:=eopNotEqual;
    tkLessEqualThan         : Result:=eopLessthanEqual;
    tkGreaterEqualThan      : Result:=eopGreaterThanEqual;
    tkPower                 : Result:=eopPower;
    tkSymmetricalDifference : Result:=eopSymmetricalDifference;                                                                                              
    tkIs                    : Result:=eopIs;
    tkAs                    : Result:=eopAs;
    tkSHR                   : Result:=eopSHR;
    tkSHL                   : Result:=eopSHL;
    tkAnd                   : Result:=eopAnd;
    tkOr                    : Result:=eopOR;
    tkXor                   : Result:=eopXOR;
    tkMod                   : Result:=eopMod;
    tkDiv                   : Result:=eopDiv;
    tkNot                   : Result:=eopNot;
    tkIn                    : Result:=eopIn;
    tkDot                   : Result:=eopSubIdent;
    tkCaret                 : Result:=eopDeref;
  else
    ParseExc(nParserNotAnOperand,SParserNotAnOperand,[AToken,TokenInfos[AToken]]);
  end;
end;
 
function TPasParser.ParseExpIdent(AParent: TPasElement): TPasExpr;
var
  Last    , Expr: TPasExpr;
  prm     : TParamsExpr;
  b       : TBinaryExpr;
  optk    : TToken;
  ok: Boolean;
begin
  Result:=nil;
  case CurToken of
    tkString:           Last:=CreatePrimitiveExpr(AParent,pekString,CurTokenString);
    tkChar:             Last:=CreatePrimitiveExpr(AParent,pekString, CurTokenText);
    tkNumber:           Last:=CreatePrimitiveExpr(AParent,pekNumber, CurTokenString);
    tkIdentifier:       Last:=CreatePrimitiveExpr(AParent,pekIdent, CurTokenText);
    tkfalse, tktrue:    Last:=CreateBoolConstExpr(Aparent,pekBoolConst, CurToken=tktrue);
    tknil:              Last:=CreateNilExpr(AParent);
    tkSquaredBraceOpen: Last:=ParseParams(AParent,pekSet);
    tkinherited:
      begin
      //inherited; inherited function
      Last:=CreateInheritedExpr(AParent);
      NextToken;
      if (CurToken=tkIdentifier) then
        begin
        b:=CreateBinaryExpr(AParent,Last, DoParseExpression(AParent), eopNone);
        if not Assigned(b.right) then
          begin
          B.Release;
          Exit; // error
          end;
        Last:=b;
        UngetToken;
        end
      else
        UngetToken;
      end;
    tkself:
      begin
      //Last:=CreatePrimitiveExpr(AParent,pekString, CurTokenText); //function(self);
      Last:=CreateSelfExpr(AParent);
      NextToken;
      if CurToken = tkDot then
        begin // self.Write(EscapeText(AText));
        optk:=CurToken;
        NextToken;
        b:=CreateBinaryExpr(AParent,Last, ParseExpIdent(AParent), TokenToExprOp(optk));
        if not Assigned(b.right) then
          begin
          B.Release;
          Exit; // error
          end;
        Last:=b;
        end;
      UngetToken;
      end;
    tkAt:
      begin
      // P:=@function;
      NextToken;
      if (length(CurTokenText)=0) or not (CurTokenText[1] in ['A'..'_']) then
        begin
        UngetToken;
        ParseExcExpectedIdentifier;
        end;
      Last:=CreatePrimitiveExpr(AParent,pekString, '@'+CurTokenText);
      end;
    tkCaret:
      begin
      // ^A..^_ characters. See #16341
      NextToken;
      if not (length(CurTokenText)=1) or not (CurTokenText[1] in ['A'..'_']) then
        begin
        UngetToken;
        ParseExcExpectedIdentifier;
        end;
      Last:=CreatePrimitiveExpr(AParent,pekString, '^'+CurTokenText);
      end;
  else
    ParseExcExpectedIdentifier;
  end;

  Result:=Last;

  if Last.Kind<>pekSet then NextToken;

  ok:=false;
  try
    if Last.Kind=pekIdent then
      begin
      while CurToken in [tkDot] do
        begin
        NextToken;
        if CurToken=tkIdentifier then
          begin
          AddToBinaryExprChain(Result,Last,
            CreatePrimitiveExpr(AParent,pekIdent,CurTokenString), eopSubIdent);
          NextToken;
          end
        else
          begin
          UngetToken;
          ParseExcExpectedIdentifier;
          end;
        end;
      repeat
        case CurToken of
          tkBraceOpen,tkSquaredBraceOpen:
            begin
            if CurToken=tkBraceOpen then
              prm:=ParseParams(AParent,pekFuncParams)
            else
              prm:=ParseParams(AParent,pekArrayParams);
            if not Assigned(prm) then Exit;
            AddParamsToBinaryExprChain(Result,Last,prm);
            end;
          tkCaret:
            begin
            Result:=CreateUnaryExpr(AParent,Result,TokenToExprOp(CurToken));
            Last:=Result;
            NextToken;
            end;
          else
            break;
          end;
      until false;
      // Needed for TSDOBaseDataObjectClass(Self.ClassType).Create
      if CurToken in [tkdot,tkas] then
        begin
        optk:=CurToken;
        NextToken;
        Expr:=ParseExpIdent(AParent);
        if Expr=nil then
          Exit; // error
        AddToBinaryExprChain(Result,Last,Expr,TokenToExprOp(optk));
      end;
    end;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.OpLevel(t: TToken): Integer;
begin
  case t of
  //  tkDot:
  //    Result:=5;
    tknot,tkAt:
      Result:=4;
    tkMul, tkDivision, tkdiv, tkmod, tkand, tkShl,tkShr, tkas, tkPower :
      Result:=3;
    tkPlus, tkMinus, tkor, tkxor:
      Result:=2;
    tkEqual, tkNotEqual, tkLessThan, tkLessEqualThan, tkGreaterThan, tkGreaterEqualThan, tkin, tkis:
      Result:=1;
  else
    Result:=0;
  end;
end;

function TPasParser.DoParseExpression(AParent : TPaselement;InitExpr: TPasExpr): TPasExpr;
var
  expstack  : TFPList;
  opstack   : array of TToken;
  opstackTop: integer;
  pcount    : Integer;
  x         : TPasExpr;
  i         : Integer;
  tempop    : TToken;
  NotBinary : Boolean;
  
const
  PrefixSym = [tkPlus, tkMinus, tknot, tkAt]; // + - not @
  BinaryOP  = [tkMul, tkDivision, tkdiv, tkmod,  tkDotDot,
               tkand, tkShl,tkShr, tkas, tkPower,
               tkPlus, tkMinus, tkor, tkxor, tkSymmetricalDifference,
               tkEqual, tkNotEqual, tkLessThan, tkLessEqualThan,
               tkGreaterThan, tkGreaterEqualThan, tkin, tkis];

  function PopExp: TPasExpr; inline;
  begin
    if expstack.Count>0 then begin
      Result:=TPasExpr(expstack[expstack.Count-1]);
      expstack.Delete(expstack.Count-1);
    end else
      Result:=nil;
  end;

  procedure PushOper(token: TToken); inline;
  begin
    inc(opstackTop);
    if opstackTop=length(opstack) then
      SetLength(opstack,length(opstack)*2+4);
    opstack[opstackTop]:=token;
  end;

  function PeekOper: TToken; inline;
  begin
    if opstackTop>=0 then Result:=opstack[opstackTop]
    else Result:=tkEOF;
  end;

  function PopOper: TToken; inline;
  begin
    Result:=PeekOper;
    if Result<>tkEOF then dec(opstackTop);
  end;

  procedure PopAndPushOperator;
  var
    t       : TToken;
    xright  : TPasExpr;
    xleft   : TPasExpr;
    bin     : TBinaryExpr;
  begin
    t:=PopOper;
    xright:=PopExp;
    xleft:=PopExp;
    if t=tkDotDot then
      begin
      bin:=CreateBinaryExpr(AParent,xleft,xright,eopNone);
      bin.Kind:=pekRange;
      end
    else
      bin:=CreateBinaryExpr(AParent,xleft,xright,TokenToExprOp(t));
    expstack.Add(bin);
  end;

begin
  //DumpCurToken('Entry',iaIndent);
  Result:=nil;
  expstack := TFPList.Create;
  SetLength(opstack,4);
  opstackTop:=-1;
  try
    repeat
      NotBinary:=True;
      pcount:=0;
      if not Assigned(InitExpr) then
        begin
        // the first part of the expression has been parsed externally.
        // this is used by Constant Expression parser (CEP) parsing only,
        // whenever it makes a false assuming on constant expression type.
        // i.e: SI_PAD_SIZE = ((128/sizeof(longint)) - 3);
        //
        // CEP assumes that it's array or record, because the expression
        // starts with "(". After the first part is parsed, the CEP meets "-"
        // that assures, it's not an array expression. The CEP should give the
        // first part back to the expression parser, to get the correct
        // token tree according to the operations priority.
        //
        // quite ugly. type information is required for CEP to work clean

        while CurToken in PrefixSym do
          begin
          PushOper(CurToken);
          inc(pcount);
          NextToken;
          end;

        if (CurToken = tkBraceOpen) then
          begin
          NextToken;
          x:=DoParseExpression(AParent);
          if CurToken<>tkBraceClose then
            begin
            x.Release;
            Exit;
            end;
          NextToken;
          //     DumpCurToken('Here 1');
               // for the expression like  (TObject(m)).Free;
               if (x<>Nil) and (CurToken=tkDot) then
                 begin
                 NextToken;
          //       DumpCurToken('Here 2');
                 x:=CreateBinaryExpr(AParent,x, ParseExpIdent(AParent), TokenToExprOp(tkDot));
          //       DumpCurToken('Here 3');
                 end;

          end
        else
          begin
          x:=ParseExpIdent(AParent);
          end;
        if not Assigned(x) then
          Exit;
        expstack.Add(x);

        for i:=1 to pcount do
          begin
          tempop:=PopOper;
          x:=popexp;
          if (tempop=tkMinus) and (x.Kind=pekRange) then
            begin
            TBinaryExpr(x).Left:=CreateUnaryExpr(x, TBinaryExpr(x).left, eopSubtract);
            expstack.Add(x);
            end
          else
            expstack.Add(CreateUnaryExpr(AParent, x, TokenToExprOp(tempop) ));
          end;
        end
      else
        begin
        expstack.Add(InitExpr);
        InitExpr:=nil;
        end;
      if (CurToken in BinaryOP) then
        begin
        // Adjusting order of the operations
        NotBinary:=False;
        tempop:=PeekOper;
        while (opstackTop>=0) and (OpLevel(tempop)>=OpLevel(CurToken)) do begin
          PopAndPushOperator;
          tempop:=PeekOper;
        end;
        PushOper(CurToken);
        NextToken;
        end;
      // Writeln('Bin ',NotBinary ,' or EOE ',isEndOfExp, ' Ex ',Assigned(x),' stack ',ExpStack.Count);
    until NotBinary or isEndOfExp;

    if not NotBinary then ParseExcExpectedIdentifier;

    while opstackTop>=0 do PopAndPushOperator;

    // only 1 expression should be on the stack, at the end of the correct expression
    if expstack.Count=1 then
      begin
      Result:=TPasExpr(expstack[0]);
      Result.Parent:=AParent;
      end;

  finally
    {if Not Assigned(Result) then
      DumpCurToken('Exiting (no result)',iaUndent)
    else
      DumpCurtoken('Exiting (Result: "'+Result.GetDeclaration(true)+'") ',iaUndent);}
    if not Assigned(Result) then begin
      // expression error!
      for i:=0 to expstack.Count-1 do
        TPasExpr(expstack[i]).Release;
    end;
    SetLength(opstack,0);
    expstack.Free;
  end;
end;


function GetExprIdent(p: TPasExpr): String;
begin
  if Assigned(p) and (p is TPrimitiveExpr) and (p.Kind=pekIdent) then
    Result:=TPrimitiveExpr(p).Value
  else
    Result:='';
end;

function TPasParser.DoParseConstValueExpression(AParent: TPasElement): TPasExpr;
var
  x : TPasExpr;
  n : AnsiString;
  r : TRecordValues;
  a : TArrayValues;

  function lastfield:boolean;

  begin
    result:= CurToken<>tkSemicolon;
    if not result then
     begin
       nexttoken;
       if curtoken=tkbraceclose then
         result:=true
       else
         ungettoken;
     end;
  end;

begin
  if CurToken <> tkBraceOpen then
    Result:=DoParseExpression(AParent)
  else begin
    NextToken;
    x:=DoParseConstValueExpression(AParent);
    case CurToken of
      tkComma: // array of values (a,b,c);
        begin
          a:=CreateArrayValues(AParent);
          a.AddValues(x);
          repeat
            NextToken;
            x:=DoParseConstValueExpression(AParent);
            a.AddValues(x);
          until CurToken<>tkComma;
          Result:=a;
        end;

      tkColon: // record field (a:xxx;b:yyy;c:zzz);
        begin
          n:=GetExprIdent(x);
          x.Release;
          r:=CreateRecordValues(AParent);
          NextToken;
          x:=DoParseConstValueExpression(AParent);
          r.AddField(n, x);
          if not lastfield then
            repeat
              n:=ExpectIdentifier;
              ExpectToken(tkColon);
              NextToken;
              x:=DoParseConstValueExpression(AParent);
              r.AddField(n, x)
            until lastfield; // CurToken<>tkSemicolon;
          Result:=r;
        end;
    else
      // Binary expression!  ((128 div sizeof(longint)) - 3);       ;
      Result:=DoParseExpression(AParent,x);
      if CurToken<>tkBraceClose then ParseExc(nParserExpectedCommaRBracket,SParserExpectedCommaRBracket);
      NextToken;
      if CurToken <> tkSemicolon then // the continue of expresion
        Result:=DoParseExpression(AParent,Result);
      Exit;
    end;
    if CurToken<>tkBraceClose then
      ParseExc(nParserExpectedCommaRBracket,SParserExpectedCommaRBracket);
    NextToken;
  end;
end;

function TPasParser.CheckOverloadList(AList: TFPList; AName: String; out
  OldMember: TPasElement): TPasOverloadedProc;

Var
  I : Integer;

begin
  Result:=Nil;
  I:=0;
  While (Result=Nil) and (I<AList.Count) do
    begin
    OldMember:=TPasElement(AList[i]);
    if CompareText(OldMember.Name, AName) = 0 then
      begin
      if OldMember is TPasOverloadedProc then
        Result:=TPasOverloadedProc(OldMember)
      else
        begin
        Result:=TPasOverloadedProc(CreateElement(TPasOverloadedProc, AName, OldMember.Parent));
        Result.Visibility:=OldMember.Visibility;
        Result.Overloads.Add(OldMember);
        Result.SourceFilename:=OldMember.SourceFilename;
        Result.SourceLinenumber:=OldMember.SourceLinenumber;
        Result.DocComment:=Oldmember.DocComment;
        AList[i] := Result;
        end;
      end;
    Inc(I);
    end;
  If Result=Nil then
    OldMember:=Nil;
end;

procedure TPasParser.AddProcOrFunction(Decs: TPasDeclarations;
  AProc: TPasProcedure);
var
  I : Integer;
  OldMember: TPasElement;
  OverloadedProc: TPasOverloadedProc;
begin
  With Decs do
    begin
    if not (po_nooverloadedprocs in Options) then
      OverloadedProc:=CheckOverloadList(Functions,AProc.Name,OldMember)
    else
      OverloadedProc:=nil;
    If (OverloadedProc<>Nil) then
      begin
      OverLoadedProc.Overloads.Add(AProc);
      if (OldMember<>OverloadedProc) then
        begin
        I:=Declarations.IndexOf(OldMember);
        If I<>-1 then
          Declarations[i]:=OverloadedProc;
        end;
      end
    else
      begin
      Declarations.Add(AProc);
      Functions.Add(AProc);
      end;
    end;
end;

// Return the parent of a function declaration. This is AParent,
// except when AParent is a class, and the function is overloaded.
// Then the parent is the overload object.
function TPasParser.CheckIfOverloaded(AParent: TPasElement; const AName: String): TPasElement;
var
  Member: TPasElement;
  OverloadedProc: TPasOverloadedProc;

begin
  Result:=AParent;
  If (not (po_nooverloadedprocs in Options)) and (AParent is TPasClassType) then
    begin
    OverloadedProc:=CheckOverLoadList(TPasClassType(AParent).Members,AName,Member);
    If (OverloadedProc<>Nil) then
      Result:=OverloadedProc;
    end;
end;


procedure TPasParser.ParseMain(var Module: TPasModule);
begin
  Module:=nil;
  NextToken;
  SaveComments;
  case CurToken of
    tkUnit:
      ParseUnit(Module);
    tkProgram:
      ParseProgram(Module);
    tkLibrary:
      ParseLibrary(Module);
  else
    ungettoken;
    ParseProgram(Module,True);
  //    ParseExcTokenError('unit');
  end;
end;

// Starts after the "unit" token
procedure TPasParser.ParseUnit(var Module: TPasModule);
var
  AUnitName: String;
begin
  Module := nil;
  AUnitName := ExpectIdentifier;
  NextToken;
  while CurToken = tkDot do
  begin
    ExpectIdentifier;
    AUnitName := AUnitName + '.' + CurTokenString;
    NextToken;
  end;
  UngetToken;
  Module := TPasModule(CreateElement(TPasModule, AUnitName,
    Engine.Package));
  FCurModule:=Module;
  try
    if Assigned(Engine.Package) then
    begin
      Module.PackageName := Engine.Package.Name;
      Engine.Package.Modules.Add(Module);
    end;
    CheckHint(Module,True);
//    ExpectToken(tkSemicolon);
    ExpectToken(tkInterface);
    If LogEvent(pleInterface) then
      DoLog(mtInfo,nLogStartInterface,SLogStartInterface);
    ParseInterface;
    Engine.FinishScope(stModule,Module);
  finally
    FCurModule:=nil;
  end;
end;

// Starts after the "program" token
procedure TPasParser.ParseProgram(var Module: TPasModule; SkipHeader : Boolean = False);

Var
  PP : TPasProgram;
  Section : TProgramSection;
  N : String;

begin
  if SkipHeader then
    N:=ChangeFileExt(Scanner.CurFilename,'')
  else
    N:=ExpectIdentifier;
  Module := nil;
  PP:=TPasProgram(CreateElement(TPasProgram, N, Engine.Package));
  Module :=PP;
  FCurModule:=Module;
  try
    if Assigned(Engine.Package) then
    begin
      Module.PackageName := Engine.Package.Name;
      Engine.Package.Modules.Add(Module);
    end;
    if not SkipHeader then
      begin
      NextToken;
      If (CurToken=tkBraceOpen) then
        begin
        PP.InputFile:=ExpectIdentifier;
        NextToken;
        if Not (CurToken in [tkBraceClose,tkComma]) then
          ParseExc(nParserExpectedCommaRBracket,SParserExpectedCommaRBracket);
        If (CurToken=tkComma) then
          PP.OutPutFile:=ExpectIdentifier;
        ExpectToken(tkBraceClose);
        NextToken;
        end;
      if (CurToken<>tkSemicolon) then
        ParseExcTokenError(';');
      end;
    Section := TProgramSection(CreateElement(TProgramSection, '', CurModule));
    PP.ProgramSection := Section;
    ParseOptionalUsesList(Section);
    ParseDeclarations(Section);
    Engine.FinishScope(stModule,Module);
  finally
    FCurModule:=nil;
  end;
end;

procedure TPasParser.ParseLibrary(var Module: TPasModule);
Var
  PP : TPasLibrary;
  Section : TLibrarySection;

begin
  Module := nil;
  PP:=TPasLibrary(CreateElement(TPasLibrary, ExpectIdentifier, Engine.Package));
  Module :=PP;
  FCurModule:=Module;
  try
    if Assigned(Engine.Package) then
    begin
      Module.PackageName := Engine.Package.Name;
      Engine.Package.Modules.Add(Module);
    end;
    NextToken;
    if (CurToken<>tkSemicolon) then
        ParseExcTokenError(';');
    Section := TLibrarySection(CreateElement(TLibrarySection, '', CurModule));
    PP.LibrarySection := Section;
    ParseOptionalUsesList(Section);
    ParseDeclarations(Section);
    Engine.FinishScope(stModule,Module);
  finally
    FCurModule:=nil;
  end;
end;

procedure TPasParser.ParseOptionalUsesList(ASection: TPasSection);
// checks if next token is Uses keyword and read uses list
begin
  NextToken;
  if CurToken=tkuses then
    ParseUsesList(ASection)
  else begin
    CheckImplicitUsedUnits(ASection);
    Engine.FinishScope(stUsesList,ASection);
    UngetToken;
  end;
end;

// Starts after the "interface" token
procedure TPasParser.ParseInterface;
var
  Section: TInterfaceSection;
begin
  Section := TInterfaceSection(CreateElement(TInterfaceSection, '', CurModule));
  CurModule.InterfaceSection := Section;
  ParseOptionalUsesList(Section);
  ParseDeclarations(Section); // this also parses the Implementation section
end;

// Starts after the "implementation" token
procedure TPasParser.ParseImplementation;
var
  Section: TImplementationSection;
begin
  Section := TImplementationSection(CreateElement(TImplementationSection, '', CurModule));
  CurModule.ImplementationSection := Section;
  ParseOptionalUsesList(Section);
  ParseDeclarations(Section);
end;

procedure TPasParser.ParseInitialization;
var
  Section: TInitializationSection;
  SubBlock: TPasImplElement;
begin
  Section := TInitializationSection(CreateElement(TInitializationSection, '', CurModule));
  CurModule.InitializationSection := Section;
  repeat
    NextToken;
    if (CurToken=tkend) then
    begin
      ExpectToken(tkDot);
      exit;
    end
    else if (CurToken=tkfinalization) then
    begin
      ParseFinalization;
      exit;
    end
    else if CurToken<>tkSemiColon then
    begin
      UngetToken;
      ParseStatement(Section,SubBlock);
      if SubBlock=nil then
        ExpectToken(tkend);
    end;
  until false;
end;

procedure TPasParser.ParseFinalization;
var
  Section: TFinalizationSection;
  SubBlock: TPasImplElement;
begin
  Section := TFinalizationSection(CreateElement(TFinalizationSection, '', CurModule));
  CurModule.FinalizationSection := Section;
  repeat
    NextToken;
    if (CurToken=tkend) then
    begin
      ExpectToken(tkDot);
      exit;
    end
    else if CurToken<>tkSemiColon then
    begin
      UngetToken;
      ParseStatement(Section,SubBlock);
      if SubBlock=nil then
        ExpectToken(tkend);
    end;
  until false;
  UngetToken;
end;

function TPasParser.GetProcTypeFromToken(tk: TToken; IsClass: Boolean
  ): TProcType;

begin
  Case tk of
    tkProcedure :
      if IsClass then
        Result:=ptClassProcedure
      else
        Result:=ptProcedure;
    tkFunction:
      if IsClass then
        Result:=ptClassFunction
      else
        Result:=ptFunction;
    tkConstructor:
      if IsClass then
        Result:=ptClassConstructor
      else
        Result:=ptConstructor;
    tkDestructor:
      if IsClass then
        Result:=ptClassDestructor
      else
        Result:=ptDestructor;
    tkOperator:
      if IsClass then
        Result:=ptClassOperator
      else
        Result:=ptOperator;
  else
    ParseExc(nParserNotAProcToken,SParserNotAProcToken);
  end;
end;

procedure TPasParser.ParseDeclarations(Declarations: TPasDeclarations);
var
  CurBlock: TDeclType;

  procedure SetBlock(NewBlock: TDeclType);
  begin
    if CurBlock=NewBlock then exit;
    if CurBlock=declType then
      Engine.FinishScope(stTypeSection,Declarations);
    CurBlock:=NewBlock;
  end;

var
  ConstEl: TPasConst;
  ResStrEl: TPasResString;
  TypeEl: TPasType;
  ClassEl: TPasClassType;
  ArrEl : TPasArrayType;
  List: TFPList;
  i,j: Integer;
  VarEl: TPasVariable;
  ExpEl: TPasExportSymbol;
  PropEl : TPasProperty;
  TypeName: String;
  PT : TProcType;
  NamePos: TPasSourcePos;
  ok: Boolean;

begin
  CurBlock := declNone;
  while True do
  begin
    NextToken;
  //  writeln('TPasParser.ParseSection Token=',CurTokenString,' ',CurToken, ' ',scanner.CurFilename);
    case CurToken of
      tkend:
        begin
        If (CurModule is TPasProgram) and (CurModule.InitializationSection=Nil) then
          ParseExcTokenError('begin');
        ExpectToken(tkDot);
        break;
        end;
      tkimplementation:
        if (Declarations is TInterfaceSection) then
          begin
          If Not Engine.InterfaceOnly then
            begin
            If LogEvent(pleImplementation) then
              DoLog(mtInfo,nLogStartImplementation,SLogStartImplementation);
            SetBlock(declNone);
            ParseImplementation;
            end;
          break;
          end;
      tkinitialization:
        if (Declarations is TInterfaceSection)
        or ((Declarations is TImplementationSection) and not (Declarations is TProgramSection)) then
          begin
          SetBlock(declNone);
          ParseInitialization;
          break;
          end;
      tkfinalization:
        if (Declarations is TInterfaceSection)
        or ((Declarations is TImplementationSection) and not (Declarations is TProgramSection)) then
          begin
          SetBlock(declNone);
          ParseFinalization;
          break;
          end;
      tkUses:
        if Declarations.ClassType=TInterfaceSection then
          ParseExcTokenError(TokenInfos[tkimplementation])
        else if Declarations is TPasSection then
          ParseExcTokenError(TokenInfos[tkend])
        else
          ParseExcSyntaxError;
      tkConst:
        SetBlock(declConst);
      tkexports:
        SetBlock(declExports);
      tkResourcestring:
        SetBlock(declResourcestring);
      tkType:
        SetBlock(declType);
      tkVar:
        SetBlock(declVar);
      tkThreadVar:
        SetBlock(declThreadVar);
      tkProperty:
        SetBlock(declProperty);
      tkProcedure, tkFunction, tkConstructor, tkDestructor,tkOperator:
        begin
        SaveComments;
        pt:=GetProcTypeFromToken(CurToken);
        AddProcOrFunction(Declarations, ParseProcedureOrFunctionDecl(Declarations, pt));
        SetBlock(declNone);
        end;
      tkClass:
        begin
          SaveComments;
          NextToken;
          If CurToken in [tkprocedure,tkFunction,tkConstructor, tkDestructor] then
            begin
            pt:=GetProcTypeFromToken(CurToken,True);
            AddProcOrFunction(Declarations,ParseProcedureOrFunctionDecl(Declarations, pt));
            SetBlock(declNone);
            end
          else
            ExpectToken(tkprocedure);
        end;
      tkIdentifier:
        begin
          SaveComments;
          case CurBlock of
            declConst:
              begin
                ConstEl := ParseConstDecl(Declarations);
                Declarations.Declarations.Add(ConstEl);
                Declarations.Consts.Add(ConstEl);
              end;
            declResourcestring:
              begin
                ResStrEl := ParseResourcestringDecl(Declarations);
                Declarations.Declarations.Add(ResStrEl);
                Declarations.ResStrings.Add(ResStrEl);
              end;
            declType:
              begin
                TypeEl := ParseTypeDecl(Declarations);
                if Assigned(TypeEl) then        // !!!
                begin
                  Declarations.Declarations.Add(TypeEl);
                  if (TypeEl.ClassType = TPasClassType)
                      and (not (po_keepclassforward in Options)) then
                  begin
                    // Remove previous forward declarations, if necessary
                    for i := 0 to Declarations.Classes.Count - 1 do
                    begin
                      ClassEl := TPasClassType(Declarations.Classes[i]);
                      if CompareText(ClassEl.Name, TypeEl.Name) = 0 then
                      begin
                        Declarations.Classes.Delete(i);
                        for j := 0 to Declarations.Declarations.Count - 1 do
                          if CompareText(TypeEl.Name,
                            TPasElement(Declarations.Declarations[j]).Name) = 0 then
                          begin
                            Declarations.Declarations.Delete(j);
                            break;
                          end;
                        ClassEl.Release;
                        break;
                      end;
                    end;
                    // Add the new class to the class list
                    Declarations.Classes.Add(TypeEl)
                  end else
                    Declarations.Types.Add(TypeEl);
                end;
              end;
            declExports:
              begin
              List := TFPList.Create;
              try
                ok:=false;
                try
                  ParseExportDecl(Declarations, List);
                  ok:=true;
                finally
                  if not ok then
                    for i := 0 to List.Count - 1 do
                      TPasExportSymbol(List[i]).Release;
                end;
                for i := 0 to List.Count - 1 do
                begin
                  ExpEl := TPasExportSymbol(List[i]);
                  Declarations.Declarations.Add(ExpEl);
                  Declarations.ExportSymbols.Add(ExpEl);
                end;
              finally
                List.Free;
              end;
              end;
            declVar, declThreadVar:
              begin
                List := TFPList.Create;
                try
                  ParseVarDecl(Declarations, List);
                  for i := 0 to List.Count - 1 do
                  begin
                    VarEl := TPasVariable(List[i]);
                    Declarations.Declarations.Add(VarEl);
                    Declarations.Variables.Add(VarEl);
                  end;
                finally
                  List.Free;
                end;
              end;
            declProperty:
              begin
              PropEl:=ParseProperty(Declarations,CurtokenString,visDefault);
              Declarations.Declarations.Add(PropEl);
              Declarations.properties.Add(PropEl);
              end;
          else
            ParseExcSyntaxError;
          end;
        end;
      tkGeneric:
        begin
          if CurBlock <> declType then
            ParseExcSyntaxError;
          TypeName := ExpectIdentifier;
          NamePos:=Scanner.CurSourcePos;
          List:=TFPList.Create;
          try
            ReadGenericArguments(List,Nil);
            ExpectToken(tkEqual);
            NextToken;
            Case CurToken of
              tkClass :
                 begin
                 ClassEl := TPasClassType(CreateElement(TPasClassType,
                   TypeName, Declarations, NamePos));
                 ClassEl.ObjKind:=okGeneric;
                 For I:=0 to List.Count-1 do
                   begin
                   TPasElement(List[i]).Parent:=ClassEl;
                   ClassEl.GenericTemplateTypes.Add(List[i]);
                   end;
                 NextToken;
                 DoParseClassType(ClassEl);
                 Declarations.Declarations.Add(ClassEl);
                 Declarations.Classes.Add(ClassEl);
                 CheckHint(classel,True);
                 end;
              tkArray:
                 begin
                 if List.Count<>1 then
                   ParseExc(nParserGenericArray1Element,sParserGenericArray1Element);
                 ArrEl:=TPasArrayType(ParseArrayType(Declarations,NamePos,TypeName,pmNone));
                 CheckHint(ArrEl,True);
                 ArrEl.ElType.Release;
                 ArrEl.elType:=TPasGenericTemplateType(List[0]);
                 Declarations.Declarations.Add(ArrEl);
                 Declarations.Types.Add(ArrEl);
                 end;
            else
              ParseExc(nParserGenericClassOrArray,SParserGenericClassOrArray);
            end;
          finally
            List.Free;
          end;
        end;
      tkbegin:
        begin
        if Declarations is TProcedureBody then
          begin
          SetBlock(declNone);
          ParseProcBeginBlock(TProcedureBody(Declarations));
          break;
          end
        else if (Declarations is TInterfaceSection)
        or (Declarations is TImplementationSection) then
          begin
          SetBlock(declNone);
          ParseInitialization;
          break;
          end
        else
          ParseExcSyntaxError;
        end;
      tklabel:
        begin
          SetBlock(declNone);
          if not (Declarations is TInterfaceSection) then
            ParseLabels(Declarations);
        end;
    else
      ParseExcSyntaxError;
    end;
  end;
  SetBlock(declNone);
end;

function TPasParser.CheckUseUnit(ASection: TPasSection; AUnitName: string
  ): TPasElement;

  procedure CheckDuplicateInUsesList(AUnitName : string; UsesList: TFPList);
  var
    i: Integer;
  begin
    if UsesList=nil then exit;
    for i:=0 to UsesList.Count-1 do
      if CompareText(AUnitName,TPasModule(UsesList[i]).Name)=0 then
        ParseExc(nParserDuplicateIdentifier,SParserDuplicateIdentifier,[AUnitName]);
  end;

begin
  if CompareText(AUnitName,CurModule.Name)=0 then
    ParseExc(nParserDuplicateIdentifier,SParserDuplicateIdentifier,[AUnitName]);
  CheckDuplicateInUsesList(AUnitName,ASection.UsesList);
  if ASection.ClassType=TImplementationSection then
    CheckDuplicateInUsesList(AUnitName,CurModule.InterfaceSection.UsesList);

  result := Engine.FindModule(AUnitName);  // should we resolve module here when "IN" filename is not known yet?
  if Assigned(result) then
    result.AddRef
  else
    Result := TPasUnresolvedUnitRef(CreateElement(TPasUnresolvedUnitRef,
      AUnitName, ASection));
  ASection.UsesList.Add(Result);
end;

procedure TPasParser.CheckImplicitUsedUnits(ASection: TPasSection);
var
  i: Integer;
begin
  If not (ASection.ClassType=TImplementationSection) Then // interface,program,library,package
    begin
    // load implicit units, like 'System'
    for i:=0 to ImplicitUses.Count-1 do
      CheckUseUnit(ASection,ImplicitUses[i]);
    end;
end;

// Starts after the "uses" token
procedure TPasParser.ParseUsesList(ASection: TPasSection);
var
  AUnitName: String;
  Element: TPasElement;
begin
  CheckImplicitUsedUnits(ASection);

  Repeat
    AUnitName := ExpectIdentifier;
    NextToken;
    while CurToken = tkDot do
    begin
      ExpectIdentifier;
      AUnitName := AUnitName + '.' + CurTokenString;
      NextToken;
    end;
    Element := CheckUseUnit(ASection,AUnitName);
    if (CurToken=tkin) then
      begin
      ExpectToken(tkString);
      if (Element is TPasModule) and (TPasmodule(Element).filename='')  then
        TPasModule(Element).FileName:=curtokenstring
      else if (Element is TPasUnresolvedUnitRef) then
        TPasUnresolvedUnitRef(Element).FileName:=curtokenstring;
      NextToken;
      end;

    if Not (CurToken in [tkComma,tkSemicolon]) then
      ParseExc(nParserExpectedCommaSemicolon,SParserExpectedCommaSemicolon);
  Until (CurToken=tkSemicolon);

  Engine.FinishScope(stUsesList,ASection);
end;

// Starts after the variable name
function TPasParser.ParseConstDecl(Parent: TPasElement): TPasConst;
var
  ok: Boolean;
begin
  SaveComments;
  Result := TPasConst(CreateElement(TPasConst, CurTokenString, Parent));
  ok:=false;
  try
    NextToken;
    if CurToken = tkColon then
      Result.VarType := ParseType(Result,Scanner.CurSourcePos)
    else
      UngetToken;
    ExpectToken(tkEqual);
    NextToken;
    Result.Expr:=DoParseConstValueExpression(Result);
    UngetToken;
    CheckHint(Result,True);
    ok:=true;
  finally
    if not ok then
      ReleaseAndNil(TPasElement(Result));
  end;
  Engine.FinishScope(stConstDef,Result);
end;

// Starts after the variable name
function TPasParser.ParseResourcestringDecl(Parent: TPasElement): TPasResString;
var
  ok: Boolean;
begin
  SaveComments;
  Result := TPasResString(CreateElement(TPasResString, CurTokenString, Parent));
  ok:=false;
  try
    ExpectToken(tkEqual);
    NextToken; // skip tkEqual
    Result.Expr:=DoParseConstValueExpression(Result);
    UngetToken;
    CheckHint(Result,True);
    ok:=true;
  finally
    if not ok then
      ReleaseAndNil(TPasElement(Result));
  end;
end;

procedure TPasParser.ReadGenericArguments(List : TFPList;Parent : TPasElement);

Var
  N : String;

begin
  ExpectToken(tkLessThan);
  repeat
    N:=ExpectIdentifier;
    List.Add(CreateElement(TPasGenericTemplateType,N,Parent));
    NextToken;
    if not (CurToken in [tkComma, tkGreaterThan]) then
      ParseExc(nParserExpectToken2Error,SParserExpectToken2Error,
        [TokenInfos[tkComma], TokenInfos[tkGreaterThan]]);
  until CurToken = tkGreaterThan;
end;

// Starts after the type name
function TPasParser.ParseRangeType(AParent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String; Full: Boolean
  ): TPasRangeType;

Var
  PE : TPasExpr;
  ok: Boolean;

begin
  Result := TPasRangeType(CreateElement(TPasRangeType, TypeName, AParent, NamePos));
  ok:=false;
  try
    if Full then
      begin
      If not (CurToken=tkEqual) then
        ParseExcTokenError(TokenInfos[tkEqual]);
      end;
    NextToken;
    PE:=DoParseExpression(Result,Nil);
    if not ((PE is TBinaryExpr) and (TBinaryExpr(PE).Kind=pekRange)) then
      begin
      PE.Release;
      ParseExc(nRangeExpressionExpected,SRangeExpressionExpected);
      end;
    Result.RangeExpr:=PE as TBinaryExpr;
    UngetToken;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
  Engine.FinishScope(stTypeDef,Result);
end;

// Starts after Exports, on first identifier.
procedure TPasParser.ParseExportDecl(Parent: TPasElement; List: TFPList);
Var
  E : TPasExportSymbol;
begin
  Repeat
    if List.Count<>0 then
      ExpectIdentifier;
    E:=TPasExportSymbol(CreateElement(TPasExportSymbol,CurtokenString,Parent));
    List.Add(E);
    NextToken;
    if CurTokenIsIdentifier('INDEX') then
      begin
      NextToken;
      E.Exportindex:=DoParseExpression(E,Nil)
      end
    else if CurTokenIsIdentifier('NAME') then
      begin
      NextToken;
      E.ExportName:=DoParseExpression(E,Nil)
      end;
    if not (CurToken in [tkComma,tkSemicolon]) then
      ParseExc(nParserExpectedCommaSemicolon,SParserExpectedCommaSemicolon);
  until (CurToken=tkSemicolon);
end;

function TPasParser.ParseSpecializeType(Parent: TPasElement;
  const TypeName: String): TPasClassType;

var
  ok: Boolean;
begin
  Result := TPasClassType(CreateElement(TPasClassType, TypeName, Parent,
    Scanner.CurSourcePos));
  ok:=false;
  try
    Result.ObjKind := okSpecialize;
    Result.AncestorType := ParseType(Result,Scanner.CurSourcePos);
    Result.IsShortDefinition:=True;
    ReadGenericArguments(TPasClassType(Result).GenericTemplateTypes,Result);
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.ParseProcedureType(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: String; const PT: TProcType
  ): TPasProcedureType;

var
  ok: Boolean;
begin
  if PT in [ptFunction,ptClassFunction] then
    Result := CreateFunctionType(TypeName, 'Result', Parent, False)
  else
    Result := TPasProcedureType(CreateElement(TPasProcedureType, TypeName, Parent, NamePos));
  ok:=false;
  try
    ParseProcedureOrFunctionHeader(Result, TPasProcedureType(Result), PT, True);
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.ParseTypeDecl(Parent: TPasElement): TPasType;

var
  TypeName: String;
  NamePos: TPasSourcePos;
begin
  TypeName := CurTokenString;
  NamePos:=Scanner.CurSourcePos;
  ExpectToken(tkEqual);
  Result:=ParseType(Parent,NamePos,TypeName,True);
end;

function TPasParser.GetVariableValueAndLocation(Parent: TPasElement; out
  Value: TPasExpr; out Location: String): Boolean;

begin
  Value:=Nil;
  NextToken;
  Result:=CurToken=tkEqual;
  if Result then
    begin
    NextToken;
    Value := DoParseConstValueExpression(Parent);
//    NextToken;
    end;
  if (CurToken=tkAbsolute) then
    begin
    Result:=True;
    ExpectIdentifier;
    Location:=CurTokenText;
    NextToken;
    if CurToken=tkDot then
      begin
      ExpectIdentifier;
      Location:=Location+'.'+CurTokenText;
      end
    else
      UnGetToken;
    end
  else
    UngetToken;
end;

function TPasParser.GetVariableModifiers(out VarMods: TVariableModifiers; out
  Libname, ExportName: string): string;

Var
  S : String;
begin
  Result := '';
  VarMods := [];
  NextToken;
  If CurTokenIsIdentifier('cvar') then
    begin
    Result:=';cvar';
    Include(VarMods,vmcvar);
    ExpectToken(tkSemicolon);
    NextToken;
    end;
  s:=LowerCase(CurTokenText);
  if Not ((s='external') or (s='public') or (s='export')) then
    UngetToken
  else
    begin
    if s='external' then
      Include(VarMods,vmexternal)
    else if (s='public') then
      Include(varMods,vmpublic)
    else if (s='export') then
      Include(varMods,vmexport);
    Result:=Result+';'+CurTokenText;
    NextToken;
    if (Curtoken<>tksemicolon) then
      begin
      if (s='external') then
        begin
        Include(VarMods,vmexternal);
        if (CurToken in [tkString,tkIdentifier])
            and Not (CurTokenIsIdentifier('name')) then
          begin
          Result := Result + ' ' + CurTokenText;
          LibName:=CurTokenText;
          NextToken;
          end;
        end;
      if CurTokenIsIdentifier('name') then
        begin
        Result := Result + ' name ';
        NextToken;
        if (CurToken in [tkString,tkIdentifier]) then
          Result := Result + CurTokenText
        else
          ParseExcSyntaxError;
        ExportName:=CurTokenText;
        NextToken;
        end
      else
        ParseExcSyntaxError;
      end;
    end;
end;


// Full means that a full variable declaration is being parsed.
procedure TPasParser.ParseVarList(Parent: TPasElement; VarList: TFPList; AVisibility: TPasMemberVisibility; Full : Boolean);
// on Exception the VarList is restored, no need to Release the new elements

var
  i, OldListCount: Integer;
  Value : TPasExpr;
  VarType: TPasType;
  VarEl: TPasVariable;
  H : TPasMemberHints;
  VarMods: TVariableModifiers;
  D,Mods,Loc,aLibName,aExpName : string;
  ok: Boolean;

begin
  OldListCount:=VarList.Count;
  ok:=false;
  try
    D:=SaveComments; // This means we support only one comment per 'list'.
    VarEl:=nil;
    Repeat
      // create the TPasVariable here, so that SourceLineNumber is correct
      VarEl:=TPasVariable(CreateElement(TPasVariable,CurTokenString,Parent,AVisibility));
      VarList.Add(VarEl);
      NextToken;
      if Not (CurToken in [tkComma,tkColon]) then
        ParseExc(nParserExpectedCommaColon,SParserExpectedCommaColon);
      if CurToken=tkComma then
        ExpectIdentifier;
    Until (CurToken=tkColon);

    // read type
    VarType := ParseComplexType(VarEl);
    for i := OldListCount to VarList.Count - 1 do
      begin
      VarEl:=TPasVariable(VarList[i]);
      // Writeln(VarEl.Name, AVisibility);
      VarEl.VarType := VarType;
      //VarType.Parent := VarEl; // this is wrong for references types
      if (i>=OldListCount) then
        VarType.AddRef;
      end;

    Value:=Nil;
    H:=CheckHint(Nil,False);
    If Full then
      GetVariableValueAndLocation(Parent,Value,Loc);
    if (Value<>nil) and (VarList.Count>OldListCount+1) then
      ParseExc(nParserOnlyOneVariableCanBeInitialized,SParserOnlyOneVariableCanBeInitialized);
    TPasVariable(VarList[OldListCount]).Expr:=Value;

    H:=H+CheckHint(Nil,Full);
    if Full then
      Mods:=GetVariableModifiers(VarMods,aLibName,aExpName)
    else
      NextToken;
    SaveComments(D);

    // connect
    for i := OldListCount to VarList.Count - 1 do
      begin
      VarEl:=TPasVariable(VarList[i]);
      // Writeln(VarEl.Name, AVisibility);
      // Procedure declaration eats the hints.
      if Assigned(VarType) and (VarType is TPasProcedureType) then
        VarEl.Hints:=VarType.Hints
      else
        VarEl.Hints:=H;
      VarEl.Modifiers:=Mods;
      VarEl.VarModifiers:=VarMods;
      VarEl.AbsoluteLocation:=Loc;
      VarEl.LibraryName:=aLibName;
      VarEl.ExportName:=aExpName;
      end;
    ok:=true;
  finally
    if not ok then
      begin
        for i:=OldListCount to VarList.Count-1 do
          TPasElement(VarList[i]).Release;
        VarList.Count:=OldListCount;
      end;
  end;
end;

procedure TPasParser.SetOptions(AValue: TPOptions);
begin
  if FOptions=AValue then Exit;
  FOptions:=AValue;
  If Assigned(FScanner) then
    FScanner.Options:=AValue;
end;

function TPasParser.SaveComments: String;
begin
  if Engine.NeedComments then
    FSavedComments:=CurComments.Text; // Expensive, so don't do unless needed.
  Result:=FSavedComments;
end;

function TPasParser.SaveComments(const AValue: String): String;
begin
  FSavedComments:=AValue;
  Result:=FSavedComments;
end;

function TPasParser.LogEvent(E: TPParserLogEvent): Boolean;
begin
  Result:=E in FLogEvents;
end;

procedure TPasParser.SetLastMsg(MsgType: TMessageType; MsgNumber: integer;
  const Fmt: String; Args: array of const);
begin
  FLastMsgType := MsgType;
  FLastMsgNumber := MsgNumber;
  FLastMsgPattern := Fmt;
  FLastMsg := Format(Fmt,Args);
  CreateMsgArgs(FLastMsgArgs,Args);
end;

procedure TPasParser.DoLog(MsgType: TMessageType; MsgNumber: integer;
  const Msg: String; SkipSourceInfo: Boolean);
begin
  DoLog(MsgType,MsgNumber,Msg,[],SkipSourceInfo);
end;

procedure TPasParser.DoLog(MsgType: TMessageType; MsgNumber: integer;
  const Fmt: String; Args: array of const; SkipSourceInfo: Boolean);
begin
  SetLastMsg(MsgType,MsgNumber,Fmt,Args);
  If Assigned(FOnLog) then
    if SkipSourceInfo or not assigned(scanner) then
      FOnLog(Self,FLastMsg)
    else
      FOnLog(Self,Format('%s(%d) : %s',[Scanner.CurFilename,Scanner.CurRow,FLastMsg]));
end;

procedure TPasParser.ParseInlineVarDecl(Parent: TPasElement; List: TFPList;
  AVisibility: TPasMemberVisibility = VisDefault; ClosingBrace: Boolean = False);

Var
  tt : TTokens;
begin
  ParseVarList(Parent,List,AVisibility,False);
  tt:=[tkEnd,tkSemicolon];
  if ClosingBrace then
   include(tt,tkBraceClose);
  if not (CurToken in tt) then
    ParseExc(nParserExpectedSemiColonEnd,SParserExpectedSemiColonEnd);
end;

// Starts after the variable name
procedure TPasParser.ParseVarDecl(Parent: TPasElement; List: TFPList);

begin
  ParseVarList(Parent,List,visDefault,True);
end;

// Starts after the opening bracket token
procedure TPasParser.ParseArgList(Parent: TPasElement; Args: TFPList; EndToken: TToken);
var
  IsUntyped, ok, LastHadDefaultValue: Boolean;
  Name : String;
  Value : TPasExpr;
  i, OldArgCount: Integer;
  Arg: TPasArgument;
  Access: TArgumentAccess;
  ArgType: TPasType;
begin
  LastHadDefaultValue := false;
  while True do
  begin
    OldArgCount:=Args.Count;
    Access := argDefault;
    IsUntyped := False;
    ArgType := nil;
    while True do
    begin
      NextToken;
      if CurToken = tkConst then
      begin
        Access := argConst;
        Name := ExpectIdentifier;
      end else if CurToken = tkConstRef then
      begin
        Access := argConstref;
        Name := ExpectIdentifier;
      end else if CurToken = tkVar then
      begin
        Access := ArgVar;
        Name := ExpectIdentifier;
      end else if (CurToken = tkIdentifier) and (UpperCase(CurTokenString) = 'OUT') then
      begin
        Access := ArgOut;
        Name := ExpectIdentifier;
      end else if CurToken = tkIdentifier then
        Name := CurTokenString
      else
        ParseExc(nParserExpectedConstVarID,SParserExpectedConstVarID);
      Arg := TPasArgument(CreateElement(TPasArgument, Name, Parent));
      Arg.Access := Access;
      Args.Add(Arg);
      NextToken;
      if CurToken = tkColon then
        break
      else if ((CurToken = tkSemicolon) or (CurToken = tkBraceClose)) and
        (Access <> argDefault) then
      begin
        // found an untyped const or var argument
        UngetToken;
        IsUntyped := True;
        break
      end
      else if CurToken <> tkComma then
        ParseExc(nParserExpectedCommaColon,SParserExpectedCommaColon);
    end;
    Value:=Nil;
    if not IsUntyped then
      begin
      Arg := TPasArgument(Args[0]);
      ArgType := ParseType(Arg,Scanner.CurSourcePos);
      ok:=false;
      try
        NextToken;
        if CurToken = tkEqual then
          begin
          if (Args.Count>OldArgCount+1) then
            begin
            ArgType.Release;
            ArgType:=nil;
            ParseExc(nParserOnlyOneArgumentCanHaveDefault,SParserOnlyOneArgumentCanHaveDefault);
            end;
          NextToken;
          Value := DoParseExpression(Parent,Nil);
          // After this, we're on ), which must be unget.
          LastHadDefaultValue:=true;
          end
        else if LastHadDefaultValue then
          ParseExc(nParserDefaultParameterRequiredFor,
            SParserDefaultParameterRequiredFor,[TPasArgument(Args[OldArgCount]).Name]);
        UngetToken;
        ok:=true;
      finally
        if (not ok) and (ArgType<>nil) then
          ArgType.Release;
      end;
      end;

    for i := OldArgCount to Args.Count - 1 do
    begin
      Arg := TPasArgument(Args[i]);
      Arg.ArgType := ArgType;
      if Assigned(ArgType) then
        begin
        if (i > OldArgCount) then
          ArgType.AddRef;
        end;
      Arg.ValueExpr := Value;
      Value:=Nil; // Only the first gets a value. OK, since Var A,B : Integer = 1 is not allowed.
    end;

    NextToken;
    if (CurToken = tkIdentifier) and (LowerCase(CurTokenString) = 'location') then
      begin
        NextToken; // remove 'location'
        NextToken; // remove register
      end;
    if CurToken = EndToken then
      break;
  end;
end;


function TPasParser.CheckProcedureArgs(Parent: TPasElement; Args: TFPList;
  Mandatory: Boolean): boolean;

begin
  NextToken;
  Result:=(Curtoken=tkbraceOpen);
  if not Result then
    begin
    if Mandatory then
      ParseExc(nParserExpectedLBracketColon,SParserExpectedLBracketColon)
    else
      UngetToken;
    end
  else
    begin
    NextToken;
    if (CurToken<>tkBraceClose) then
      begin
      UngetToken;
      ParseArgList(Parent, Args, tkBraceClose);
      end;
    end;
end;

procedure TPasParser.HandleProcedureModifier(Parent: TPasElement; pm: TProcedureModifier);

Var
  Tok : String;
  P : TPasProcedure;
  E : TPasExpr;

begin
  if parent is TPasProcedure then
    P:=TPasProcedure(Parent);
  if Assigned(P) then
    P.AddModifier(pm);
  if (pm=pmExternal) then
    begin
    NextToken;
    if CurToken in [tkString,tkIdentifier] then
      begin
      // extrenal libname
      // external libname name XYZ
      // external name XYZ
      Tok:=UpperCase(CurTokenString);
      if Not ((curtoken=tkIdentifier) and (Tok='NAME')) then
        begin
        E:=DoParseExpression(Parent);
        if Assigned(P) then
          P.LibraryExpr:=E;
        end;
      if CurToken=tkSemicolon then
        UnGetToken
      else
        begin
        Tok:=UpperCase(CurTokenString);
        if ((curtoken=tkIdentifier) and (Tok='NAME')) then
          begin
          NextToken;
          if not (CurToken in [tkString,tkIdentifier]) then
            ParseExcTokenError(TokenInfos[tkString]);
          E:=DoParseExpression(Parent);
          if Assigned(P) then
            P.LibrarySymbolName:=E;
          end;
        end;
      end
    else
      UngetToken;
    end
  else if (pm = pmPublic) then
    begin
    NextToken;
    { Should be token Name,
      if not we're in a class and the public section starts }
    If (Uppercase(CurTokenString)<>'NAME') then
      begin
      UngetToken;
      UngetToken;
      exit;
      end
    else
      begin
      NextToken;  // Should be export name string.
      if not (CurToken in [tkString,tkIdentifier]) then
        ParseExcTokenError(TokenInfos[tkString]);
      E:=DoParseExpression(Parent);
      if parent is TPasProcedure then
        TPasProcedure(Parent).PublicName:=E;
      if (CurToken <> tkSemicolon) then
        ParseExcTokenError(TokenInfos[tkSemicolon]);
      end;
    end
  else if (pm=pmForward) then
    begin
    if (Parent.Parent is TInterfaceSection) then
       begin
       ParseExc(nParserForwardNotInterface,SParserForwardNotInterface);
       UngetToken;
       end;
    end
  else if (pm=pmMessage) then
    begin
    Repeat
      NextToken;
      If CurToken<>tkSemicolon then
        begin
        if parent is TPasProcedure then
          TPasProcedure(Parent).MessageName:=CurtokenString;
        If (CurToken=tkString) and (parent is TPasProcedure) then
          TPasProcedure(Parent).Messagetype:=pmtString;
        end;
    until CurToken = tkSemicolon;
    UngetToken;
    end;
end;

// Next token is expected to be a "(", ";" or for a function ":". The caller
// will get the token after the final ";" as next token.
procedure TPasParser.ParseProcedureOrFunctionHeader(Parent: TPasElement;
  Element: TPasProcedureType; ProcType: TProcType; OfObjectPossible: Boolean);

  procedure ConsumeSemi;
  begin
    NextToken;
    if (CurToken <> tksemicolon) and IsCurTokenHint then
      ungettoken;
  end;

  function DoCheckHint : Boolean;

  var
    ahint : TPasMemberHint;
  begin
  Result:= IsCurTokenHint(ahint);
  if Result then  // deprecated,platform,experimental,library, unimplemented etc
    begin
    element.hints:=element.hints+[ahint];
    if aHint=hDeprecated then
      begin
      nextToken;
      if (CurToken<>tkString) then
        UnGetToken
      else
        element.HintMessage:=curtokenstring;
      end;
    end;
  end;

Var
  Tok : String;
  CC : TCallingConvention;
  PM : TProcedureModifier;
  Done: Boolean;
  ResultEl: TPasResultElement;

begin
  // Element must be non-nil. Removed all checks for not-nil.
  // If it is nil, the following fails anyway.
  CheckProcedureArgs(Element,Element.Args,ProcType in [ptOperator,ptClassOperator]);
  case ProcType of
    ptFunction,ptClassFunction:
      begin
      ExpectToken(tkColon);
      ResultEl:=TPasFunctionType(Element).ResultEl;
      ResultEl.ResultType := ParseType(ResultEl,Scanner.CurSourcePos);
      end;
    ptOperator,ptClassOperator:
      begin
      NextToken;
      ResultEl:=TPasFunctionType(Element).ResultEl;
      if (CurToken=tkIdentifier) then
        begin
        ResultEl.Name := CurTokenName;
        ExpectToken(tkColon);
        end
      else
        if (CurToken=tkColon) then
          ResultEl.Name := 'Result'
        else
          ParseExc(nParserExpectedColonID,SParserExpectedColonID);
        ResultEl.ResultType := ParseType(ResultEl,Scanner.CurSourcePos)
      end;
  end;
  if OfObjectPossible then
    begin
    NextToken;
    if (curToken =tkOf) then
      begin
      ExpectToken(tkObject);
      Element.IsOfObject := True;
      end 
    else if (curToken = tkIs) then
      begin
      expectToken(tkIdentifier);
      if (lowerCase(CurTokenString)<>'nested') then
        ParseExc(nParserExpectedNested,SParserExpectedNested);
      Element.isNested:=True;
      end
    else
      UnGetToken;  
    end;  
  NextToken;
  if CurToken = tkEqual then
    begin
    // for example: const p: procedure = nil;
    UngetToken;
    exit;
    end
  else
    UngetToken;
  Repeat
    NextToken;
    If TokenisCallingConvention(CurTokenString,cc) then
      begin
      Element.CallingConvention:=Cc;
      if cc = ccSysCall then
      begin
        // remove LibBase
        NextToken;
        if CurToken=tkSemiColon then
          UngetToken
        else
          // remove legacy or basesysv on MorphOS syscalls
          begin
          if CurTokenIsIdentifier('legacy') or CurTokenIsIdentifier('BaseSysV') then
            NextToken;
          NextToken; // remove offset
          end;
      end;
      ExpectToken(tkSemicolon);
      end
    else if TokenIsProcedureModifier(Parent,CurTokenString,pm) then
      HandleProcedureModifier(Parent,Pm)
    else if (CurToken=tklibrary) then // library is a token and a directive.
      begin
      Tok:=UpperCase(CurTokenString);
      NextToken;
      If (tok<>'NAME') then
        Element.Hints:=Element.Hints+[hLibrary]
      else
        begin
        NextToken;  // Should be export name string.
        ExpectToken(tkSemicolon);
        end;
      end
    else if DoCheckHint then
      consumesemi
    else if (CurToken = tkSquaredBraceOpen) then
      begin
      repeat
        NextToken
      until CurToken = tkSquaredBraceClose;
      ExpectToken(tkSemicolon);
      end;
    Done:=(CurToken=tkSemiColon);
    if Done then
      begin
      NextToken;
      Done:=Not ((Curtoken=tkSquaredBraceOpen) or TokenIsProcedureModifier(Parent,CurtokenString,Pm) or IscurtokenHint() or TokenisCallingConvention(CurTokenString,cc));
//      DumpCurToken('Done '+IntToStr(Ord(Done)));
      UngetToken;
      end;
//    Writeln('Done: ',TokenInfos[Curtoken],' ',CurtokenString);
  Until Done;
  if DoCheckHint then  // deprecated,platform,experimental,library, unimplemented etc
    ConsumeSemi;
  if (ProcType in [ptOperator,ptClassOperator]) and (Parent is TPasOperator) then
    TPasOperator(Parent).CorrectName;
  Engine.FinishScope(stProcedureHeader,Element);
  if (Parent is TPasProcedure)
  and (not TPasProcedure(Parent).IsForward)
  and (not TPasProcedure(Parent).IsExternal)
  and ((Parent.Parent is TImplementationSection)
     or (Parent.Parent is TProcedureBody))
  then
    ParseProcedureBody(Parent);
  Engine.FinishScope(stProcedure,Parent);
end;

// starts after the semicolon
procedure TPasParser.ParseProcedureBody(Parent: TPasElement);

var
  Body: TProcedureBody;

begin
  Body := TProcedureBody(CreateElement(TProcedureBody, '', Parent));
  TPasProcedure(Parent).Body:=Body;
  ParseDeclarations(Body);
end;


function TPasParser.ParseProperty(Parent: TPasElement; const AName: String;
  AVisibility: TPasMemberVisibility): TPasProperty;

  function GetAccessorName(aParent: TPasElement; out Expr: TPasExpr): String;
  var
    Last: TPasExpr;
    Params: TParamsExpr;
    Param: TPasExpr;
  begin
    ExpectIdentifier;
    Result := CurTokenString;
    Expr := CreatePrimitiveExpr(aParent,pekIdent,CurTokenString);
    Last := Expr;

    // read .subident.subident...
    repeat
      NextToken;
      if CurToken <> tkDot then break;
      ExpectIdentifier;
      Result := Result + '.' + CurTokenString;
      AddToBinaryExprChain(Expr,Last,CreatePrimitiveExpr(aParent,pekIdent,CurTokenString),eopSubIdent);
    until false;

    // read optional array index
    if CurToken <> tkSquaredBraceOpen then
      UnGetToken
    else
      begin
      Result := Result + '[';
      Params:=TParamsExpr(CreateElement(TParamsExpr,'',aParent));
      Params.Kind:=pekArrayParams;
      AddParamsToBinaryExprChain(Expr,Last,Params);
      NextToken;
      case CurToken of
        tkChar:             Param:=CreatePrimitiveExpr(aParent,pekString, CurTokenText);
        tkNumber:           Param:=CreatePrimitiveExpr(aParent,pekNumber, CurTokenString);
        tkIdentifier:       Param:=CreatePrimitiveExpr(aParent,pekIdent, CurTokenText);
        tkfalse, tktrue:    Param:=CreateBoolConstExpr(aParent,pekBoolConst, CurToken=tktrue);
      else
        ParseExcExpectedIdentifier;
      end;
      Params.AddParam(Param);
      Result := Result + CurTokenString;
      ExpectToken(tkSquaredBraceClose);
      Result := Result + ']';
      end;
  end;

var
  isArray , ok: Boolean;
  h   : TPasMemberHint;

begin
  Result:=TPasProperty(CreateElement(TPasProperty,AName,Parent,AVisibility));
  ok:=false;
  try
    NextToken;
    isArray:=CurToken=tkSquaredBraceOpen;
    if isArray then
      begin
      ParseArgList(Result, Result.Args, tkSquaredBraceClose);
      NextToken;
      end;
    if CurToken = tkColon then
      begin
      Result.VarType := ParseType(Result,Scanner.CurSourcePos);
      NextToken;
      end;
    if CurTokenIsIdentifier('INDEX') then
      begin
      NextToken;
      Result.IndexExpr := DoParseExpression(Result);
      end;
    if CurTokenIsIdentifier('READ') then
      begin
      Result.ReadAccessorName := GetAccessorName(Result,Result.ReadAccessor);
      NextToken;
      end;
    if CurTokenIsIdentifier('WRITE') then
      begin
      Result.WriteAccessorName := GetAccessorName(Result,Result.WriteAccessor);
      NextToken;
      end;
    if CurTokenIsIdentifier('IMPLEMENTS') then
      begin
      Result.ImplementsName := GetAccessorName(Result,Result.ImplementsFunc);
      NextToken;
      end;
    if CurTokenIsIdentifier('STORED') then
      begin
      NextToken;
      if CurToken = tkTrue then
        Result.StoredAccessorName := 'True'
      else if CurToken = tkFalse then
        Result.StoredAccessorName := 'False'
      else if CurToken = tkIdentifier then
        begin
        UngetToken;
        Result.StoredAccessorName := GetAccessorName(Result,Result.StoredAccessor);
        end
      else
        ParseExcSyntaxError;
      NextToken;
      end;
    if CurTokenIsIdentifier('DEFAULT') then
      begin
      if isArray then
        ParseExc(nParserArrayPropertiesCannotHaveDefaultValue,SParserArrayPropertiesCannotHaveDefaultValue);
      NextToken;
      Result.DefaultExpr := DoParseExpression(Result);
//      NextToken;
      end
    else if CurtokenIsIdentifier('NODEFAULT') then
      begin
      Result.IsNodefault:=true;
      NextToken;
      end;
    // Here the property ends. There can still be a 'default'
    if CurToken = tkSemicolon then
      NextToken;
    if CurTokenIsIdentifier('DEFAULT') then
      begin
      if (Result.VarType<>Nil) and (not isArray) then
        ParseExc(nParserDefaultPropertyMustBeArray,SParserDefaultPropertyMustBeArray);
      NextToken;
      if CurToken = tkSemicolon then
        begin
        Result.IsDefault := True;
        NextToken;
        end
      end;
    // Handle hints
    while IsCurTokenHint(h) do
      begin
      Result.Hints:=Result.Hints+[h];
      NextToken;
      if CurToken=tkSemicolon then
        NextToken;
      end;
    UngetToken;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
  Engine.FinishScope(stDeclaration,Result);
end;

// Starts after the "begin" token
procedure TPasParser.ParseProcBeginBlock(Parent: TProcedureBody);
var
  BeginBlock: TPasImplBeginBlock;
  SubBlock: TPasImplElement;
begin

  BeginBlock := TPasImplBeginBlock(CreateElement(TPasImplBeginBlock, '', Parent));
  Parent.Body := BeginBlock;
  repeat
    NextToken;
//    writeln('TPasParser.ParseProcBeginBlock ',curtokenstring);
    if CurToken=tkend then
      break
    else if CurToken<>tkSemiColon then
    begin
      UngetToken;
      ParseStatement(BeginBlock,SubBlock);
      if SubBlock=nil then
        ExpectToken(tkend);
    end;
  until false;
  ExpectToken(tkSemicolon);
//  writeln('TPasParser.ParseProcBeginBlock ended ',curtokenstring);
end;

procedure TPasParser.ParseAsmBlock(AsmBlock : TPasImplAsmStatement);
begin
  if po_asmwhole in Options then
    begin
    FTokenBufferIndex:=1;
    FTokenBufferSize:=1;
    FCommentsBuffer[0].Clear;
    repeat
      Scanner.ReadNonPascalTilEndToken(true);
      case Scanner.CurToken of
      tkLineEnding:
        AsmBlock.Tokens.Add(Scanner.CurTokenString);
      tkend:
        begin
        FTokenBuffer[0] := tkend;
        FTokenStringBuffer[0] := Scanner.CurTokenString;
        break;
        end
      else
        begin
        // missing end
        FTokenBuffer[0] := tkEOF;
        FTokenStringBuffer[0] := '';
        end;
      end;
    until false;
    FCurToken := FTokenBuffer[0];
    FCurTokenString := FTokenStringBuffer[0];
    FCurComments:=FCommentsBuffer[0];
    CheckToken(tkend);
    end
  else
    begin
    NextToken;
    While CurToken<>tkEnd do
      begin
      // ToDo: allow @@end
      AsmBlock.Tokens.Add(CurTokenText);
      NextToken;
      end;
    end;
  // NextToken; // Eat end.
  // Do not consume end. Current token will normally be end;
end;

// Next token is start of (compound) statement
// After parsing CurToken is on last token of statement
procedure TPasParser.ParseStatement(Parent: TPasImplBlock;
  out NewImplElement: TPasImplElement);
var
  CurBlock: TPasImplBlock;

  {$IFDEF VerbosePasParser}
  function i: string;
  var
    c: TPasElement;
  begin
    Result:='ParseImplCompoundStatement ';
    c:=CurBlock;
    while c<>nil do begin
      Result:=Result+'  ';
      c:=c.Parent;
    end;
  end;
  {$ENDIF}

  function CloseBlock: boolean; // true if parent reached
  begin
    if CurBlock.ClassType=TPasImplExceptOn then
      Engine.FinishScope(stExceptOnStatement,CurBlock);
    CurBlock:=CurBlock.Parent as TPasImplBlock;
    Result:=CurBlock=Parent;
  end;

  function CloseStatement(CloseIfs: boolean): boolean; // true if parent reached
  begin
    if CurBlock=Parent then exit(true);
    while CurBlock.CloseOnSemicolon
    or (CloseIfs and (CurBlock is TPasImplIfElse)) do
      if CloseBlock then exit(true);
    Result:=false;
  end;

  procedure CreateBlock(NewBlock: TPasImplBlock);
  begin
    CurBlock.AddElement(NewBlock);
    CurBlock:=NewBlock;
    if NewImplElement=nil then NewImplElement:=CurBlock;
  end;

var
  SubBlock: TPasImplElement;
  CmdElem: TPasImplElement;
  left, right: TPasExpr;
  El : TPasImplElement;
  ak : TAssignKind;
  lt : TLoopType;
  ok: Boolean;
  SrcPos: TPasSourcePos;
  Name: String;
  TypeEl: TPasType;

begin
  NewImplElement:=nil;
  CurBlock := Parent;
  while True do
  begin
    NextToken;
    //WriteLn(i,'Token=',CurTokenText);
    case CurToken of
    tkasm :
      begin
      El:=TPasImplElement(CreateElement(TPasImplAsmStatement,'',CurBlock));
      ParseAsmBlock(TPasImplAsmStatement(El));
      CurBlock.AddElement(El);
      NewImplElement:=El;
      end;
    tkbegin:
      begin
      El:=TPasImplElement(CreateElement(TPasImplBeginBlock,'',CurBlock));
      CreateBlock(TPasImplBeginBlock(El));
      end;
    tkrepeat:
      begin
      El:=TPasImplRepeatUntil(CreateElement(TPasImplRepeatUntil,'',CurBlock));
      CreateBlock(TPasImplRepeatUntil(El));
      end;
    tkIf:
      begin
        NextToken;
        Left:=DoParseExpression(CurBlock);
        UNgettoken;
        El:=TPasImplIfElse(CreateElement(TPasImplIfElse,'',CurBlock));
        TPasImplIfElse(El).ConditionExpr:=Left;
        //WriteLn(i,'IF Condition="',Condition,'" Token=',CurTokenText);
        CreateBlock(TPasImplIfElse(El));
        ExpectToken(tkthen);
      end;
    tkelse:
      if (CurBlock is TPasImplIfElse) then
      begin
        if TPasImplIfElse(CurBlock).IfBranch=nil then
        begin
        El:=TPasImplCommand(CreateElement(TPasImplCommand,'', CurBlock));
        CurBlock.AddElement(El);
        end;
        if TPasImplIfElse(CurBlock).ElseBranch<>nil then
        begin
          // this and the following 3 may solve TPasImplIfElse.AddElement BUG
          // ifs without begin end
          // if .. then
          //  if .. then
          //   else
          // else
          CloseBlock;
          CloseStatement(false);
        end;
      end else if (CurBlock is TPasImplWhileDo) then
      begin
        //if .. then while .. do smt else ..
        CloseBlock;
        UngetToken;
      end else if (CurBlock is TPasImplRaise) then
      begin
        //if .. then Raise Exception else ..
        CloseBlock;
        UngetToken;
      end else if (CurBlock is TPasImplTryExcept) then
      begin
        CloseBlock;
        El:=TPasImplTryExceptElse(CreateElement(TPasImplTryExceptElse,'',CurBlock));
        TPasImplTry(CurBlock).ElseBranch:=TPasImplTryExceptElse(El);
        CurBlock:=TPasImplTryExceptElse(El);
      end else
        ParseExcSyntaxError;
    tkwhile:
      begin
        // while Condition do
        NextToken;
        left:=DoParseExpression(Parent);
        ungettoken;
        //WriteLn(i,'WHILE Condition="',Condition,'" Token=',CurTokenText);
        El:=TPasImplWhileDo(CreateElement(TPasImplWhileDo,'',CurBlock));
        TPasImplWhileDo(El).ConditionExpr:=left;
        CreateBlock(TPasImplWhileDo(El));
        ExpectToken(tkdo);
      end;
    tkgoto:
      begin
        nexttoken;
        curblock.AddCommand('goto '+curtokenstring);
        expecttoken(tkSemiColon);
      end;
    tkfor:
      begin
        // for VarName := StartValue to EndValue do
        // for VarName in Expression do
        El:=TPasImplForLoop(CreateElement(TPasImplForLoop,'',CurBlock));
        ok:=false;
        Try
          ExpectIdentifier;
          Left:=CreatePrimitiveExpr(El,pekIdent,CurTokenString);
          Right:=Left;
          TPasImplForLoop(El).VariableName:=Left;
          repeat
            NextToken;
            case CurToken of
              tkAssign:
                begin
                lt:=ltNormal;
                break;
                end;
              tkin:
                begin
                lt:=ltIn;
                break;
                end;
              tkDot:
                begin
                ExpectIdentifier;
                AddToBinaryExprChain(Left,Right,
                  CreatePrimitiveExpr(El,pekIdent,CurTokenString), eopSubIdent);
                TPasImplForLoop(El).VariableName:=Left;
                end;
            else
              ParseExc(nParserExpectedAssignIn,SParserExpectedAssignIn);
            end;
          until false;
          NextToken;
          TPasImplForLoop(El).StartExpr:=DoParseExpression(El);
          if (Lt=ltNormal) then
            begin
            if Not (CurToken in [tkTo,tkDownTo]) then
              ParseExcTokenError(TokenInfos[tkTo]);
            if CurToken=tkdownto then
              Lt:=ltDown;
            NextToken;
            TPasImplForLoop(El).EndExpr:=DoParseExpression(El);
            end;
          TPasImplForLoop(El).LoopType:=lt;
          if (CurToken<>tkDo) then
            ParseExcTokenError(TokenInfos[tkDo]);
          ok:=true;
        finally
          if not ok then
            El.Release;
        end;
        CreateBlock(TPasImplForLoop(El));
        //WriteLn(i,'FOR "',VarName,'" := ',StartValue,' to ',EndValue,' Token=',CurTokenText);
      end;
    tkwith:
      begin
        // with Expr do
        // with Expr, Expr do
        SrcPos:=Scanner.CurSourcePos;
        NextToken;
        Left:=DoParseExpression(Parent);
        //writeln(i,'WITH Expr="',Expr,'" Token=',CurTokenText);
        El:=TPasImplWithDo(CreateElement(TPasImplWithDo,'',CurBlock,SrcPos));
        TPasImplWithDo(El).AddExpression(Left);
        CreateBlock(TPasImplWithDo(El));
        repeat
          if CurToken=tkdo then break;
          if CurToken<>tkComma then
            ParseExcTokenError(TokenInfos[tkdo]);
          NextToken;
          Left:=DoParseExpression(Parent);
          //writeln(i,'WITH ...,Expr="',Expr,'" Token=',CurTokenText);
          TPasImplWithDo(CurBlock).AddExpression(Left);
        until false;
      end;
    tkcase:
      begin
        NextToken;
        Left:=DoParseExpression(Parent);
        UngetToken;
        //writeln(i,'CASE OF Expr="',Expr,'" Token=',CurTokenText);
        ExpectToken(tkof);
        El:=TPasImplCaseOf(CreateElement(TPasImplCaseOf,'',CurBlock));
        TPasImplCaseOf(El).CaseExpr:=Left;
        Left.Parent:=El;
        CreateBlock(TPasImplCaseOf(El));
        repeat
          NextToken;
          //writeln(i,'CASE OF Token=',CurTokenText);
          case CurToken of
          tkend:
            begin
            if CurBlock.Elements.Count=0 then
              ParseExc(nParserExpectCase,SParserExpectCase);
            break; // end without else
            end;
          tkelse:
            begin
              // create case-else block
              El:=TPasImplCaseElse(CreateElement(TPasImplCaseElse,'',CurBlock));
              TPasImplCaseOf(CurBlock).ElseBranch:=TPasImplCaseElse(El);
              CreateBlock(TPasImplCaseElse(El));
              break;
            end
          else
            // read case values
            if (curToken=tkIdentifier) and (LowerCase(CurtokenString)='otherwise') then
              begin
              // create case-else block
              El:=TPasImplCaseElse(CreateElement(TPasImplCaseElse,'',CurBlock));
              TPasImplCaseOf(CurBlock).ElseBranch:=TPasImplCaseElse(El);
              CreateBlock(TPasImplCaseElse(El));
              break;
              end
            else
              repeat
                Left:=DoParseExpression(CurBlock);
                //writeln(i,'CASE value="',Expr,'" Token=',CurTokenText);
                if CurBlock is TPasImplCaseStatement then
                  TPasImplCaseStatement(CurBlock).Expressions.Add(Left)
                else
                  begin
                  El:=TPasImplCaseStatement(CreateElement(TPasImplCaseStatement,'',CurBlock));
                  TPasImplCaseStatement(El).AddExpression(Left);
                  CurBlock.AddElement(El);
                  CurBlock:=TPasImplCaseStatement(El);
                  end;
                //writeln(i,'CASE after value Token=',CurTokenText);
                if (CurToken=tkComma) then
                  NextToken
                else if (CurToken<>tkColon) then
                  ParseExcTokenError(TokenInfos[tkComma]);
              until Curtoken=tkColon;
            // read statement
            ParseStatement(CurBlock,SubBlock);
            CloseBlock;
            if CurToken<>tkSemicolon then
            begin
              NextToken;
              if not (CurToken in [tkSemicolon,tkelse,tkend]) then
                ParseExcTokenError(TokenInfos[tkSemicolon]);
              if CurToken<>tkSemicolon then
                UngetToken;
            end;
          end;
        until false;
        if CurToken=tkend then
        begin
          if CloseBlock then break;
          if CloseStatement(false) then break;
        end;
      end;
    tktry:
      begin
      El:=TPasImplTry(CreateElement(TPasImplTry,'',CurBlock));
      CreateBlock(TPasImplTry(El));
      end;
    tkfinally:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplTry then
        begin
          El:=TPasImplTryFinally(CreateElement(TPasImplTryFinally,'',CurBlock));
          TPasImplTry(CurBlock).FinallyExcept:=TPasImplTryFinally(El);
          CurBlock:=TPasImplTryFinally(El);
        end else
          ParseExcSyntaxError;
      end;
    tkexcept:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplTry then
        begin
          //writeln(i,'EXCEPT');
          El:=TPasImplTryExcept(CreateElement(TPasImplTryExcept,'',CurBlock));
          TPasImplTry(CurBlock).FinallyExcept:=TPasImplTryExcept(El);
          CurBlock:=TPasImplTryExcept(El);
        end else
          ParseExcSyntaxError;
      end;
    tkon:
      begin
        // in try except:
        // on E: Exception do
        // on Exception do
        if CurBlock is TPasImplTryExcept then
        begin
          ExpectIdentifier;
          El:=TPasImplExceptOn(CreateElement(TPasImplExceptOn,'',CurBlock));
          SrcPos:=Scanner.CurSourcePos;
          Name:=CurTokenString;
          NextToken;
          //writeln('ON t=',Name,' Token=',CurTokenText);
          if CurToken=tkColon then
            begin
            // the first expression was the variable name
            NextToken;
            TypeEl:=ParseSimpleType(El,SrcPos,'');
            TPasImplExceptOn(El).TypeEl:=TypeEl;
            TPasImplExceptOn(El).VarEl:=TPasVariable(CreateElement(TPasVariable,
                                  Name,El,SrcPos));
            TPasImplExceptOn(El).VarEl.VarType:=TypeEl;
            TypeEl.AddRef;
            end
          else
            begin
            UngetToken;
            TPasImplExceptOn(El).TypeEl:=ParseSimpleType(El,SrcPos,'');
            end;
          Engine.FinishScope(stExceptOnExpr,El);
          CurBlock.AddElement(El);
          CurBlock:=TPasImplExceptOn(El);
          ExpectToken(tkDo);
        end else
          ParseExcSyntaxError;
      end;
    tkraise:
      begin
      El:=TPasImplRaise(CreateElement(TPasImplRaise,'',CurBlock));
      CreateBlock(TPasImplRaise(El));
      NextToken;
      If Curtoken=tkSemicolon then
        UnGetToken
      else
        begin
        TPasImplRaise(El).ExceptObject:=DoParseExpression(El);
        if (CurToken=tkIdentifier) and (Uppercase(CurtokenString)='AT') then
          begin
          NextToken;
          TPasImplRaise(El).ExceptAddr:=DoParseExpression(El);
          end;
        if Curtoken in [tkSemicolon,tkEnd] then
          UngetToken
        end;
      end;
    tkend:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplBeginBlock then
        begin
          if CloseBlock then break; // close end
          if CloseStatement(false) then break;
        end else if CurBlock is TPasImplCaseElse then
        begin
          if CloseBlock then break; // close else
          if CloseBlock then break; // close caseof
          if CloseStatement(false) then break;
        end else if CurBlock is TPasImplTryHandler then
        begin
          if CloseBlock then break; // close finally/except
          if CloseBlock then break; // close try
          if CloseStatement(false) then break;
        end else
          ParseExcSyntaxError;
      end;
    tkSemiColon:
      if CloseStatement(true) then break;
    tkuntil:
      begin
        if CloseStatement(true) then
        begin
          UngetToken;
          break;
        end;
        if CurBlock is TPasImplRepeatUntil then
        begin
          NextToken;
          Left:=DoParseExpression(Parent);
          UngetToken;
          TPasImplRepeatUntil(CurBlock).ConditionExpr:=Left;
          //WriteLn(i,'UNTIL Condition="',Condition,'" Token=',CurTokenString);
          if CloseBlock then break;
        end else
          ParseExcSyntaxError;
      end;
    else
      left:=DoParseExpression(Parent);
      case CurToken of
        tkAssign,
        tkAssignPlus,
        tkAssignMinus,
        tkAssignMul,
        tkAssignDivision:
        begin
          // assign statement
          Ak:=TokenToAssignKind(CurToken);
          NextToken;
          right:=DoParseExpression(Parent); // this may solve TPasImplWhileDo.AddElement BUG
          El:=TPasImplAssign(CreateElement(TPasImplAssign,'',CurBlock));
          left.Parent:=El;
          right.Parent:=El;
          TPasImplAssign(El).left:=Left;
          TPasImplAssign(El).right:=Right;
          TPasImplAssign(El).Kind:=ak;
          CurBlock.AddElement(El);
          CmdElem:=TPasImplAssign(El);
          UngetToken;
        end;
        tkColon:
        begin
          if not (left is TPrimitiveExpr) then
            ParseExcTokenError(TokenInfos[tkSemicolon]);
          // label mark. todo: check mark identifier in the list of labels
          El:=TPasImplLabelMark(CreateElement(TPasImplLabelMark,'', CurBlock));
          TPasImplLabelMark(El).LabelId:=TPrimitiveExpr(left).Value;
          CurBlock.AddElement(El);
          CmdElem:=TPasImplLabelMark(El);
          left.Free;
        end;
      else
        // simple statement (function call)
        El:=TPasImplSimple(CreateElement(TPasImplSimple,'',CurBlock));
        TPasImplSimple(El).expr:=Left;
        CurBlock.AddElement(El);
        CmdElem:=TPasImplSimple(El);
        UngetToken;
      end;

      if not (CmdElem is TPasImplLabelMark) then
        if NewImplElement=nil then NewImplElement:=CmdElem;
    end;
  end;
end;

procedure TPasParser.ParseLabels(AParent: TPasElement);
var
  Labels: TPasLabels;
begin
  Labels:=TPasLabels(CreateElement(TPasLabels, '', AParent));
  repeat
    Labels.Labels.Add(ExpectIdentifier);
    NextToken;
    if not (CurToken in [tkSemicolon, tkComma]) then
      ParseExcTokenError(TokenInfos[tkSemicolon]);
  until CurToken=tkSemicolon;
end;

// Starts after the "procedure" or "function" token
function TPasParser.GetProcedureClass(ProcType: TProcType): TPTreeElement;

begin
  Case ProcType of
    ptFunction       : Result:=TPasFunction;
    ptClassFunction  : Result:=TPasClassFunction;
    ptClassProcedure : Result:=TPasClassProcedure;
    ptClassConstructor : Result:=TPasClassConstructor;
    ptClassDestructor  : Result:=TPasClassDestructor;
    ptProcedure      : Result:=TPasProcedure;
    ptConstructor    : Result:=TPasConstructor;
    ptDestructor     : Result:=TPasDestructor;
    ptOperator       : Result:=TPasOperator;
    ptClassOperator  : Result:=TPasClassOperator;
  else
    ParseExc(nParserUnknownProcedureType,SParserUnknownProcedureType,[Ord(ProcType)]);
  end;
end;

function TPasParser.ParseProcedureOrFunctionDecl(Parent: TPasElement; ProcType: TProcType;AVisibility : TPasMemberVisibility = VisDefault): TPasProcedure;

  function ExpectProcName: string;
  begin
    Result:=ExpectIdentifier;
    //writeln('ExpectProcName ',Parent.Classname);
    if Parent is TImplementationSection then
    begin
      NextToken;
      if CurToken=tkDot then
      begin
        Result:=Result+'.'+ExpectIdentifier;
      end else
        UngetToken;
    end;
  end;

var
  Name: String;
  PC : TPTreeElement;
  Ot : TOperatorType;
  IsTokenBased , ok: Boolean;

begin
  If (Not (ProcType in [ptOperator,ptClassOperator])) then
    Name:=ExpectProcName
  else
    begin
    NextToken;
    IsTokenBased:=Curtoken<>tkIdentifier;
    if IsTokenBased then
      OT:=TPasOperator.TokenToOperatorType(CurTokenText)
    else
      OT:=TPasOperator.NameToOperatorType(CurTokenString);
    if (ot=otUnknown) then
      ParseExc(nErrUnknownOperatorType,SErrUnknownOperatorType,[CurTokenString]);
    Name:=OperatorNames[Ot];
    end;
  PC:=GetProcedureClass(ProcType);
  Parent:=CheckIfOverLoaded(Parent,Name);
  Result:=TPasProcedure(CreateElement(PC,Name,Parent,AVisibility));
  ok:=false;
  try
    if Not (ProcType in [ptFunction, ptClassFunction, ptOperator, ptClassOperator]) then
      Result.ProcType := TPasProcedureType(CreateElement(TPasProcedureType, '', Result))
    else
      begin
      Result.ProcType := CreateFunctionType('', 'Result', Result, True);
      if (ProcType in [ptOperator, ptClassOperator]) then
        begin
        TPasOperator(Result).TokenBased:=IsTokenBased;
        TPasOperator(Result).OperatorType:=OT;
        TPasOperator(Result).CorrectName;
        end;
      end;
    ParseProcedureOrFunctionHeader(Result, Result.ProcType, ProcType, False);
    Result.Hints:=Result.ProcType.Hints;
    Result.HintMessage:=Result.ProcType.HintMessage;
    // + is detected as 'positive', but is in fact Add if there are 2 arguments.
    if (ProcType in [ptOperator, ptClassOperator]) then
      With TPasOperator(Result) do
        begin
        if (OperatorType in [otPositive, otNegative]) then
          begin
          if (ProcType.Args.Count>1) then
            begin
            Case OperatorType of
              otPositive : OperatorType:=otPlus;
              otNegative : OperatorType:=otMinus;
            end;
            Name:=OperatorNames[OperatorType];
            TPasOperator(Result).CorrectName;
            end;
          end;
        end;
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

// Current token is the first token after tkOf
procedure TPasParser.ParseRecordVariantParts(ARec: TPasRecordType;
  AEndToken: TToken);

Var
  M : TPasRecordType;
  V : TPasVariant;
  Done : Boolean;

begin
  Repeat
    V:=TPasVariant(CreateElement(TPasVariant, '', ARec));
    ARec.Variants.Add(V);
    Repeat
      NextToken;
      V.Values.Add(DoParseExpression(ARec));
      if Not (CurToken in [tkComma,tkColon]) then
        ParseExc(nParserExpectedCommaColon,SParserExpectedCommaColon);
    Until (curToken=tkColon);
    ExpectToken(tkBraceOpen);
    NextToken;
    M:=TPasRecordType(CreateElement(TPasRecordType,'',V));
    V.Members:=M;
    ParseRecordFieldList(M,tkBraceClose,False);
    // Current token is closing ), so we eat that
    NextToken;
    // If there is a semicolon, we eat that too.
    if CurToken=tkSemicolon then
      NextToken;
    // ParseExpression starts with a nexttoken.
    // So we need to determine the next token, and if it is an ending token, unget.
    Done:=CurToken=AEndToken;
    If not Done then
      Ungettoken;
  Until Done;
end;

procedure TPasParser.DumpCurToken(const Msg: String; IndentAction: TIndentAction
  );
begin
  if IndentAction=iaUndent then
    FDumpIndent:=copy(FDumpIndent,1,Length(FDumpIndent)-2);
  Writeln(FDumpIndent,Msg,' : ',TokenInfos[CurToken],' "',CurTokenString,'", Position: ',Scanner.CurFilename,'(',Scanner.CurRow,',',SCanner.CurColumn,') : ',Scanner.CurLine);
  if IndentAction=iaIndent then
    FDumpIndent:=FDumpIndent+'  ';
  Flush(output);
end;

// Starts on first token after Record or (. Ends on AEndToken
procedure TPasParser.ParseRecordFieldList(ARec: TPasRecordType;
  AEndToken: TToken; AllowMethods: Boolean);

Var
  VariantName : String;
  v : TPasmemberVisibility;
  Proc: TPasProcedure;
  ProcType: TProcType;
  Prop : TPasProperty;
  Cons : TPasConst;
  isClass : Boolean;
  NamePos: TPasSourcePos;
begin
  v:=visDefault;
  isClass:=False;
  while CurToken<>AEndToken do
    begin
    SaveComments;
    Case CurToken of
      tkConst:
        begin
        if Not AllowMethods then
          ParseExc(nErrRecordConstantsNotAllowed,SErrRecordConstantsNotAllowed);
        ExpectToken(tkIdentifier);
        Cons:=ParseConstDecl(ARec);
        Cons.Visibility:=v;
        ARec.members.Add(Cons);
        end;
      tkClass:
        begin
        if Not AllowMethods then
          ParseExc(nErrRecordMethodsNotAllowed,SErrRecordMethodsNotAllowed);
        if isClass then
          ParseExc(nParserTypeSyntaxError,SParserTypeSyntaxError);
        isClass:=True;
        end;
      tkProperty:
        begin
        if Not AllowMethods then
          ParseExc(nErrRecordPropertiesNotAllowed,SErrRecordPropertiesNotAllowed);
        ExpectToken(tkIdentifier);
        Prop:=ParseProperty(ARec,CurtokenString,v);
        Prop.isClass:=isClass;
        Arec.Members.Add(Prop);
        end;
      tkOperator,
      tkProcedure,
      tkFunction :
        begin
        if Not AllowMethods then
          ParseExc(nErrRecordMethodsNotAllowed,SErrRecordMethodsNotAllowed);
        ProcType:=GetProcTypeFromToken(CurToken,isClass);
        Proc:=ParseProcedureOrFunctionDecl(ARec,ProcType,v);
        if Proc.Parent is TPasOverloadedProc then
          TPasOverloadedProc(Proc.Parent).Overloads.Add(Proc)
        else
          ARec.Members.Add(Proc);
        end;
      tkIdentifier :
        begin
//        If (po_delphi in Scanner.Options) then
          if CheckVisibility(CurtokenString,v) then
            begin
            If not (po_delphi in Scanner.Options) then
              ParseExc(nErrRecordVisibilityNotAllowed,SErrRecordVisibilityNotAllowed);
            if not (v in [visPrivate,visPublic,visStrictPrivate]) then
              ParseExc(nParserInvalidRecordVisibility,SParserInvalidRecordVisibility);
            NextToken;
            Continue;
            end;
        ParseInlineVarDecl(ARec, ARec.Members, v, AEndToken=tkBraceClose);
        end;
      tkCase :
        begin
        ARec.Variants:=TFPList.Create;
        NextToken;
        VariantName:=CurTokenString;
        NamePos:=Scanner.CurSourcePos;
        NextToken;
        If CurToken=tkColon then
          begin
          ARec.VariantEl:=TPasVariable(CreateElement(TPasVariable,VariantName,ARec,NamePos));
          TPasVariable(ARec.VariantEl).VarType:=ParseType(ARec,Scanner.CurSourcePos);
          end
        else
          begin
          UnGetToken;
          UnGetToken;
          ARec.VariantEl:=ParseType(ARec,Scanner.CurSourcePos);
          end;
        ExpectToken(tkOf);
        ParseRecordVariantParts(ARec,AEndToken);
        end;
    else
      ParseExc(nParserTypeSyntaxError,SParserTypeSyntaxError);
    end;
    If CurToken<>tkClass then
      isClass:=False;
    if CurToken<>AEndToken then
      NextToken;
    end;
end;

// Starts after the "record" token
function TPasParser.ParseRecordDecl(Parent: TPasElement;
  const NamePos: TPasSourcePos; const TypeName: string;
  const Packmode: TPackMode): TPasRecordType;

var
  ok: Boolean;
begin
  Result := TPasRecordType(CreateElement(TPasRecordType, TypeName, Parent, NamePos));
  ok:=false;
  try
    Result.PackMode:=PackMode;
    NextToken;
    ParseRecordFieldList(Result,tkEnd,true);
    Engine.FinishScope(stTypeDef,Result);
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

Function IsVisibility(S : String;  var AVisibility :TPasMemberVisibility) : Boolean;

Const
  VNames : array[TPasMemberVisibility] of string =
    ('', 'private', 'protected', 'public', 'published', 'automated', '', '');
Var
  V : TPasMemberVisibility;

begin
  Result:=False;
  S:=lowerCase(S);
  For V :=Low(TPasMemberVisibility) to High(TPasMemberVisibility) do
    begin
    Result:=(VNames[V]<>'') and (S=VNames[V]);
    if Result then
      begin
      AVisibility := v;
      Exit;
      end;
    end;
end;

function TPasParser.CheckVisibility(S: String;
  var AVisibility: TPasMemberVisibility): Boolean;

Var
  B : Boolean;

begin
  s := LowerCase(CurTokenString);
  B:=(S='strict');
  if B then
    begin
    NextToken;
    s:=LowerCase(CurTokenString);
    end;
  Result:=isVisibility(S,AVisibility);
  if Result then
    begin
    if B then
      case AVisibility of
        visPrivate   : AVisibility:=visStrictPrivate;
        visProtected : AVisibility:=visStrictProtected;
      else
        ParseExc(nParserStrangeVisibility,SParserStrangeVisibility,[S]);
      end
    end
  else if B then
    ParseExc(nParserExpectVisibility,SParserExpectVisibility);
end;

procedure TPasParser.ProcessMethod(AType: TPasClassType; IsClass : Boolean; AVisibility : TPasMemberVisibility);

var
  Proc: TPasProcedure;
  ProcType: TProcType;
begin
  ProcType:=GetProcTypeFromToken(CurToken,isClass);
  Proc:=ParseProcedureOrFunctionDecl(AType,ProcType,AVisibility);
  if Proc.Parent is TPasOverloadedProc then
    TPasOverloadedProc(Proc.Parent).Overloads.Add(Proc)
  else
    AType.Members.Add(Proc);
end;

procedure TPasParser.ParseClassFields(AType: TPasClassType;
  const AVisibility: TPasMemberVisibility; IsClassField: Boolean);

Var
  VarList: TFPList;
  Element: TPasElement;
  I : Integer;

begin
  VarList := TFPList.Create;
  try
    ParseInlineVarDecl(AType, VarList, AVisibility, False);
    for i := 0 to VarList.Count - 1 do
      begin
      Element := TPasElement(VarList[i]);
      Element.Visibility := AVisibility;
      if IsClassField and (Element is TPasVariable) then
        TPasVariable(Element).VarModifiers:=TPasVariable(Element).VarModifiers+[vmClass];
      AType.Members.Add(Element);
      end;
  finally
    VarList.Free;
  end;
end;

procedure TPasParser.ParseClassLocalTypes(AType: TPasClassType; AVisibility : TPasMemberVisibility);

Var
  T : TPasType;
  Done : Boolean;
begin
//  Writeln('Parsing local types');
  Repeat
    T:=ParseTypeDecl(AType);
    T.Visibility:=AVisibility;
    AType.Members.Add(t);
//    Writeln(CurtokenString,' ',TokenInfos[Curtoken]);
    NextToken;
    Done:=(Curtoken<>tkIdentifier) or CheckVisibility(CurtokenString,AVisibility);
    if Done then
      UngetToken;
  Until Done;
end;

procedure TPasParser.ParseClassLocalConsts(AType: TPasClassType; AVisibility : TPasMemberVisibility);

Var
  C : TPasConst;
  Done : Boolean;
begin
//  Writeln('Parsing local consts');
  Repeat
    C:=ParseConstDecl(AType);
    C.Visibility:=AVisibility;
    AType.Members.Add(C);
//    Writeln(CurtokenString,' ',TokenInfos[Curtoken]);
    NextToken;
    Done:=(Curtoken<>tkIdentifier) or CheckVisibility(CurtokenString,AVisibility);
    if Done then
      UngetToken;
  Until Done;
end;

procedure TPasParser.ParseClassMembers(AType: TPasClassType);

Var
  CurVisibility : TPasMemberVisibility;

begin
  CurVisibility := visDefault;
  while (CurToken<>tkEnd) do
    begin
    case CurToken of
      tkType:
        begin
        ExpectToken(tkIdentifier);
        SaveComments;
        ParseClassLocalTypes(AType,CurVisibility);
        end;
      tkConst:
        begin
        ExpectToken(tkIdentifier);
        SaveComments;
        ParseClassLocalConsts(AType,CurVisibility);
        end;
      tkVar,
      tkIdentifier:
        begin
        if (AType.ObjKind=okInterface) then
          ParseExc(nParserNoFieldsAllowed,SParserNoFieldsAllowed);
        if CurToken=tkVar then
          ExpectToken(tkIdentifier);
        SaveComments;
        if Not CheckVisibility(CurtokenString,CurVisibility) then
          ParseClassFields(AType,CurVisibility,false);
        end;
      tkProcedure,tkFunction,tkConstructor,tkDestructor:
        begin
        SaveComments;
        if (Curtoken in [tkConstructor,tkDestructor]) and (AType.ObjKind in [okInterface,okRecordHelper]) then
          ParseExc(nParserNoConstructorAllowed,SParserNoConstructorAllowed);
        ProcessMethod(AType,False,CurVisibility);
        end;
      tkclass:
        begin
         SaveComments;
         NextToken;
         if CurToken in [tkConstructor,tkDestructor,tkprocedure,tkFunction] then
           ProcessMethod(AType,True,CurVisibility)
         else if CurToken = tkVar then
           begin
           ExpectToken(tkIdentifier);
           ParseClassFields(AType,CurVisibility,true);
           end
         else if CurToken=tkProperty then
           begin
           ExpectToken(tkIdentifier);
           AType.Members.Add(ParseProperty(AType,CurtokenString,CurVisibility));
           end
         else
           ParseExc(nParserTypeSyntaxError,SParserTypeSyntaxError)
        end;
      tkProperty:
        begin
        SaveComments;
        ExpectIdentifier;
        AType.Members.Add(ParseProperty(AType,CurtokenString,CurVisibility));
        end;
    end;
    NextToken;
    end;
end;
procedure TPasParser.DoParseClassType(AType: TPasClassType);

var
  Element : TPasElement;
  s: String;

begin
  // nettism/new delphi features
  if (CurToken=tkIdentifier) and (Atype.ObjKind in [okClass,okGeneric]) then
    begin
    s := LowerCase(CurTokenString);
    if (s = 'sealed') or (s = 'abstract') then
      begin
      AType.Modifiers.Add(s);
      NextToken;
      end;
    end;
  // Parse ancestor list
  AType.IsForward:=(CurToken=tkSemiColon);
  if (CurToken=tkBraceOpen) then
    begin
    AType.AncestorType := ParseType(AType,Scanner.CurSourcePos);
    while True do
      begin
      NextToken;
      if CurToken = tkBraceClose then
        break;
      UngetToken;
      ExpectToken(tkComma);
      Element:=ParseType(AType,Scanner.CurSourcePos); // search interface.
      if assigned(element) then
        AType.Interfaces.add(element);
      end;
    NextToken;
    AType.IsShortDefinition:=(CurToken=tkSemicolon);
    end;
  if (AType.ObjKind in [okClassHelper,okRecordHelper]) then
    begin
    if (CurToken<>tkFor) then
      ParseExcTokenError(TokenInfos[tkFor]);
    AType.HelperForType:=ParseType(AType,Scanner.CurSourcePos);
    NextToken;
    end;
  Engine.FinishScope(stAncestors,AType);
  if (AType.IsShortDefinition or AType.IsForward) then
    UngetToken
  else
    begin
    if (AType.ObjKind=okInterface) and (CurToken = tkSquaredBraceOpen) then
      begin
      NextToken;
      AType.GUIDExpr:=DoParseExpression(AType);
      if (CurToken<>tkSquaredBraceClose) then
        ParseExcTokenError(TokenInfos[tkSquaredBraceClose]);
      NextToken;
      end;
    ParseClassMembers(AType);
    end;
end;

function TPasParser.ParseClassDecl(Parent: TPasElement;
  const NamePos: TPasSourcePos; const AClassName: String;
  AObjKind: TPasObjKind; PackMode: TPackMode): TPasType;

Var
  ok: Boolean;

begin
  NextToken;

  if (AObjKind = okClass) and (CurToken = tkOf) then
    begin
    Result := TPasClassOfType(CreateElement(TPasClassOfType, AClassName,
      Parent, NamePos));
    ExpectIdentifier;
    UngetToken;                // Only names are allowed as following type
    TPasClassOfType(Result).DestType := ParseType(Result,Scanner.CurSourcePos);
    exit;
    end;
  if (CurToken = tkHelper) then
    begin
    if Not (AObjKind in [okClass,okRecordHelper]) then
      ParseExc(nParserHelperNotAllowed,SParserHelperNotAllowed,[ObjKindNames[AObjKind]]);
    if (AObjKind = okClass)  then
      AObjKind:=okClassHelper;
    NextToken;
    end;
  Result := TPasClassType(CreateElement(TPasClassType, AClassName,
    Parent, NamePos));

  ok:=false;
  try
    TPasClassType(Result).ObjKind := AObjKind;
    TPasClassType(Result).PackMode:=PackMode;
    DoParseClassType(TPasClassType(Result));
    Engine.FinishScope(stTypeDef,Result);
    ok:=true;
  finally
    if not ok then
      Result.Release;
  end;
end;

function TPasParser.CreateElement(AClass: TPTreeElement; const AName: String;
  AParent: TPasElement): TPasElement;
begin
  Result := Engine.CreateElement(AClass, AName, AParent, visDefault, Scanner.CurSourcePos);
end;

function TPasParser.CreateElement(AClass: TPTreeElement; const AName: String;
  AParent: TPasElement; const ASrcPos: TPasSourcePos): TPasElement;
begin
  Result := Engine.CreateElement(AClass, AName, AParent, visDefault, ASrcPos);
end;

function TPasParser.CreateElement(AClass: TPTreeElement; const AName: String;
  AParent: TPasElement; AVisibility: TPasMemberVisibility): TPasElement;
begin
  Result := Engine.CreateElement(AClass, AName, AParent, AVisibility,
    Scanner.CurSourcePos);
end;

function TPasParser.CreateElement(AClass: TPTreeElement; const AName: String;
  AParent: TPasElement; AVisibility: TPasMemberVisibility;
  const ASrcPos: TPasSourcePos): TPasElement;
begin
  Result := Engine.CreateElement(AClass, AName, AParent, AVisibility, ASrcPos);
end;

function TPasParser.CreatePrimitiveExpr(AParent: TPasElement;
  AKind: TPasExprKind; const AValue: String): TPrimitiveExpr;
begin
  Result:=TPrimitiveExpr(CreateElement(TPrimitiveExpr,'',AParent));
  Result.Kind:=AKind;
  Result.Value:=AValue;
end;

function TPasParser.CreateBoolConstExpr(AParent: TPasElement;
  AKind: TPasExprKind; const ABoolValue: Boolean): TBoolConstExpr;
begin
  Result:=TBoolConstExpr(CreateElement(TBoolConstExpr,'',AParent));
  Result.Kind:=AKind;
  Result.Value:=ABoolValue;
end;

function TPasParser.CreateBinaryExpr(AParent: TPasElement; xleft,
  xright: TPasExpr; AOpCode: TExprOpCode): TBinaryExpr;
begin
  Result:=TBinaryExpr(CreateElement(TBinaryExpr,'',AParent));
  Result.OpCode:=AOpCode;
  Result.Kind:=pekBinary;
  if xleft<>nil then
    begin
    Result.left:=xleft;
    xleft.Parent:=Result;
    end;
  if xright<>nil then
    begin
    Result.right:=xright;
    xright.Parent:=Result;
    end;
end;

procedure TPasParser.AddToBinaryExprChain(var ChainFirst, ChainLast: TPasExpr;
  Element: TPasExpr; AOpCode: TExprOpCode);

  procedure RaiseInternal;
  begin
    raise Exception.Create('TBinaryExpr.AddToChain: internal error');
  end;

var
  Last: TBinaryExpr;
begin
  if Element=nil then
    exit
  else if ChainFirst=nil then
    begin
    // empty chain => simply add element, no need to create TBinaryExpr
    if (ChainLast<>nil) then
      RaiseInternal;
    ChainFirst:=Element;
    ChainLast:=Element;
    end
  else if ChainLast is TBinaryExpr then
    begin
    // add a new TBinaryExpr at the end of the chain
    Last:=TBinaryExpr(ChainLast);
    if (Last.left=nil) or (Last.right=nil) then
      // chain not yet full => inconsistency
      RaiseInternal;
    Last.right:=CreateBinaryExpr(Last,Last.right,Element,AOpCode);
    ChainLast:=Last;
    end
  else
    begin
    // one element => create a TBinaryExpr with two elements
    if ChainFirst<>ChainLast then
      RaiseInternal;
    ChainLast:=CreateBinaryExpr(ChainLast.Parent,ChainLast,Element,AOpCode);
    ChainFirst:=ChainLast;
    end;
end;

procedure TPasParser.AddParamsToBinaryExprChain(var ChainFirst,
  ChainLast: TPasExpr; Params: TParamsExpr);
// append Params to chain, using the last element as Params.Value
var
  Bin: TBinaryExpr;
begin
  if Params.Value<>nil then
    ParseExcSyntaxError;
  if ChainLast=nil then
    ParseExcSyntaxError;
  if ChainLast is TBinaryExpr then
    begin
    Bin:=TBinaryExpr(ChainLast);
    if Bin.left=nil then
      ParseExcSyntaxError;
    if Bin.right=nil then
      ParseExcSyntaxError;
    Params.Value:=Bin.right;
    Params.Value.Parent:=Params;
    Bin.right:=Params;
    Params.Parent:=Bin;
    end
  else
    begin
    if ChainFirst<>ChainLast then
      ParseExcSyntaxError;
    Params.Value:=ChainFirst;
    Params.Parent:=ChainFirst.Parent;
    ChainFirst.Parent:=Params;
    ChainFirst:=Params;
    ChainLast:=Params;
    end;
end;

function TPasParser.CreateUnaryExpr(AParent: TPasElement; AOperand: TPasExpr;
  AOpCode: TExprOpCode): TUnaryExpr;
begin
  Result:=TUnaryExpr(CreateElement(TUnaryExpr,'',AParent));
  Result.Kind:=pekUnary;
  Result.Operand:=AOperand;
  Result.Operand.Parent:=Result;
  Result.OpCode:=AOpCode;
end;

function TPasParser.CreateArrayValues(AParent: TPasElement): TArrayValues;
begin
  Result:=TArrayValues(CreateElement(TArrayValues,'',AParent));
  Result.Kind:=pekListOfExp;
end;

function TPasParser.CreateFunctionType(const AName, AResultName: String;
  AParent: TPasElement; UseParentAsResultParent: Boolean): TPasFunctionType;
begin
  Result:=Engine.CreateFunctionType(AName,AResultName,
                                    AParent,UseParentAsResultParent,
                                    Scanner.CurSourcePos);
end;

function TPasParser.CreateInheritedExpr(AParent: TPasElement): TInheritedExpr;
begin
  Result:=TInheritedExpr(CreateElement(TInheritedExpr,'',AParent));
  Result.Kind:=pekInherited;
end;

function TPasParser.CreateSelfExpr(AParent: TPasElement): TSelfExpr;
begin
  Result:=TSelfExpr(CreateElement(TSelfExpr,'Self',AParent));
  Result.Kind:=pekSelf;
end;

function TPasParser.CreateNilExpr(AParent: TPasElement): TNilExpr;
begin
  Result:=TNilExpr(CreateElement(TNilExpr,'nil',AParent));
  Result.Kind:=pekNil;
end;

function TPasParser.CreateRecordValues(AParent: TPasElement): TRecordValues;
begin
  Result:=TRecordValues(CreateElement(TRecordValues,'',AParent));
  Result.Kind:=pekListOfExp;
end;

end.
