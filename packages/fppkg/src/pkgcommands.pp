unit pkgcommands;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, pkghandler, fpmkunit;

implementation

uses
  zipper,
  pkgmessages,
  pkgglobals,
  pkgoptions,
  pkgdownload,
  pkgrepos,
  pkgFppkg,
  fpxmlrep,
  fprepos;

type
  { TCommandAddConfig }

  TCommandAddConfig = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandUpdate }

  TCommandUpdate = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandListPackages }

  TCommandListPackages = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandScanPackages }

  TCommandScanPackages = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandDownload }

  TCommandDownload = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandUnzip }

  TCommandUnzip = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandCompile }

  TCommandCompile = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandBuild }

  TCommandBuild = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandInstall }

  TCommandInstall = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandUnInstall }

  TCommandUnInstall = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandClean }

  TCommandClean = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandArchive }

  TCommandArchive = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandInstallDependencies }

  TCommandInstallDependencies = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandFixBroken }

  TCommandFixBroken = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandListSettings }

  TCommandListSettings = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

  { TCommandInfo }

  TCommandInfo = Class(TPackagehandler)
  Public
    Procedure Execute;override;
  end;

var
  DependenciesDepth: integer;

{ TCommandInfo }

procedure TCommandInfo.Execute;
var
  P : TFPPackage;
  S : string;
  I : Integer;
begin
  if PackageName='' then
    Error(SErrNoPackageSpecified);
  P:=GFPpkg.PackageByName(PackageName, pkgpkAvailable);

  log(llProgres,SLogPackageInfoName,[P.Name]);
  S := P.Email;
  if S <> '' then
    S := '<' + S +'>';
  log(llProgres,SLogPackageInfoAuthor,[P.Author, S]);
  log(llProgres,SLogPackageInfoVersion,[P.Version.AsString]);
  log(llProgres,SLogPackageInfoCategory,[P.Category]);
  log(llProgres,SLogPackageInfoWebsite,[P.HomepageURL]);
  log(llProgres,SLogPackageInfoLicense,[P.License]);

  log(llProgres,SLogPackageInfoOSes,[OSesToString(P.OSes)]);
  log(llProgres,SLogPackageInfoCPUs,[CPUSToString(P.CPUs)]);

  log(llProgres,SLogPackageInfoDescription1);
  log(llProgres,SLogPackageInfoDescription2,[P.Description]);

  if P.Dependencies.Count>0 then
    begin
      log(llProgres,SLogPackageInfoDependencies1,[]);
      for I := 0 to P.Dependencies.Count-1 do
        begin
          if not P.Dependencies[I].MinVersion.Empty then
            S := '('+P.Dependencies[I].MinVersion.AsString+')'
          else
            S := '';
          log(llProgres,SLogPackageInfoDependencies2,[P.Dependencies[I].PackageName,S]);
        end;
    end;
end;

{ TCommandUnInstall }

procedure TCommandUnInstall.Execute;
var
  AvailP: TFPPackage;
begin
  if PackageName<>'' then
    begin
      if (PackageName=CmdLinePackageName) then
        begin
          ExecuteAction(PackageName,'unzip');
        end
      else if (PackageName<>CurrentDirPackageName) then
        begin
          AvailP:=GFPpkg.FindPackage(PackageName, pkgpkAvailable);
          if Assigned(AvailP) then
            begin
              if AvailP.PackagesStructure.UnzipBeforeUse then
                ExecuteAction(PackageName,'unzip');
            end;
        end;
    end;
  ExecuteAction(PackageName,'fpmakeuninstall');
end;

{ TCommandListSettings }

procedure TCommandListSettings.Execute;
begin
  GFPpkg.Options.LogValues(llProgres);
  GFPpkg.CompilerOptions.LogValues(llProgres,'');
  GFPpkg.FPMakeCompilerOptions.LogValues(llProgres,'fpmake-building ');
end;


procedure TCommandAddConfig.Execute;
begin
{
  Log(llInfo,SLogGeneratingCompilerConfig,[S]);
  Options.InitCompilerDefaults(Args[2]);
  Options.SaveCompilerToFile(S);
}
end;


procedure TCommandUpdate.Execute;
var
  PackagesURL :  String;
begin
  // Download and load mirrors.xml
  // This can be skipped when a custom RemoteRepository is configured
  if (GFPpkg.Options.GlobalSection.RemoteMirrorsURL<>'') and
     (GFPpkg.Options.GlobalSection.RemoteRepository='auto') then
    begin
      Log(llCommands,SLogDownloading,[GFPpkg.Options.GlobalSection.RemoteMirrorsURL,GFPpkg.Options.GlobalSection.LocalMirrorsFile]);
      DownloadFile(GFPpkg.Options.GlobalSection.RemoteMirrorsURL,GFPpkg.Options.GlobalSection.LocalMirrorsFile);
      LoadLocalAvailableMirrors;
    end;
  // Download packages.xml
  PackagesURL:=GetRemoteRepositoryURL(PackagesFileName);
  Log(llCommands,SLogDownloading,[PackagesURL,GFPpkg.Options.GlobalSection.LocalPackagesFile]);
  DownloadFile(PackagesURL,GFPpkg.Options.GlobalSection.LocalPackagesFile);
  // Read the repository again
  GFPpkg.ScanAvailablePackages;
  // no need to log errors again
  FindInstalledPackages(GFPpkg.CompilerOptions,False);
end;


procedure TCommandListPackages.Execute;
begin
  ListPackages(GFPpkg.Options.CommandLineSection.ShowLocation);
end;


procedure TCommandScanPackages.Execute;
begin
  { nothing, already handled in fppkg.pp as special case
    before the local fppkg directory is processed }
end;


procedure TCommandDownload.Execute;
var
  P : TFPPackage;
begin
  if PackageName='' then
    Error(SErrNoPackageSpecified);
  P:=GFPpkg.PackageByName(PackageName, pkgpkAvailable);
  if not FileExists(PackageLocalArchive(P)) then
    ExecuteAction(PackageName,'downloadpackage');
end;


procedure TCommandUnzip.Execute;
Var
  BuildDir : string;
  ArchiveFile : String;
  P : TFPPackage;
begin
  if PackageName='' then
    Error(SErrNoPackageSpecified);
  P:=GFPpkg.PackageByName(PackageName, pkgpkAvailable);
  BuildDir:=PackageBuildPath(P);
  ArchiveFile:=PackageLocalArchive(P);
  if not FileExists(ArchiveFile) then
    ExecuteAction(PackageName,'downloadpackage');
  { Create builddir, remove it first if needed }
  if DirectoryExists(BuildDir) then
    DeleteDir(BuildDir);
  ForceDirectories(BuildDir);
  SetCurrentDir(BuildDir);
  { Unzip Archive }
  With TUnZipper.Create do
    try
      Log(llCommands,SLogUnzippping,[ArchiveFile]);
      OutputPath:=PackageBuildPath(P);
      UnZipAllFiles(ArchiveFile);
    Finally
      Free;
    end;
end;


procedure TCommandCompile.Execute;
begin
  if PackageName<>'' then
    begin
      // For local files we need the information inside the zip to get the
      // dependencies
      if (PackageName=CmdLinePackageName) or (PackageName=URLPackageName) then
        begin
          ExecuteAction(PackageName,'unzip');
          ExecuteAction(PackageName,'installdependencies');
        end
      else
        if (PackageName=CurrentDirPackageName) then
          begin
            ExecuteAction(PackageName,'installdependencies');
          end
      else
        begin
          ExecuteAction(PackageName,'installdependencies');
          ExecuteAction(PackageName,'unzip');
        end;
    end;
  ExecuteAction(PackageName,'fpmakecompile');
end;


procedure TCommandBuild.Execute;
var
  P: TFPPackage;
begin
  if PackageName<>'' then
    begin
      // For local files we need the information inside the zip to get the
      // dependencies
      if (PackageName=CmdLinePackageName) or (PackageName=URLPackageName) then
        begin
          ExecuteAction(PackageName,'unzip');
          ExecuteAction(PackageName,'installdependencies');
        end
      else
        if (PackageName=CurrentDirPackageName) then
          begin
            ExecuteAction(PackageName,'installdependencies');
          end
      else
        begin
          P:=GFPpkg.FindPackage(PackageName, pkgpkAvailable);
          if Assigned(P) then
            begin
              if P.PackagesStructure.UnzipBeforeUse then
                ExecuteAction(PackageName,'unzip');
            end;
          ExecuteAction(PackageName,'installdependencies');
        end;
    end;
  ExecuteAction(PackageName,'fpmakebuild');
end;


procedure TCommandInstall.Execute;

var
  S : String;
  P   : TFPPackage;
  InstallRepo: TFPRepository;

  function GetFpmFilename: string;
  var
    ConfFile: string;
  begin
    Result := '';
    if Assigned(InstallRepo.DefaultPackagesStructure) then
      begin
        Result := InstallRepo.DefaultPackagesStructure.GetBaseInstallDir;
        ConfFile := IncludeTrailingPathDelimiter(Result)+'fpmkinst'+PathDelim+GFPpkg.CompilerOptions.CompilerTarget+PathDelim+s+FpmkExt;
        if not FileExistsLog(ConfFile) then
          begin
            // If there is no fpm-file, search for an (obsolete, pre-2.7.x)
            // fpunits.cfg-file
            ConfFile := IncludeTrailingPathDelimiter(Result)+S+PathDelim+UnitConfigFileName;
            if FileExistsLog(ConfFile) then
              Result := ConfFile;
          end
        else
          Result := ConfFile;
      end;
  end;

var
  UFN : String;
begin
  if PackageName<>'' then
    begin
      ExecuteAction(PackageName,'build');
      ExecuteAction(PackageName,'fpmakeinstall');
      if (PackageName=CmdLinePackageName) or (PackageName=CurrentDirPackageName) or
         (PackageName=URLPackageName) then
        begin
          // Load package name from manifest
          if not FileExists(ManifestFileName) then
            ExecuteAction(PackageName,'fpmakemanifest');
          P:=LoadManifestFromFile(ManifestFileName);
          S:=P.Name;
          FreeAndNil(P);
        end
      else
        S:=PackageName;

      InstallRepo := GFPpkg.RepositoryByName(GFPpkg.Options.CommandLineSection.InstallRepository);
      if Assigned(InstallRepo) then
        begin
          P := InstallRepo.FindPackage(S);
          if not Assigned(P) then
            P := InstallRepo.AddPackage(S);
          if Assigned(P) then
            begin
              UFN:=GetFpmFilename;
              if UFN<>'' then
                begin
                  P.LoadUnitConfigFromFile(UFN);
                  if P.IsFPMakeAddIn then
                    AddFPMakeAddIn(P);
                end;
            end;
        end;
    end
  else
    ExecuteAction(PackageName,'fpmakeinstall');
end;


procedure TCommandClean.Execute;
begin
  ExecuteAction(PackageName,'fpmakeclean');
end;


procedure TCommandArchive.Execute;
begin
  ExecuteAction(PackageName,'fpmakearchive');
end;


procedure TCommandInstallDependencies.Execute;

  function PackageVersionStr(APackage: TFPPackage): string;
  begin
    if Assigned(APackage) then
      Result := APackage.Version.AsString
    else
      Result := 'N/A';
  end;

var
  i : Integer;
  MissingDependency,
  D : TFPDependency;
  P,
  InstalledP,
  AvailP : TFPPackage;
  PackNr: integer;
  ManifestPackages : TFPPackages;
  X : TFPXMLRepositoryHandler;
  L : TStringList;
  status : string;
begin
  if PackageName='' then
    Error(SErrNoPackageSpecified);
  ManifestPackages:=nil;
  // Load dependencies for local packages
  if (PackageName=CmdLinePackageName) or (PackageName=CurrentDirPackageName) or
     (PackageName=URLPackageName) then
    begin
      ExecuteAction(PackageName,'fpmakemanifest');
      ManifestPackages:=TFPPackages.Create(TFPPackage);
      X:=TFPXMLRepositoryHandler.Create;
      try
        X.LoadFromXml(ManifestPackages,ManifestFileName);
      finally
        X.Free;
      end;
      if ManifestPackages.Count>0 then
        begin
          PackNr:=0;
          P := ManifestPackages[PackNr];
        end
      else
        begin
          ManifestPackages.Free;
          Error(SErrManifestNoSinglePackage,[ManifestFileName]);
        end;
    end
  else
    P:=GFPpkg.PackageByName(PackageName, pkgpkBoth);

  MissingDependency:=nil;
  while assigned(P) do
    begin
      // Find and List dependencies
      L:=TStringList.Create;
      for i:=0 to P.Dependencies.Count-1 do
        begin
          D:=P.Dependencies[i];
          if not ((GFPpkg.CompilerOptions.CompilerOS in D.OSes) and (GFPpkg.CompilerOptions.CompilerCPU in D.CPUs)) then
            Log(llDebug,SDbgPackageDependencyOtherTarget,[D.PackageName,MakeTargetString(GFPpkg.CompilerOptions.CompilerCPU,GFPpkg.CompilerOptions.CompilerOS)])
          // Skip dependencies that are available within the fpmake-file itself
          else if not (assigned(ManifestPackages) and assigned(ManifestPackages.FindPackage(D.PackageName))) then
            begin
              AvailP := nil;
              InstalledP:=GFPpkg.FindPackage(D.PackageName, pkgpkInstalled);
              // Need installation?
              if not assigned(InstalledP) or
                 (InstalledP.Version.CompareVersion(D.MinVersion)<0) then
                begin
                  AvailP:=GFPpkg.FindPackage(D.PackageName, pkgpkAvailable);
                  if not assigned(AvailP) or
                     (AvailP.Version.CompareVersion(D.MinVersion)<0) then
                    begin
                      status:='Not Available!';
                      MissingDependency:=D;
                    end
                  else
                    begin
                      status:='Updating';
                      L.Add(D.PackageName);
                    end;
                end
              else
                begin
                  if InstalledP.IsPackageBroken then
                    begin
                      status:='Broken, recompiling';
                      L.Add(D.PackageName);
                    end
                  else
                    status:='OK';
                end;
              Log(llInfo,SLogPackageDependency,
                  [D.PackageName,D.MinVersion.AsString,PackageVersionStr(InstalledP),
                   PackageVersionStr(AvailP),status])
            end
        end;
      if assigned(ManifestPackages) and (PackNr<ManifestPackages.Count-1)  then
        begin
          inc(PackNr);
          P := ManifestPackages[PackNr]
        end
      else
        p := nil;
    end;
  // Give error on first missing dependency
  if assigned(MissingDependency) then
    Error(SErrNoPackageAvailable,[MissingDependency.PackageName,MissingDependency.MinVersion.AsString]);
  // Install needed updates
  if L.Count > 0 then
    begin
      if DependenciesDepth=0 then
        pkgglobals.Log(llProgres,SProgrInstallDependencies);
      inc(DependenciesDepth);

      for i:=0 to L.Count-1 do
        ExecuteAction(L[i],'install');

      dec(DependenciesDepth);
      if DependenciesDepth=0 then
        pkgglobals.Log(llProgres,SProgrDependenciesInstalled);
    end;
  FreeAndNil(L);
  if assigned(ManifestPackages) then
    ManifestPackages.Free;
end;


procedure TCommandFixBroken.Execute;
var
  i : integer;
  SL : TStringList;
begin
  SL:=TStringList.Create;
  repeat
    FindBrokenPackages(SL);
    if SL.Count=0 then
      break;
    pkgglobals.Log(llProgres,SProgrReinstallDependent);
    for i:=0 to SL.Count-1 do
      begin
        ExecuteAction(SL[i],'build');
        ExecuteAction(SL[i],'install');
      end;
  until false;
  FreeAndNil(SL);
end;


initialization
  DependenciesDepth:=0;
  RegisterPkgHandler('update',TCommandUpdate);
  RegisterPkgHandler('list',TCommandListPackages);
  RegisterPkgHandler('scan',TCommandScanPackages);
  RegisterPkgHandler('download',TCommandDownload);
  RegisterPkgHandler('unzip',TCommandUnzip);
  RegisterPkgHandler('compile',TCommandCompile);
  RegisterPkgHandler('build',TCommandBuild);
  RegisterPkgHandler('install',TCommandInstall);
  RegisterPkgHandler('uninstall',TCommandUnInstall);
  RegisterPkgHandler('clean',TCommandClean);
  RegisterPkgHandler('archive',TCommandArchive);
  RegisterPkgHandler('installdependencies',TCommandInstallDependencies);
  RegisterPkgHandler('fixbroken',TCommandFixBroken);
  RegisterPkgHandler('listsettings',TCommandListSettings);
  RegisterPkgHandler('info',TCommandInfo);
end.
