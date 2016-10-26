{
    Copyright (c) 2011-2015 Blaise.ru
    Copyright (c) Maciej Izak (continuation of work started by Blaise.ru)

    Does parsing anonymous methods for Free Pascal / NewPascal :)

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

 ****************************************************************************
}

unit pnameless;

{$i fpcdefs.inc}

interface

  uses
    symsym, symdef,
    psub,PROCINFO,
    node,nbas;

  function parse_method_reference(const name: string): tobjectdef;
  function get_operator_invoke(const obj: tabstractrecorddef): tprocsym; inline;
  function parse_nameless_routine(const enclosing_routine: tprocdef): tnode;
  procedure initialise_capturer(const routine: tprocdef; var stmt: tstatementnode); inline;
  function load_contextual_self(const context: tprocdef): tnode;
  function handle_possible_capture(const ctx: tprocinfo; const sym: tabstractnormalvarsym): tnode;
  function reload_captured_sym(const routine: tprocdef; const sym: tabstractnormalvarsym): tnode;
  function are_compatible_interfaces(const l, r: tobjectdef): boolean;
  procedure postprocess_capturer(const routine: tprocdef); inline;
  procedure delete_captured_variables(const routine: tprocdef);

implementation

  uses
    cclasses,
    verbose,
    tokens, symconst, symbase, symtable, parabase,
    scanner,
    pbase,pdecsub,
    defcmp,
    nld,ncnv,nmem,ncal,nobj,nutils;


{.$define DEBUG_CLOSURES}
{$ifdef EXTDEBUG}
  {$assertions on}
{$endif}


function declare_invokable_interface(const name: string): tobjectdef;
  begin
    result:=tobjectdef.create(odt_interfacecom, name, interface_iunknown, true);
    result.objectoptions += [oo_has_virtual,oo_is_invokable];
  end;


    procedure {tprocdef.}add_to_procsym(const self: tprocdef); overload; inline;
      begin
        tprocsym(self.procsym).ProcdefList.Add(self);
      end;

    procedure {tprocdef.}add_to_procsym(const self: tprocdef; sym: tprocsym); overload;inline;
      begin
        self.procsym:=sym;
        add_to_procsym(self);
      end;

function parse_method_reference(const name: string): tobjectdef;
  var
    invoke: tprocdef;
  begin
    consume(token);
    consume(_TO);
    if token in [_PROCEDURE,_FUNCTION] then
      begin
        result:=declare_invokable_interface(name);
        symtablestack.push(result.symtable);
        invoke:=parse_proc_dec(false,result,false,ppm_method_reference);// TODO: ptype.pas parses procvars directly, using parse_parameter_dec
        // todo: extra ";" @
        //if check_proc_directive(true) then
        //  parse_proc_directives(invoke,[pd_procvar]);// TODO: limit the allowed subset?
        handle_calling_convention(invoke);// TODO: ?
        {invoke.}add_to_procsym(invoke);
        include(invoke.procoptions,po_virtualmethod);
        symtablestack.pop(result.symtable);
      end
    else
      consume(_PROCEDURE);// TODO: better error?
  end;

const
  invokable_method_name = 'INVOKE';

function get_operator_invoke(const obj: tabstractrecorddef): tprocsym; inline;
  begin
    if oo_is_invokable in obj.objectoptions then begin
      result := obj.symtable.find(invokable_method_name) as tprocsym;
      if result = nil then internalerror(2015020201);
    end else begin
      // TODO: "Type is not invokable" ?
      result := nil;
    end
  end;

function create_nameless_interface(const capturer_def: tobjectdef; const nameless_routine: tprocdef): tobjectdef;
  var
    intf_def: tobjectdef;
  {$ifdef DEBUG_CLOSURES}
    intf_sym: ttypesym;
  {$endif}
    invoke_sym: tprocsym;
    invoke: tprocdef;
    i: integer;
  begin
    // declare a new interface
    intf_def:=declare_invokable_interface('I'+nameless_routine.procsym.RealName);
    include(intf_def.objectoptions, oo_is_nameless);

  {$ifdef DEBUG_CLOSURES}
    intf_sym:=ttypesym.create(intf_def.objrealname^, intf_def);
    inc(intf_sym.refs);
    capturer_def.owner.insert(intf_sym);
  {$endif}

    invoke_sym:=tprocsym.create(invokable_method_name);
    intf_def.symtable.insert(invoke_sym);
    symtablestack.push(intf_def.symtable);
    invoke:=tprocdef.create(normal_function_level, true);
    invoke.struct := intf_def;
    symtablestack.pop(intf_def.symtable);
    {invoke.}add_to_procsym(invoke, invoke_sym);

    include(invoke.procoptions, po_virtualmethod);
    invoke.returndef:=nameless_routine.returndef;
    //invoke.calcparas;
    invoke.paras:=tparalist.create(false);
    invoke.paras.count:=nameless_routine.paras.count;
    for i:=0 to nameless_routine.paras.count-1 do
      invoke.paras[i]:=nameless_routine.paras[i];// TODO: WHO OWNS?!

    invoke.proccalloption:=nameless_routine.proccalloption;
    invoke.proctypeoption:=nameless_routine.proctypeoption;
    // implement it on TCapture
    capturer_def.register_implemented_interface(intf_def);
    // add mapping
    find_implemented_interface(capturer_def,intf_def).AddMapping(intf_def.objname^+'.'+invokable_method_name,nameless_routine.procsym.Name{todo?});

    result:=intf_def;
  end;

type tcapturersym = tlocalvarsym;

function get_capturer(const routine: tprocdef): tcapturersym; forward;

function load_capturer(const capturer: tabstractnormalvarsym): tnode; inline;
  begin
    // TODO: load_self_node for loadnf_is_self? WHEN capturer IS A $SELF?!
    result := cloadnode.create(capturer, capturer.owner)
  end;

function load_capturer_field(const capturer: tabstractnormalvarsym; const field: tfieldvarsym): tnode;
  begin
    assert(field.owner.defowner = capturer.vardef);
    result:=csubscriptnode.create(field, load_capturer(capturer));
  end;


function parse_nameless_routine(const enclosing_routine: tprocdef): tnode;
  var
    pd: tprocdef;
    capturer: tcapturersym;
    capturer_def: tobjectdef;
    nm_intf: tobjectdef;
    prev_struct: tabstractrecorddef;
  begin
    capturer:=get_capturer(enclosing_routine);
    capturer_def:=tobjectdef(capturer.vardef);

    prev_struct:=current_structdef;
    current_structdef:=capturer_def;
    // Popping happens in read_proc right before calling read_proc_body
    // TODO: Find a way of not pushing this?
    symtablestack.push(capturer_def.symtable);
    pd:=read_proc(false, nil, false, ppm_nameless_routine);
    {pd.}add_to_procsym(pd);
    current_structdef:=prev_struct;

    // for every nameless method we create an Invoke-interface
    nm_intf:=create_nameless_interface(capturer_def{TODO: obtain from pd?}, pd);

    result:=ctypeconvnode.create(load_capturer(capturer), nm_intf);
  end;


const
  capturer_var_name = 'Capturer';


function find_capturer(const routine: tprocdef): tcapturersym;
  var
    sym: TSymEntry;
  begin
    sym:=routine.localst.Find({$ifdef DEBUG_CLOSURES}upcase{$endif}(capturer_var_name));
    if not assigned(sym) then
      internalerror(2015031001);
    {$ifdef EXTDEBUG}
    result := sym as tcapturersym;
    assert( result.vardef.typ = objectdef );
    {$else}
    result := tcapturersym(sym);
    {$endif}
  end;


function instantiate_capturer(const routine: tprocdef): tnode;
  var
    capturer_sym: tcapturersym;
    capturer_def: tobjectdef;
    ctor:         tprocsym;
  begin
    {$ifdef DEBUG_CLOSURES}writeln('instantiate_capturer @ ', routine.procsym.RealName);{$endif}
    capturer_sym:=find_capturer(routine);
    capturer_def:=tobjectdef(capturer_sym.vardef);

    // Neither TInterfacedObject, nor TCapturer have a custom constructor
    ctor:=class_tobject.symtable.Find('CREATE') as tprocsym;

    // Insert "Capturer := TCapturer.Create()" as the first statement of the routine
    result:=cloadvmtaddrnode.create(ctypenode.create(capturer_def));
    result:=ccallnode.create(nil, ctor, capturer_def.symtable, result, [], nil);
    result:=cassignmentnode.create(load_capturer(capturer_sym), result);
  end;


procedure initialise_captured_parameters(const routine: tprocdef; var stmt: tstatementnode);
  var
    capturer: tcapturersym;
    i: integer;
    p: tparavarsym;
    node: tnode;
  begin
    capturer:=find_capturer(routine);

    for i := 0 to routine.paras.Count-1 do
      begin
        p:=tparavarsym(routine.paras[i]);
        if p.is_captured then
          begin
            {$ifdef DEBUG_CLOSURES}writeln(#9'initialise_captured_parameter ', p.RealName);{$endif}
            node:=cloadnode.create(p, p.owner);
            tloadnode(node).loadnodeflags:=[loadnf_captured_param]; // otherwise, it will be rewritten later!
            node:=cassignmentnode.create(
                      load_capturer_field(capturer, p.captured_into),
                      node
                      );
            addstatement(stmt, node);
          end;
      end;
  end;


procedure initialise_capturer(const routine: tprocdef; var stmt: tstatementnode); inline;
  begin
    if po_has_closure in routine.procoptions then
      begin
        addstatement(stmt, instantiate_capturer(routine));
        initialise_captured_parameters(routine, stmt);
      end;
  end;


function declare_capturer(const symtable: TSymTable): tcapturersym; inline;
  const
    capturer_class_name = 'Capturer';
  var
    capturer_def: tobjectdef;
    capturer_sym: ttypesym;
  begin
    // create class "type TCapturer = class(TInterfacedObject)"
    capturer_def:=tobjectdef.create(odt_class, capturer_class_name, search_system_type('TINTERFACEDOBJECT').typedef as tobjectdef, true);

    // Symbol is required for tdef.mangledparaname, which is now used by tobjectdef.vmt_def
    capturer_sym:=ttypesym.create({$ifndef DEBUG_CLOSURES}'$'+{$endif}'T'+capturer_class_name, capturer_def, true);
    inc(capturer_sym.refs);
    symtable.insert(capturer_sym);

    // TODO: "vmtdef$TCapturer" -- see tdef.OwnerHierarchyName
    //writeln('vmtdef$'+capturer_def.mangledparaname);

    // create "var $Capturer: TCapturer"
    result:=tcapturersym.create({$ifndef DEBUG_CLOSURES}'$'+{$endif}capturer_var_name, vs_value, capturer_def, [{TODO:DEBUG:?vo_is_public-- see $self}], true);
        // TODO: ^-- fileinfo:=current_tokenpos!
    symtable.insert(result);

    // Actual initialisation happens in generate_bodyentry_block -> instantiate_capturer.
    // We mark this prematurely, so that no warnings are reported during parse_body.
    result.varstate:=vs_initialised;
  end;


function get_capturer(const routine: tprocdef): tcapturersym;
  begin
    if po_has_closure in routine.procoptions then
      result:=find_capturer(routine)
    else begin
      // so far, the routine had no nameless methods
      include(routine.procoptions, po_has_closure);
      {$ifdef DEBUG_CLOSURES}writeln('declare_capturer @ ', routine.procsym.RealName);{$endif}
      result:=declare_capturer(routine.localst);
    end
  end;

function get_self(const routine: tprocdef): tabstractnormalvarsym; inline;
begin
  result := routine.parast.Find('self') as tabstractnormalvarsym;
end;

function get_enclosing_routine(const nameless_routine: tprocdef): tprocdef; inline;
begin
  result := nameless_routine.struct{capturer_def}.owner{localst}.defowner as tprocdef;
end;

// capture the variable into a field on the capture object
function capture_outer_sym(const nameless_routine: tprocdef; const outer_sym: tabstractnormalvarsym): tabstractnormalvarsym;
  var
    sym_owner_routine: tprocdef;
    enclosing_routine: tprocdef;
    capturer_symtable: tabstractrecordsymtable;
    captured_into: tfieldvarsym;
  begin
    assert( outer_sym.captured_into = nil );

    sym_owner_routine := outer_sym.owner.defowner as tprocdef;
    enclosing_routine := get_enclosing_routine(nameless_routine);

    if sym_owner_routine <> enclosing_routine then begin
      // currently, we do not allow reaching out through more than one nesting level;
      // additional bookkeeping is required for such functionality
      Comment(V_Error, 'capture_outer_sym: reaching too far -- cannot capture '+sym_owner_routine.procsym.RealName+'::'+outer_sym.RealName+' from '+enclosing_routine.procsym.RealName);
      internalerror(2012012001);
    end;

    {$ifdef DEBUG_CLOSURES}writeln('capturing ', outer_sym.RealName, ' whose refs = ', outer_sym.refs);{$endif}
    result := get_self(nameless_routine);
    capturer_symtable := (result.vardef as tobjectdef).symtable as tabstractrecordsymtable;

    captured_into := tfieldvarsym.create(outer_sym.RealName, vs_value, outer_sym.vardef, [], true);
    capturer_symtable.insert(captured_into);
    // ^-- after this, all subsequent "N" in THIS nameless routine will be resolved via $self automatically
    capturer_symtable.addfield(captured_into, vis_public);

    outer_sym.captured_into := captured_into;
  end;


function capture_outer_self(const nameless_routine: tprocdef; out captured_outer_self: tfieldvarsym): tabstractnormalvarsym; inline;
  var
    enclosing_routine: tprocdef;
    outer_self: tabstractnormalvarsym;
  begin
    enclosing_routine := get_enclosing_routine(nameless_routine);
    if (enclosing_routine = nil{PROGRAM}) or enclosing_routine.no_self_node then begin
      Comment(V_Error, 'capture_outer_self: enclosing_routine has no $self');
      internalerror(2015020401);
    end;

    outer_self := get_self(enclosing_routine);
    if outer_self = nil then internalerror(2015020402);
    result := capture_outer_sym(nameless_routine, outer_self);
    captured_outer_self := outer_self.captured_into;
  end;

function load_outer_self(const nameless_routine: tprocdef): tnode;
  var
    captured_outer_self: tfieldvarsym;
    capturer: tabstractnormalvarsym;
  begin
    captured_outer_self := nameless_routine.owner.Find('self') as tfieldvarsym;

    if captured_outer_self = nil then
      capturer := capture_outer_self(nameless_routine, captured_outer_self)
    else
      capturer := get_self(nameless_routine);

    result := load_capturer_field(capturer, captured_outer_self)
  end;

function load_contextual_self(const context: tprocdef): tnode; // todo: INLINE?
  begin
    if po_nameless in context.procoptions then begin
      if po_nameless in get_enclosing_routine(context).procoptions then begin
        Comment(V_Error, 'load_outer_self: enclosing_routine is nameless -- cannot reach farther');
        internalerror(2015072101);
      end;
      result := load_outer_self(context)
    end else
      result := load_self_node
  end;


function load_captured_sym(const routine: tprocdef; const field: tfieldvarsym): tnode;
  begin
    result:=load_capturer_field(find_capturer(routine), field);
  end;


function handle_possible_capture(const ctx: tprocinfo; const sym: tabstractnormalvarsym): tnode;
  var
    context, toplevel_context: tprocdef;
    sym_owner: tprocdef;
    capturer: tabstractnormalvarsym;
  begin
    context := ctx.procdef;
    sym_owner := sym.owner.defowner as tprocdef;

    if sym.is_captured then
      // A captured symbol is being accessed ...
      if context = sym_owner then begin
        // 1) from its own routine after it is captured by an embedded nameless routine
        {$ifdef DEBUG_CLOSURES}writeln('load_captured_sym ', sym.RealName);{$endif}
        result:=load_captured_sym(context, sym.captured_into)
      end else if context.struct = sym.captured_into.owner.defowner then
        // 2) from an embedded nameless routine (including nested routines) that has already captured it earlier
        result:=load_capturer_field(get_self(ctx.get_normal_proc.procdef), sym.captured_into)
      else
        internalerror(2011121001)
    else if (context <> sym_owner) then begin
      toplevel_context := ctx.get_normal_proc.procdef;
      if po_nameless in toplevel_context.procoptions then
        if context.struct <> sym_owner.struct then begin
          // Either a nameless routine, or a routine nested in one, accesses a local symbol of the enclosing routine (sym_owner)
          capturer:=capture_outer_sym(toplevel_context, sym);
          result:=load_capturer_field(capturer, sym.captured_into)
        end else
          // Both routines are within the same chain of nesting (toplevel_context)
          result := nil
      else
        // A nested routine accesses a local symbol of an enclosing routine
        result := nil
    end else
      result:=nil
  end;


function reload_captured_sym(const routine: tprocdef; const sym: tabstractnormalvarsym): tnode;
  begin
    {$ifdef DEBUG_CLOSURES}writeln('reload_captured_sym ', sym.RealName);{$endif}
    if routine <> sym.owner.defowner then
      internalerror(2011121002);

    result:=load_captured_sym(routine,sym.captured_into)
  end;


function are_compatible_headers(const pd1, pd2: tprocdef): boolean;
  begin     // TODO: revise the check
    result :=
      (compare_paras(pd1.paras,pd2.paras,cp_all,[cpo_ignorehidden{,cpo_comparedefaultvalue,cpo_ignoreuniv}])>=te_equal)
      and (compare_defs(pd1.returndef,pd2.returndef,nothingn)>=te_equal)
      and (pd1.proccalloption=pd2.proccalloption)
      and (pd1.proctypeoption=pd2.proctypeoption)
      and (pd1.procoptions-[po_global{TODO:why?}]=pd2.procoptions);
  end;


// TODO: allow explicit coercion for any interfaces, not just for nameless ones?
function are_compatible_interfaces(const l, r: tobjectdef): boolean;
  begin
    result :=
      (oo_is_nameless in r.objectoptions)
      and (l.childof = r.childof) // are they derived from the same interface?
      // TODO: exclude nested types etc (but types are not allowed)
      and (l.symtable.DefList.Count <= r.symtable.DefList.Count) // Left cannot have more methods than Right
      and (r.symtable.DefList.Count = 1) // TODO:! Also, l.defcount can be 0
      and are_compatible_headers(l.symtable.DefList[0] as tprocdef,
                                 r.symtable.DefList[0] as tprocdef) // TODO:!
      ;
  end;


procedure remove_captured_variable(X: TObject; Unused: pointer);
  var S: tabstractnormalvarsym absolute X;
  begin
    writeln(S.RealName);
    if (S.typ=localvarsym) and assigned(S.captured_into) then begin
      writeln(#9'deleted ', S.RealName);
      S.Owner.Delete(S) // !!cannot be deleted from foreach!!
    end;
  end;

// Without this, for example, initialisations will be generated for captured managed variables,
//   but Initialise(ManagedVar) is transformed into Initialise(Capturer.ManagedField),
//   and Capturer is not created until after managed variables are initialised.
procedure delete_captured_variables(const routine: tprocdef);
  var
    st: TSymTable;
    I: Integer;
    SL: TFPHashObjectList;
    S: TSymEntry;
  begin
    {$ifdef DEBUG_CLOSURES}writeln('delete_captured_variables in ', routine.fullprocname(true));{$endif}
    st := routine.localst;
    //st.SymList.ForEachCall(remove_captured_variable,nil);

    // TODO: what about debugging? how to expose such vars?
    SL := st.SymList;
    I := SL.Count;
    while I > 0 do begin
      dec(I);
      S := SL.Items[I] as TSymEntry;

      // TODO: what about params by value that are created/inited same way as managed localvar?!
      if (S.typ=localvarsym) and tlocalvarsym(S).is_captured then begin
        {$ifdef DEBUG_CLOSURES}writeln(#9'deleting ', S.RealName);{$endif}
        S.Owner.Delete(S) // TODO: ACTUALLY DESTROYS?
      end;
    end;
  end;


procedure generate_capturer_vmt(const capturer_def: tobjectdef); inline;
  begin
    with TVMTBuilder.Create(capturer_def) do begin
      generate_vmt;// TODO: same @ WHERE? -- extract
      Destroy;
    end;
  end;

procedure postprocess_capturer(const routine: tprocdef); inline;
  var
    capturer_def: tobjectdef;
  begin
    if not (po_has_closure in routine.procoptions) then exit;

    {$ifdef DEBUG_CLOSURES}writeln('postprocess_capturer @ ', routine.procsym.RealName);{$endif}

    capturer_def := tobjectdef( find_capturer(routine).vardef );
    // These two are delayed until this point because
    // ... we have been adding fields on-the-fly
    tabstractrecordsymtable(capturer_def.symtable).addalignmentpadding;
    // ... we have been adding interfaces on-the-fly
    generate_capturer_vmt(capturer_def);
  end;


end.
