open Prims
type local_binding =
  (FStar_Ident.ident,FStar_Syntax_Syntax.bv,Prims.bool)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type rec_binding =
  (FStar_Ident.ident,FStar_Ident.lid,FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type module_abbrev =
  (FStar_Ident.ident,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
[@@deriving show]
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____21 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____26 -> false
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}[@@deriving show]
let __proj__Mkrecord_or_dc__item__typename:
  record_or_dc -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
let __proj__Mkrecord_or_dc__item__constrname:
  record_or_dc -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
let __proj__Mkrecord_or_dc__item__parms:
  record_or_dc -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
let __proj__Mkrecord_or_dc__item__fields:
  record_or_dc ->
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__fields
let __proj__Mkrecord_or_dc__item__is_private_or_abstract:
  record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
let __proj__Mkrecord_or_dc__item__is_record: record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_record
type scope_mod =
  | Local_binding of local_binding
  | Rec_binding of rec_binding
  | Module_abbrev of module_abbrev
  | Open_module_or_namespace of open_module_or_namespace
  | Top_level_def of FStar_Ident.ident
  | Record_or_dc of record_or_dc[@@deriving show]
let uu___is_Local_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____198 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____212 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____226 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____240 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____254 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____268 -> false
let __proj__Record_or_dc__item___0: scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field[@@deriving show]
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____283 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____288 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref[@@deriving
                                                                    show]
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option;
  modules:
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap:
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  syntax_only: Prims.bool;
  ds_hooks: dsenv_hooks;}[@@deriving show]
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> Prims.unit;
  ds_push_include_hook: env -> FStar_Ident.lident -> Prims.unit;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit;}[@@deriving
                                                                    show]
let __proj__Mkenv__item__curmodule:
  env -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmodule
let __proj__Mkenv__item__curmonad:
  env -> FStar_Ident.ident FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmonad
let __proj__Mkenv__item__modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__modules
let __proj__Mkenv__item__scope_mods: env -> scope_mod Prims.list =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__scope_mods
let __proj__Mkenv__item__exported_ids: env -> exported_id_set FStar_Util.smap
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__exported_ids
let __proj__Mkenv__item__trans_exported_ids:
  env -> exported_id_set FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__trans_exported_ids
let __proj__Mkenv__item__includes:
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__includes
let __proj__Mkenv__item__sigaccum: env -> FStar_Syntax_Syntax.sigelts =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigaccum
let __proj__Mkenv__item__sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigmap
let __proj__Mkenv__item__iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__iface
let __proj__Mkenv__item__admitted_iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__admitted_iface
let __proj__Mkenv__item__expect_typ: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__expect_typ
let __proj__Mkenv__item__docs: env -> FStar_Parser_AST.fsdoc FStar_Util.smap
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__docs
let __proj__Mkenv__item__remaining_iface_decls:
  env ->
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__remaining_iface_decls
let __proj__Mkenv__item__syntax_only: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__syntax_only
let __proj__Mkenv__item__ds_hooks: env -> dsenv_hooks =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__ds_hooks
let __proj__Mkdsenv_hooks__item__ds_push_open_hook:
  dsenv_hooks -> env -> open_module_or_namespace -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
let __proj__Mkdsenv_hooks__item__ds_push_include_hook:
  dsenv_hooks -> env -> FStar_Ident.lident -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook:
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_module_abbrev_hook
let default_ds_hooks: dsenv_hooks =
  {
    ds_push_open_hook = (fun uu____1561  -> fun uu____1562  -> ());
    ds_push_include_hook = (fun uu____1565  -> fun uu____1566  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1570  -> fun uu____1571  -> fun uu____1572  -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1598 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1628 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___184_1657 = env in
      {
        curmodule = (uu___184_1657.curmodule);
        curmonad = (uu___184_1657.curmonad);
        modules = (uu___184_1657.modules);
        scope_mods = (uu___184_1657.scope_mods);
        exported_ids = (uu___184_1657.exported_ids);
        trans_exported_ids = (uu___184_1657.trans_exported_ids);
        includes = (uu___184_1657.includes);
        sigaccum = (uu___184_1657.sigaccum);
        sigmap = (uu___184_1657.sigmap);
        iface = b;
        admitted_iface = (uu___184_1657.admitted_iface);
        expect_typ = (uu___184_1657.expect_typ);
        docs = (uu___184_1657.docs);
        remaining_iface_decls = (uu___184_1657.remaining_iface_decls);
        syntax_only = (uu___184_1657.syntax_only);
        ds_hooks = (uu___184_1657.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___185_1670 = e in
      {
        curmodule = (uu___185_1670.curmodule);
        curmonad = (uu___185_1670.curmonad);
        modules = (uu___185_1670.modules);
        scope_mods = (uu___185_1670.scope_mods);
        exported_ids = (uu___185_1670.exported_ids);
        trans_exported_ids = (uu___185_1670.trans_exported_ids);
        includes = (uu___185_1670.includes);
        sigaccum = (uu___185_1670.sigaccum);
        sigmap = (uu___185_1670.sigmap);
        iface = (uu___185_1670.iface);
        admitted_iface = b;
        expect_typ = (uu___185_1670.expect_typ);
        docs = (uu___185_1670.docs);
        remaining_iface_decls = (uu___185_1670.remaining_iface_decls);
        syntax_only = (uu___185_1670.syntax_only);
        ds_hooks = (uu___185_1670.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___186_1683 = e in
      {
        curmodule = (uu___186_1683.curmodule);
        curmonad = (uu___186_1683.curmonad);
        modules = (uu___186_1683.modules);
        scope_mods = (uu___186_1683.scope_mods);
        exported_ids = (uu___186_1683.exported_ids);
        trans_exported_ids = (uu___186_1683.trans_exported_ids);
        includes = (uu___186_1683.includes);
        sigaccum = (uu___186_1683.sigaccum);
        sigmap = (uu___186_1683.sigmap);
        iface = (uu___186_1683.iface);
        admitted_iface = (uu___186_1683.admitted_iface);
        expect_typ = b;
        docs = (uu___186_1683.docs);
        remaining_iface_decls = (uu___186_1683.remaining_iface_decls);
        syntax_only = (uu___186_1683.syntax_only);
        ds_hooks = (uu___186_1683.ds_hooks)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1701 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1701 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1707 =
            let uu____1708 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1708 in
          FStar_All.pipe_right uu____1707 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let open_modules_and_namespaces: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___153_1901  ->
         match uu___153_1901 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1906 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___187_1915 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___187_1915.curmonad);
        modules = (uu___187_1915.modules);
        scope_mods = (uu___187_1915.scope_mods);
        exported_ids = (uu___187_1915.exported_ids);
        trans_exported_ids = (uu___187_1915.trans_exported_ids);
        includes = (uu___187_1915.includes);
        sigaccum = (uu___187_1915.sigaccum);
        sigmap = (uu___187_1915.sigmap);
        iface = (uu___187_1915.iface);
        admitted_iface = (uu___187_1915.admitted_iface);
        expect_typ = (uu___187_1915.expect_typ);
        docs = (uu___187_1915.docs);
        remaining_iface_decls = (uu___187_1915.remaining_iface_decls);
        syntax_only = (uu___187_1915.syntax_only);
        ds_hooks = (uu___187_1915.ds_hooks)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let iface_decls:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1933 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1967  ->
                match uu____1967 with
                | (m,uu____1975) -> FStar_Ident.lid_equals l m)) in
      match uu____1933 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1992,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2022 =
          FStar_List.partition
            (fun uu____2052  ->
               match uu____2052 with
               | (m,uu____2060) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2022 with
        | (uu____2065,rest) ->
            let uu___188_2099 = env in
            {
              curmodule = (uu___188_2099.curmodule);
              curmonad = (uu___188_2099.curmonad);
              modules = (uu___188_2099.modules);
              scope_mods = (uu___188_2099.scope_mods);
              exported_ids = (uu___188_2099.exported_ids);
              trans_exported_ids = (uu___188_2099.trans_exported_ids);
              includes = (uu___188_2099.includes);
              sigaccum = (uu___188_2099.sigaccum);
              sigmap = (uu___188_2099.sigmap);
              iface = (uu___188_2099.iface);
              admitted_iface = (uu___188_2099.admitted_iface);
              expect_typ = (uu___188_2099.expect_typ);
              docs = (uu___188_2099.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___188_2099.syntax_only);
              ds_hooks = (uu___188_2099.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2122 = current_module env in qual uu____2122 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2124 =
            let uu____2125 = current_module env in qual uu____2125 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2124 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___189_2138 = env in
      {
        curmodule = (uu___189_2138.curmodule);
        curmonad = (uu___189_2138.curmonad);
        modules = (uu___189_2138.modules);
        scope_mods = (uu___189_2138.scope_mods);
        exported_ids = (uu___189_2138.exported_ids);
        trans_exported_ids = (uu___189_2138.trans_exported_ids);
        includes = (uu___189_2138.includes);
        sigaccum = (uu___189_2138.sigaccum);
        sigmap = (uu___189_2138.sigmap);
        iface = (uu___189_2138.iface);
        admitted_iface = (uu___189_2138.admitted_iface);
        expect_typ = (uu___189_2138.expect_typ);
        docs = (uu___189_2138.docs);
        remaining_iface_decls = (uu___189_2138.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___189_2138.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___190_2151 = env in
      {
        curmodule = (uu___190_2151.curmodule);
        curmonad = (uu___190_2151.curmonad);
        modules = (uu___190_2151.modules);
        scope_mods = (uu___190_2151.scope_mods);
        exported_ids = (uu___190_2151.exported_ids);
        trans_exported_ids = (uu___190_2151.trans_exported_ids);
        includes = (uu___190_2151.includes);
        sigaccum = (uu___190_2151.sigaccum);
        sigmap = (uu___190_2151.sigmap);
        iface = (uu___190_2151.iface);
        admitted_iface = (uu___190_2151.admitted_iface);
        expect_typ = (uu___190_2151.expect_typ);
        docs = (uu___190_2151.docs);
        remaining_iface_decls = (uu___190_2151.remaining_iface_decls);
        syntax_only = (uu___190_2151.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2156 . Prims.unit -> 'Auu____2156 FStar_Util.smap =
  fun uu____2162  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2166  ->
    let uu____2167 = new_sigmap () in
    let uu____2170 = new_sigmap () in
    let uu____2173 = new_sigmap () in
    let uu____2184 = new_sigmap () in
    let uu____2195 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2167;
      trans_exported_ids = uu____2170;
      includes = uu____2173;
      sigaccum = [];
      sigmap = uu____2184;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2195;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks
    }
let sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  = fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____2229  ->
         match uu____2229 with
         | (m,uu____2235) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___191_2245 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___191_2245.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___192_2246 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___192_2246.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___192_2246.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
let unmangleOpName:
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun id  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2336  ->
           match uu____2336 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____2359 =
                   let uu____2360 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2360 dd dq in
                 FStar_Pervasives_Native.Some uu____2359
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore[@@deriving show]
let uu___is_Cont_ok: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2405 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2438 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2454 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___154_2480  ->
      match uu___154_2480 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2498 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2498 cont_t) -> 'Auu____2498 cont_t
  =
  fun ns  ->
    fun id  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          if FStar_Ident.lid_equals typename' record.typename
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2544  ->
                   match uu____2544 with
                   | (f,uu____2552) ->
                       if id.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None  -> Cont_ignore
          else Cont_ignore
let get_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___155_2603  ->
    match uu___155_2603 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes:
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind  ->
    fun find_in_module  ->
      fun find_in_module_default  ->
        fun env  ->
          fun ns  ->
            fun id  ->
              let idstr = id.FStar_Ident.idText in
              let rec aux uu___156_2666 =
                match uu___156_2666 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2677 = get_exported_id_set env mname in
                      match uu____2677 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2698 = mex eikind in
                            FStar_ST.op_Bang uu____2698 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2873 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2873 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2936 = qual modul id in
                        find_in_module uu____2936
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____2940 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___157_2946  ->
    match uu___157_2946 with
    | Exported_id_field  -> true
    | uu____2947 -> false
let try_lookup_id'':
  'a .
    env ->
      FStar_Ident.ident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___158_3058 =
                    match uu___158_3058 with
                    | (id',uu____3060,uu____3061) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let check_rec_binding_id uu___159_3065 =
                    match uu___159_3065 with
                    | (id',uu____3067,uu____3068) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3072 = current_module env in
                    FStar_Ident.ids_of_lid uu____3072 in
                  let proc uu___160_3078 =
                    match uu___160_3078 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3086 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id1 r k_record)
                          Cont_ignore env uu____3086 id
                    | uu____3091 -> Cont_ignore in
                  let rec aux uu___161_3099 =
                    match uu___161_3099 with
                    | a::q ->
                        let uu____3108 = proc a in
                        option_of_cont (fun uu____3112  -> aux q) uu____3108
                    | [] ->
                        let uu____3113 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3117  -> FStar_Pervasives_Native.None)
                          uu____3113 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3126 'Auu____3127 .
    FStar_Range.range ->
      ('Auu____3127,FStar_Syntax_Syntax.bv,'Auu____3126)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3126)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3145  ->
      match uu____3145 with
      | (id',x,mut) -> let uu____3155 = bv_to_name x r in (uu____3155, mut)
let find_in_module:
  'Auu____3166 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3166)
          -> 'Auu____3166 -> 'Auu____3166
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3201 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3201 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id  ->
      let uu____3239 = unmangleOpName id in
      match uu____3239 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3265 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____3279 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____3279) (fun uu____3289  -> Cont_fail)
            (fun uu____3295  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3310  -> fun uu____3311  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3326  -> fun uu____3327  -> Cont_fail)
let lookup_default_id:
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env  ->
    fun id  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3402 ->
                let lid = qualify env id in
                let uu____3404 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3404 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3428 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3428
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3451 = current_module env in qual uu____3451 id in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3463 = current_module env in
           FStar_Ident.lid_equals lid uu____3463)
        ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
let resolve_module_name:
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___162_3498 =
          match uu___162_3498 with
          | [] ->
              let uu____3503 = module_is_defined env lid in
              if uu____3503
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3512 =
                  let uu____3515 = FStar_Ident.path_of_lid ns in
                  let uu____3518 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3515 uu____3518 in
                FStar_Ident.lid_of_path uu____3512
                  (FStar_Ident.range_of_lid lid) in
              let uu____3521 = module_is_defined env new_lid in
              if uu____3521
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3527 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3534::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3550 =
          let uu____3551 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3551 in
        if uu____3550
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3553 =
                let uu____3554 =
                  let uu____3559 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____3559, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____3554 in
              FStar_Exn.raise uu____3553))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3569 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3573 = resolve_module_name env modul_orig true in
          (match uu____3573 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3577 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___163_3590  ->
           match uu___163_3590 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3592 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3684 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3684
                   (FStar_Util.map_option
                      (fun uu____3734  ->
                         match uu____3734 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____3765 =
          is_full_path &&
            (let uu____3767 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3767) in
        if uu____3765
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3797 = aux ns_rev_prefix ns_last_id in
               (match uu____3797 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3858 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3858 with
      | (uu____3867,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'':
  'a .
    env ->
      FStar_Ident.lident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun f_module  ->
                fun l_default  ->
                  match lid.FStar_Ident.ns with
                  | uu____3984::uu____3985 ->
                      let uu____3988 =
                        let uu____3991 =
                          let uu____3992 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____3992
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____3991 true in
                      (match uu____3988 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3996 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4000  -> FStar_Pervasives_Native.None)
                             uu____3996)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___164_4021  ->
      match uu___164_4021 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces':
  'a .
    env ->
      FStar_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStar_Ident.lident ->
               (FStar_Syntax_Syntax.sigelt,Prims.bool)
                 FStar_Pervasives_Native.tuple2 ->
                 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun k_local_binding  ->
        fun k_rec_binding  ->
          fun k_global_def  ->
            let k_global_def' k lid1 def =
              let uu____4126 = k_global_def lid1 def in
              cont_of_option k uu____4126 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4156 = k_local_binding l in
                 cont_of_option Cont_fail uu____4156)
              (fun r  ->
                 let uu____4162 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4162)
              (fun uu____4166  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4175,uu____4176,uu____4177,l,uu____4179,uu____4180) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___165_4191  ->
               match uu___165_4191 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4194,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4206 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4212,uu____4213,uu____4214)
        -> FStar_Pervasives_Native.None
    | uu____4215 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4228 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4236 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4236
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4228 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4251 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4251 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___169_4285 =
            match uu___169_4285 with
            | (uu____4292,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4294) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4297 ->
                     let uu____4314 =
                       let uu____4315 =
                         let uu____4320 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4320, false) in
                       Term_name uu____4315 in
                     FStar_Pervasives_Native.Some uu____4314
                 | FStar_Syntax_Syntax.Sig_datacon uu____4321 ->
                     let uu____4336 =
                       let uu____4337 =
                         let uu____4342 =
                           let uu____4343 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4343 in
                         (uu____4342, false) in
                       Term_name uu____4337 in
                     FStar_Pervasives_Native.Some uu____4336
                 | FStar_Syntax_Syntax.Sig_let ((uu____4346,lbs),uu____4348)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4364 =
                       let uu____4365 =
                         let uu____4370 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4370, false) in
                       Term_name uu____4365 in
                     FStar_Pervasives_Native.Some uu____4364
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4372,uu____4373) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4377 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___166_4381  ->
                                  match uu___166_4381 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4382 -> false))) in
                     if uu____4377
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4387 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___167_4392  ->
                                      match uu___167_4392 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4393 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4398 -> true
                                      | uu____4399 -> false))) in
                         if uu____4387
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____4401 =
                         FStar_Util.find_map quals
                           (fun uu___168_4406  ->
                              match uu___168_4406 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4410 -> FStar_Pervasives_Native.None) in
                       (match uu____4401 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4419 ->
                            let uu____4422 =
                              let uu____4423 =
                                let uu____4428 =
                                  let uu____4429 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____4429 in
                                (uu____4428, false) in
                              Term_name uu____4423 in
                            FStar_Pervasives_Native.Some uu____4422)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4435 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4448 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4467 =
              let uu____4468 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4468 in
            FStar_Pervasives_Native.Some uu____4467 in
          let k_rec_binding uu____4484 =
            match uu____4484 with
            | (id,l,dd) ->
                let uu____4496 =
                  let uu____4497 =
                    let uu____4502 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4502, false) in
                  Term_name uu____4497 in
                FStar_Pervasives_Native.Some uu____4496 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4508 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4508 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4526 -> FStar_Pervasives_Native.None)
            | uu____4533 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____4565 = try_lookup_name true exclude_interf env lid in
        match uu____4565 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4580 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4597 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4597 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4612 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4635 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4635 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4651;
             FStar_Syntax_Syntax.sigquals = uu____4652;
             FStar_Syntax_Syntax.sigmeta = uu____4653;
             FStar_Syntax_Syntax.sigattrs = uu____4654;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4673;
             FStar_Syntax_Syntax.sigquals = uu____4674;
             FStar_Syntax_Syntax.sigmeta = uu____4675;
             FStar_Syntax_Syntax.sigattrs = uu____4676;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4694,uu____4695,uu____4696,uu____4697,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4699;
             FStar_Syntax_Syntax.sigquals = uu____4700;
             FStar_Syntax_Syntax.sigmeta = uu____4701;
             FStar_Syntax_Syntax.sigattrs = uu____4702;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4724 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4747 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4747 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4757;
             FStar_Syntax_Syntax.sigquals = uu____4758;
             FStar_Syntax_Syntax.sigmeta = uu____4759;
             FStar_Syntax_Syntax.sigattrs = uu____4760;_},uu____4761)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4771;
             FStar_Syntax_Syntax.sigquals = uu____4772;
             FStar_Syntax_Syntax.sigmeta = uu____4773;
             FStar_Syntax_Syntax.sigattrs = uu____4774;_},uu____4775)
          -> FStar_Pervasives_Native.Some ne
      | uu____4784 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4799 = try_lookup_effect_name env lid in
      match uu____4799 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4802 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4813 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4813 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4823,uu____4824,uu____4825,uu____4826);
             FStar_Syntax_Syntax.sigrng = uu____4827;
             FStar_Syntax_Syntax.sigquals = uu____4828;
             FStar_Syntax_Syntax.sigmeta = uu____4829;
             FStar_Syntax_Syntax.sigattrs = uu____4830;_},uu____4831)
          ->
          let rec aux new_name =
            let uu____4850 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4850 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4868) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____4877,uu____4878,uu____4879,cmp,uu____4881) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4887 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4888,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4894 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___170_4925 =
        match uu___170_4925 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4934,uu____4935,uu____4936);
             FStar_Syntax_Syntax.sigrng = uu____4937;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4939;
             FStar_Syntax_Syntax.sigattrs = uu____4940;_},uu____4941)
            -> FStar_Pervasives_Native.Some quals
        | uu____4948 -> FStar_Pervasives_Native.None in
      let uu____4955 =
        resolve_in_open_namespaces' env lid
          (fun uu____4963  -> FStar_Pervasives_Native.None)
          (fun uu____4967  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4955 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4977 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4996 =
        FStar_List.tryFind
          (fun uu____5011  ->
             match uu____5011 with
             | (mlid,modul) ->
                 let uu____5018 = FStar_Ident.path_of_lid mlid in
                 uu____5018 = path) env.modules in
      match uu____4996 with
      | FStar_Pervasives_Native.Some (uu____5025,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___171_5057 =
        match uu___171_5057 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5064,lbs),uu____5066);
             FStar_Syntax_Syntax.sigrng = uu____5067;
             FStar_Syntax_Syntax.sigquals = uu____5068;
             FStar_Syntax_Syntax.sigmeta = uu____5069;
             FStar_Syntax_Syntax.sigattrs = uu____5070;_},uu____5071)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5091 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5091
        | uu____5092 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5098  -> FStar_Pervasives_Native.None)
        (fun uu____5100  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___172_5125 =
        match uu___172_5125 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5135);
             FStar_Syntax_Syntax.sigrng = uu____5136;
             FStar_Syntax_Syntax.sigquals = uu____5137;
             FStar_Syntax_Syntax.sigmeta = uu____5138;
             FStar_Syntax_Syntax.sigattrs = uu____5139;_},uu____5140)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5163 -> FStar_Pervasives_Native.None)
        | uu____5170 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5180  -> FStar_Pervasives_Native.None)
        (fun uu____5184  -> FStar_Pervasives_Native.None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____5227 = try_lookup_name any_val exclude_interf env lid in
          match uu____5227 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5242 -> FStar_Pervasives_Native.None
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5273 = try_lookup_lid env l in
      match uu____5273 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5287) ->
          let uu____5292 =
            let uu____5293 = FStar_Syntax_Subst.compress e in
            uu____5293.FStar_Syntax_Syntax.n in
          (match uu____5292 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5299 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___193_5315 = env in
        {
          curmodule = (uu___193_5315.curmodule);
          curmonad = (uu___193_5315.curmonad);
          modules = (uu___193_5315.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___193_5315.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___193_5315.sigaccum);
          sigmap = (uu___193_5315.sigmap);
          iface = (uu___193_5315.iface);
          admitted_iface = (uu___193_5315.admitted_iface);
          expect_typ = (uu___193_5315.expect_typ);
          docs = (uu___193_5315.docs);
          remaining_iface_decls = (uu___193_5315.remaining_iface_decls);
          syntax_only = (uu___193_5315.syntax_only);
          ds_hooks = (uu___193_5315.ds_hooks)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___174_5348 =
        match uu___174_5348 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5355,uu____5356,uu____5357);
             FStar_Syntax_Syntax.sigrng = uu____5358;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5360;
             FStar_Syntax_Syntax.sigattrs = uu____5361;_},uu____5362)
            ->
            let uu____5367 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___173_5371  ->
                      match uu___173_5371 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5372 -> false)) in
            if uu____5367
            then
              let uu____5375 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5375
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5377;
             FStar_Syntax_Syntax.sigrng = uu____5378;
             FStar_Syntax_Syntax.sigquals = uu____5379;
             FStar_Syntax_Syntax.sigmeta = uu____5380;
             FStar_Syntax_Syntax.sigattrs = uu____5381;_},uu____5382)
            ->
            let uu____5401 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5401
        | uu____5402 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5408  -> FStar_Pervasives_Native.None)
        (fun uu____5410  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___175_5437 =
        match uu___175_5437 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5446,uu____5447,uu____5448,uu____5449,datas,uu____5451);
             FStar_Syntax_Syntax.sigrng = uu____5452;
             FStar_Syntax_Syntax.sigquals = uu____5453;
             FStar_Syntax_Syntax.sigmeta = uu____5454;
             FStar_Syntax_Syntax.sigattrs = uu____5455;_},uu____5456)
            -> FStar_Pervasives_Native.Some datas
        | uu____5471 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5481  -> FStar_Pervasives_Native.None)
        (fun uu____5485  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5530 =
    let uu____5531 =
      let uu____5536 =
        let uu____5539 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5539 in
      let uu____5586 = FStar_ST.op_Bang record_cache in uu____5536 ::
        uu____5586 in
    FStar_ST.op_Colon_Equals record_cache uu____5531 in
  let pop1 uu____5676 =
    let uu____5677 =
      let uu____5682 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5682 in
    FStar_ST.op_Colon_Equals record_cache uu____5677 in
  let peek1 uu____5774 =
    let uu____5775 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5775 in
  let insert r =
    let uu____5826 =
      let uu____5831 = let uu____5834 = peek1 () in r :: uu____5834 in
      let uu____5837 =
        let uu____5842 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5842 in
      uu____5831 :: uu____5837 in
    FStar_ST.op_Colon_Equals record_cache uu____5826 in
  let filter1 uu____5934 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____5943 =
      let uu____5948 =
        let uu____5953 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5953 in
      filtered :: uu____5948 in
    FStar_ST.op_Colon_Equals record_cache uu____5943 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6109 = record_cache_aux_with_filter in
  match uu____6109 with | (aux,uu____6153) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6197 = record_cache_aux_with_filter in
  match uu____6197 with | (uu____6224,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6269 = record_cache_aux in
  match uu____6269 with | (push1,uu____6291,uu____6292,uu____6293) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6317 = record_cache_aux in
  match uu____6317 with | (uu____6338,pop1,uu____6340,uu____6341) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6367 = record_cache_aux in
  match uu____6367 with | (uu____6390,uu____6391,peek1,uu____6393) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6417 = record_cache_aux in
  match uu____6417 with | (uu____6438,uu____6439,uu____6440,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6497) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___176_6513  ->
                   match uu___176_6513 with
                   | FStar_Syntax_Syntax.RecordType uu____6514 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6523 -> true
                   | uu____6532 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___177_6554  ->
                      match uu___177_6554 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6556,uu____6557,uu____6558,uu____6559,uu____6560);
                          FStar_Syntax_Syntax.sigrng = uu____6561;
                          FStar_Syntax_Syntax.sigquals = uu____6562;
                          FStar_Syntax_Syntax.sigmeta = uu____6563;
                          FStar_Syntax_Syntax.sigattrs = uu____6564;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6573 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___178_6608  ->
                    match uu___178_6608 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6612,uu____6613,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6615;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6617;
                        FStar_Syntax_Syntax.sigattrs = uu____6618;_} ->
                        let uu____6629 =
                          let uu____6630 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____6630 in
                        (match uu____6629 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6636,t,uu____6638,uu____6639,uu____6640);
                             FStar_Syntax_Syntax.sigrng = uu____6641;
                             FStar_Syntax_Syntax.sigquals = uu____6642;
                             FStar_Syntax_Syntax.sigmeta = uu____6643;
                             FStar_Syntax_Syntax.sigattrs = uu____6644;_} ->
                             let uu____6653 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____6653 with
                              | (formals,uu____6667) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6716  ->
                                            match uu____6716 with
                                            | (x,q) ->
                                                let uu____6729 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____6729
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6786  ->
                                            match uu____6786 with
                                            | (x,q) ->
                                                let uu____6799 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____6799,
                                                  (x.FStar_Syntax_Syntax.sort)))) in
                                  let fields = fields' in
                                  let record =
                                    {
                                      typename;
                                      constrname =
                                        (constrname.FStar_Ident.ident);
                                      parms;
                                      fields;
                                      is_private_or_abstract =
                                        ((FStar_List.contains
                                            FStar_Syntax_Syntax.Private
                                            typename_quals)
                                           ||
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Abstract
                                              typename_quals));
                                      is_record = is_rec
                                    } in
                                  ((let uu____6814 =
                                      let uu____6817 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____6817 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____6814);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____6894 =
                                            match uu____6894 with
                                            | (id,uu____6902) ->
                                                let modul =
                                                  let uu____6908 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____6908.FStar_Ident.str in
                                                let uu____6909 =
                                                  get_exported_id_set e modul in
                                                (match uu____6909 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____6936 =
                                                         let uu____6937 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____6937 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____6936);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____6989 =
                                                               let uu____6990
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____6990.FStar_Ident.ident in
                                                             uu____6989.FStar_Ident.idText in
                                                           let uu____6992 =
                                                             let uu____6993 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____6993 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____6992))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7054 -> ())
                    | uu____7055 -> ()))
        | uu____7056 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7073 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7073 with
        | (ns,id) ->
            let uu____7090 = peek_record_cache () in
            FStar_Util.find_map uu____7090
              (fun record  ->
                 let uu____7096 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7102  -> FStar_Pervasives_Native.None)
                   uu____7096) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7104  -> Cont_ignore) (fun uu____7106  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7112 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7112)
        (fun k  -> fun uu____7118  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7131 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7131 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7137 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7152 = try_lookup_record_by_field_name env lid in
        match uu____7152 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7156 =
              let uu____7157 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7157 in
            let uu____7160 =
              let uu____7161 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7161 in
            uu____7156 = uu____7160 ->
            let uu____7164 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7168  -> Cont_ok ()) in
            (match uu____7164 with
             | Cont_ok uu____7169 -> true
             | uu____7170 -> false)
        | uu____7173 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7190 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7190 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7200 =
            let uu____7205 =
              let uu____7206 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7206
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7205, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7200
      | uu____7211 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7232  ->
    let uu____7233 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7233
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7254  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___179_7265  ->
      match uu___179_7265 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___180_7303 =
            match uu___180_7303 with
            | Rec_binding uu____7304 -> true
            | uu____7305 -> false in
          let this_env =
            let uu___194_7307 = env in
            let uu____7308 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___194_7307.curmodule);
              curmonad = (uu___194_7307.curmonad);
              modules = (uu___194_7307.modules);
              scope_mods = uu____7308;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___194_7307.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___194_7307.sigaccum);
              sigmap = (uu___194_7307.sigmap);
              iface = (uu___194_7307.iface);
              admitted_iface = (uu___194_7307.admitted_iface);
              expect_typ = (uu___194_7307.expect_typ);
              docs = (uu___194_7307.docs);
              remaining_iface_decls = (uu___194_7307.remaining_iface_decls);
              syntax_only = (uu___194_7307.syntax_only);
              ds_hooks = (uu___194_7307.ds_hooks)
            } in
          let uu____7311 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____7311 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7322 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___195_7339 = env in
      {
        curmodule = (uu___195_7339.curmodule);
        curmonad = (uu___195_7339.curmonad);
        modules = (uu___195_7339.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___195_7339.exported_ids);
        trans_exported_ids = (uu___195_7339.trans_exported_ids);
        includes = (uu___195_7339.includes);
        sigaccum = (uu___195_7339.sigaccum);
        sigmap = (uu___195_7339.sigmap);
        iface = (uu___195_7339.iface);
        admitted_iface = (uu___195_7339.admitted_iface);
        expect_typ = (uu___195_7339.expect_typ);
        docs = (uu___195_7339.docs);
        remaining_iface_decls = (uu___195_7339.remaining_iface_decls);
        syntax_only = (uu___195_7339.syntax_only);
        ds_hooks = (uu___195_7339.ds_hooks)
      }
let push_bv':
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
            FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x true
let push_bv:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____7394 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____7394
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err1 l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____7421) ->
              let uu____7426 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____7426 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____7434 =
          let uu____7435 =
            let uu____7440 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____7440, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____7435 in
        FStar_Exn.raise uu____7434 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____7449 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7458 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7465 -> (true, true)
          | uu____7474 -> (false, false) in
        match uu____7449 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____7480 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7486 =
                     let uu____7487 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____7487 in
                   if uu____7486
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____7480 with
             | FStar_Pervasives_Native.Some l when
                 let uu____7492 = FStar_Options.interactive () in
                 Prims.op_Negation uu____7492 -> err1 l
             | uu____7493 ->
                 (extract_record env globals s;
                  (let uu___196_7511 = env in
                   {
                     curmodule = (uu___196_7511.curmodule);
                     curmonad = (uu___196_7511.curmonad);
                     modules = (uu___196_7511.modules);
                     scope_mods = (uu___196_7511.scope_mods);
                     exported_ids = (uu___196_7511.exported_ids);
                     trans_exported_ids = (uu___196_7511.trans_exported_ids);
                     includes = (uu___196_7511.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___196_7511.sigmap);
                     iface = (uu___196_7511.iface);
                     admitted_iface = (uu___196_7511.admitted_iface);
                     expect_typ = (uu___196_7511.expect_typ);
                     docs = (uu___196_7511.docs);
                     remaining_iface_decls =
                       (uu___196_7511.remaining_iface_decls);
                     syntax_only = (uu___196_7511.syntax_only);
                     ds_hooks = (uu___196_7511.ds_hooks)
                   }))) in
      let env2 =
        let uu___197_7513 = env1 in
        let uu____7514 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___197_7513.curmodule);
          curmonad = (uu___197_7513.curmonad);
          modules = (uu___197_7513.modules);
          scope_mods = uu____7514;
          exported_ids = (uu___197_7513.exported_ids);
          trans_exported_ids = (uu___197_7513.trans_exported_ids);
          includes = (uu___197_7513.includes);
          sigaccum = (uu___197_7513.sigaccum);
          sigmap = (uu___197_7513.sigmap);
          iface = (uu___197_7513.iface);
          admitted_iface = (uu___197_7513.admitted_iface);
          expect_typ = (uu___197_7513.expect_typ);
          docs = (uu___197_7513.docs);
          remaining_iface_decls = (uu___197_7513.remaining_iface_decls);
          syntax_only = (uu___197_7513.syntax_only);
          ds_hooks = (uu___197_7513.ds_hooks)
        } in
      let uu____7549 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7575) ->
            let uu____7584 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____7584)
        | uu____7611 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____7549 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____7670  ->
                   match uu____7670 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____7691 =
                                  let uu____7694 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____7694 in
                                FStar_ST.op_Colon_Equals globals uu____7691);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____7762 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____7762.FStar_Ident.str in
                                    ((let uu____7764 =
                                        get_exported_id_set env3 modul in
                                      match uu____7764 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____7790 =
                                            let uu____7791 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____7791 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____7790
                                      | FStar_Pervasives_Native.None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___198_7851 = env3 in
              let uu____7852 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___198_7851.curmodule);
                curmonad = (uu___198_7851.curmonad);
                modules = (uu___198_7851.modules);
                scope_mods = uu____7852;
                exported_ids = (uu___198_7851.exported_ids);
                trans_exported_ids = (uu___198_7851.trans_exported_ids);
                includes = (uu___198_7851.includes);
                sigaccum = (uu___198_7851.sigaccum);
                sigmap = (uu___198_7851.sigmap);
                iface = (uu___198_7851.iface);
                admitted_iface = (uu___198_7851.admitted_iface);
                expect_typ = (uu___198_7851.expect_typ);
                docs = (uu___198_7851.docs);
                remaining_iface_decls = (uu___198_7851.remaining_iface_decls);
                syntax_only = (uu___198_7851.syntax_only);
                ds_hooks = (uu___198_7851.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____7895 =
        let uu____7900 = resolve_module_name env ns false in
        match uu____7900 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____7914 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____7928  ->
                      match uu____7928 with
                      | (m,uu____7934) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____7914
            then (ns, Open_namespace)
            else
              (let uu____7940 =
                 let uu____7941 =
                   let uu____7946 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____7946, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____7941 in
               FStar_Exn.raise uu____7940)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____7895 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____7965 = resolve_module_name env ns false in
      match uu____7965 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____7973 = current_module env1 in
              uu____7973.FStar_Ident.str in
            (let uu____7975 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____7975 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____7999 =
                   let uu____8002 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8002 in
                 FStar_ST.op_Colon_Equals incl uu____7999);
            (match () with
             | () ->
                 let uu____8069 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____8069 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8086 =
                          let uu____8103 = get_exported_id_set env1 curmod in
                          let uu____8110 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____8103, uu____8110) in
                        match uu____8086 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8164 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8164 in
                              let ex = cur_exports k in
                              (let uu____8347 =
                                 let uu____8348 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____8348 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____8347);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____8410 =
                                     let uu____8411 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____8411 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____8410) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____8462 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____8483 =
                        let uu____8484 =
                          let uu____8489 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____8489, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____8484 in
                      FStar_Exn.raise uu____8483))))
      | uu____8490 ->
          let uu____8493 =
            let uu____8494 =
              let uu____8499 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____8499, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____8494 in
          FStar_Exn.raise uu____8493
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____8512 = module_is_defined env l in
        if uu____8512
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____8516 =
             let uu____8517 =
               let uu____8522 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____8522, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____8517 in
           FStar_Exn.raise uu____8516)
let push_doc:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____8541 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____8541 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____8545 =
                    let uu____8546 = FStar_Ident.string_of_lid l in
                    let uu____8547 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____8548 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____8546 uu____8547 uu____8548 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____8545);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____8565 = try_lookup_lid env l in
                (match uu____8565 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8577 =
                         let uu____8578 = FStar_Options.interactive () in
                         Prims.op_Negation uu____8578 in
                       if uu____8577
                       then
                         let uu____8579 =
                           let uu____8580 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format1
                             "Admitting %s without a definition" uu____8580 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid l)
                           uu____8579
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___199_8590 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___199_8590.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___199_8590.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___199_8590.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___199_8590.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____8591 -> ())
            | uu____8600 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8619) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1  ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____8639,uu____8640,uu____8641,uu____8642,uu____8643)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____8652 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____8655,uu____8656) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____8662,lbs),uu____8664) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____8685 =
                               let uu____8686 =
                                 let uu____8687 =
                                   let uu____8690 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____8690.FStar_Syntax_Syntax.fv_name in
                                 uu____8687.FStar_Syntax_Syntax.v in
                               uu____8686.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____8685))
                   else ();
                   if
                     (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                       &&
                       (Prims.op_Negation
                          (FStar_List.contains FStar_Syntax_Syntax.Private
                             quals))
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let lid =
                               let uu____8704 =
                                 let uu____8707 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____8707.FStar_Syntax_Syntax.fv_name in
                               uu____8704.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___200_8712 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___200_8712.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___200_8712.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___200_8712.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____8722 -> ()));
      (let curmod =
         let uu____8724 = current_module env in uu____8724.FStar_Ident.str in
       (let uu____8726 =
          let uu____8743 = get_exported_id_set env curmod in
          let uu____8750 = get_trans_exported_id_set env curmod in
          (uu____8743, uu____8750) in
        match uu____8726 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____8804 = cur_ex eikind in FStar_ST.op_Bang uu____8804 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____8986 =
                let uu____8987 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____8987 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____8986 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____9038 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___201_9056 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___201_9056.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___201_9056.exported_ids);
                    trans_exported_ids = (uu___201_9056.trans_exported_ids);
                    includes = (uu___201_9056.includes);
                    sigaccum = [];
                    sigmap = (uu___201_9056.sigmap);
                    iface = (uu___201_9056.iface);
                    admitted_iface = (uu___201_9056.admitted_iface);
                    expect_typ = (uu___201_9056.expect_typ);
                    docs = (uu___201_9056.docs);
                    remaining_iface_decls =
                      (uu___201_9056.remaining_iface_decls);
                    syntax_only = (uu___201_9056.syntax_only);
                    ds_hooks = (uu___201_9056.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____9080 =
       let uu____9083 = FStar_ST.op_Bang stack in env :: uu____9083 in
     FStar_ST.op_Colon_Equals stack uu____9080);
    (let uu___202_9122 = env in
     let uu____9123 = FStar_Util.smap_copy (sigmap env) in
     let uu____9134 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___202_9122.curmodule);
       curmonad = (uu___202_9122.curmonad);
       modules = (uu___202_9122.modules);
       scope_mods = (uu___202_9122.scope_mods);
       exported_ids = (uu___202_9122.exported_ids);
       trans_exported_ids = (uu___202_9122.trans_exported_ids);
       includes = (uu___202_9122.includes);
       sigaccum = (uu___202_9122.sigaccum);
       sigmap = uu____9123;
       iface = (uu___202_9122.iface);
       admitted_iface = (uu___202_9122.admitted_iface);
       expect_typ = (uu___202_9122.expect_typ);
       docs = uu____9134;
       remaining_iface_decls = (uu___202_9122.remaining_iface_decls);
       syntax_only = (uu___202_9122.syntax_only);
       ds_hooks = (uu___202_9122.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____9140  ->
    let uu____9141 = FStar_ST.op_Bang stack in
    match uu____9141 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9186 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____9202 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____9205 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____9239 = FStar_Util.smap_try_find sm' k in
              match uu____9239 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___203_9264 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___203_9264.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___203_9264.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___203_9264.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___203_9264.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____9265 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____9270 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list;
  exported_id_fields: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkexported_ids__item__exported_id_terms:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
let __proj__Mkexported_ids__item__exported_id_fields:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
let as_exported_ids: exported_id_set -> exported_ids =
  fun e  ->
    let terms =
      let uu____9355 =
        let uu____9358 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____9358 in
      FStar_Util.set_elements uu____9355 in
    let fields =
      let uu____9533 =
        let uu____9536 = e Exported_id_field in FStar_ST.op_Bang uu____9536 in
      FStar_Util.set_elements uu____9533 in
    { exported_id_terms = terms; exported_id_fields = fields }
let as_exported_id_set:
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____9741 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____9741 in
        let fields =
          let uu____9751 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____9751 in
        (fun uu___181_9756  ->
           match uu___181_9756 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option;}
[@@deriving show]
let __proj__Mkmodule_inclusion_info__item__mii_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_includes:
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_includes
let default_mii: module_inclusion_info =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  }
let as_includes:
  'Auu____9869 .
    'Auu____9869 Prims.list FStar_Pervasives_Native.option ->
      'Auu____9869 Prims.list FStar_ST.ref
  =
  fun uu___182_9881  ->
    match uu___182_9881 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____9916 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____9916 as_exported_ids in
      let uu____9919 = as_ids_opt env.exported_ids in
      let uu____9922 = as_ids_opt env.trans_exported_ids in
      let uu____9925 =
        let uu____9930 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____9930 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____9919;
        mii_trans_exported_ids = uu____9922;
        mii_includes = uu____9925
      }
let prepare_module_or_interface:
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          module_inclusion_info ->
            (env,Prims.bool) FStar_Pervasives_Native.tuple2
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___183_10038 =
                  match uu___183_10038 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____10050  ->
                     match uu____10050 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____10074 =
                    let uu____10079 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____10079, Open_namespace) in
                  [uu____10074]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____10109 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____10109);
              (match () with
               | () ->
                   ((let uu____10125 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____10125);
                    (match () with
                     | () ->
                         ((let uu____10141 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____10141);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___204_10165 = env1 in
                                 let uu____10166 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___204_10165.curmonad);
                                   modules = (uu___204_10165.modules);
                                   scope_mods = uu____10166;
                                   exported_ids =
                                     (uu___204_10165.exported_ids);
                                   trans_exported_ids =
                                     (uu___204_10165.trans_exported_ids);
                                   includes = (uu___204_10165.includes);
                                   sigaccum = (uu___204_10165.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___204_10165.expect_typ);
                                   docs = (uu___204_10165.docs);
                                   remaining_iface_decls =
                                     (uu___204_10165.remaining_iface_decls);
                                   syntax_only = (uu___204_10165.syntax_only);
                                   ds_hooks = (uu___204_10165.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____10178 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____10204  ->
                      match uu____10204 with
                      | (l,uu____10210) -> FStar_Ident.lid_equals l mname)) in
            match uu____10178 with
            | FStar_Pervasives_Native.None  ->
                let uu____10219 = prep env in (uu____10219, false)
            | FStar_Pervasives_Native.Some (uu____10220,m) ->
                ((let uu____10227 =
                    (let uu____10230 = FStar_Options.interactive () in
                     Prims.op_Negation uu____10230) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____10227
                  then
                    let uu____10231 =
                      let uu____10232 =
                        let uu____10237 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str in
                        (uu____10237, (FStar_Ident.range_of_lid mname)) in
                      FStar_Errors.Error uu____10232 in
                    FStar_Exn.raise uu____10231
                  else ());
                 (let uu____10239 =
                    let uu____10240 = push env in prep uu____10240 in
                  (uu____10239, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.None  ->
          let uu___205_10250 = env in
          {
            curmodule = (uu___205_10250.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___205_10250.modules);
            scope_mods = (uu___205_10250.scope_mods);
            exported_ids = (uu___205_10250.exported_ids);
            trans_exported_ids = (uu___205_10250.trans_exported_ids);
            includes = (uu___205_10250.includes);
            sigaccum = (uu___205_10250.sigaccum);
            sigmap = (uu___205_10250.sigmap);
            iface = (uu___205_10250.iface);
            admitted_iface = (uu___205_10250.admitted_iface);
            expect_typ = (uu___205_10250.expect_typ);
            docs = (uu___205_10250.docs);
            remaining_iface_decls = (uu___205_10250.remaining_iface_decls);
            syntax_only = (uu___205_10250.syntax_only);
            ds_hooks = (uu___205_10250.ds_hooks)
          }
let fail_or:
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup  ->
      fun lid  ->
        let uu____10281 = lookup lid in
        match uu____10281 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____10294  ->
                   match uu____10294 with
                   | (lid1,uu____10300) -> FStar_Ident.text_of_lid lid1)
                env.modules in
            let msg =
              FStar_Util.format1 "Identifier not found: [%s]"
                (FStar_Ident.text_of_lid lid) in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____10305 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____10305
                     (FStar_Ident.range_of_lid lid) in
                 let uu____10306 = resolve_module_name env modul true in
                 match uu____10306 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m  -> m = modul'.FStar_Ident.str)
                          opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       (lid.FStar_Ident.ident).FStar_Ident.idText) in
            FStar_Exn.raise
              (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
        | FStar_Pervasives_Native.Some r -> r
let fail_or2:
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id  ->
      let uu____10340 = lookup id in
      match uu____10340 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Identifier not found ["
                   (Prims.strcat id.FStar_Ident.idText "]")),
                 (id.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.Some r -> r