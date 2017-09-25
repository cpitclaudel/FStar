open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2
  | Binding_sig of (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
  FStar_Pervasives_Native.tuple2
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____44 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____62 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____94 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____126 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____148 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
  | UnfoldTac[@@deriving show]
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____189 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____194 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____199 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____205 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____218 -> false
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkmlift__item__mlift_wp:
  mlift ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let __proj__Mkmlift__item__mlift_term:
  mlift ->
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
type edge =
  {
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}[@@deriving show]
let __proj__Mkedge__item__msource: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
let __proj__Mkedge__item__mtarget: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
let __proj__Mkedge__item__mlift: edge -> mlift =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list;}[@@deriving show]
let __proj__Mkeffects__item__decls:
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
let __proj__Mkeffects__item__order: effects -> edge Prims.list =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
let __proj__Mkeffects__item__joins:
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
type name_prefix = Prims.string Prims.list[@@deriving show]
type flat_proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list[@@deriving
                                                                    show]
type proof_namespace = flat_proof_namespace Prims.list[@@deriving show]
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2[@@deriving show]
type goal = FStar_Syntax_Syntax.term[@@deriving show]
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  top_level: Prims.bool;
  check_uvars: Prims.bool;
  use_eq: Prims.bool;
  is_iface: Prims.bool;
  admit: Prims.bool;
  lax: Prims.bool;
  lax_universes: Prims.bool;
  failhard: Prims.bool;
  nosynth: Prims.bool;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index:
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option;
  proof_ns: proof_namespace;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;
  is_native_tactic: FStar_Ident.lid -> Prims.bool;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref;
  tc_hooks: tcenv_hooks;}[@@deriving show]
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}[@@deriving show]
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2;
  implicits:
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list;}[@@deriving show]
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> Prims.unit;}[@@deriving show]
let __proj__Mkenv__item__solver: env -> solver_t =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__solver
let __proj__Mkenv__item__range: env -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__range
let __proj__Mkenv__item__curmodule: env -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__curmodule
let __proj__Mkenv__item__gamma: env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__gamma
let __proj__Mkenv__item__gamma_cache: env -> cached_elt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__gamma_cache
let __proj__Mkenv__item__modules: env -> FStar_Syntax_Syntax.modul Prims.list
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__modules
let __proj__Mkenv__item__expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__expected_typ
let __proj__Mkenv__item__sigtab:
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__sigtab
let __proj__Mkenv__item__is_pattern: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_pattern
let __proj__Mkenv__item__instantiate_imp: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__instantiate_imp
let __proj__Mkenv__item__effects: env -> effects =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__effects
let __proj__Mkenv__item__generalize: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__generalize
let __proj__Mkenv__item__letrecs:
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__letrecs
let __proj__Mkenv__item__top_level: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__top_level
let __proj__Mkenv__item__check_uvars: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__check_uvars
let __proj__Mkenv__item__use_eq: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__use_eq
let __proj__Mkenv__item__is_iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_iface
let __proj__Mkenv__item__admit: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__admit
let __proj__Mkenv__item__lax: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__lax
let __proj__Mkenv__item__lax_universes: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__lax_universes
let __proj__Mkenv__item__failhard: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__failhard
let __proj__Mkenv__item__nosynth: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__nosynth
let __proj__Mkenv__item__type_of:
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__type_of
let __proj__Mkenv__item__universe_of:
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__universe_of
let __proj__Mkenv__item__use_bv_sorts: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__use_bv_sorts
let __proj__Mkenv__item__qname_and_index:
  env ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__qname_and_index
let __proj__Mkenv__item__proof_ns: env -> proof_namespace =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__proof_ns
let __proj__Mkenv__item__synth:
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__synth
let __proj__Mkenv__item__is_native_tactic:
  env -> FStar_Ident.lid -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_native_tactic
let __proj__Mkenv__item__identifier_info:
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__identifier_info
let __proj__Mkenv__item__tc_hooks: env -> tcenv_hooks =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__tc_hooks
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__init
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__push
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__pop
let __proj__Mksolver_t__item__encode_modul:
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_modul
let __proj__Mksolver_t__item__encode_sig:
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_sig
let __proj__Mksolver_t__item__preprocess:
  solver_t ->
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__preprocess
let __proj__Mksolver_t__item__solve:
  solver_t ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__solve
let __proj__Mksolver_t__item__is_trivial:
  solver_t -> env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__is_trivial
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__finish
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__refresh
let __proj__Mkguard_t__item__guard_f:
  guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
let __proj__Mkguard_t__item__deferred:
  guard_t -> FStar_TypeChecker_Common.deferred =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
let __proj__Mkguard_t__item__univ_ineqs:
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
let __proj__Mkguard_t__item__implicits:
  guard_t ->
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook:
  tcenv_hooks -> env -> binding -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4434  -> fun uu____4435  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___126_4448 = env in
      {
        solver = (uu___126_4448.solver);
        range = (uu___126_4448.range);
        curmodule = (uu___126_4448.curmodule);
        gamma = (uu___126_4448.gamma);
        gamma_cache = (uu___126_4448.gamma_cache);
        modules = (uu___126_4448.modules);
        expected_typ = (uu___126_4448.expected_typ);
        sigtab = (uu___126_4448.sigtab);
        is_pattern = (uu___126_4448.is_pattern);
        instantiate_imp = (uu___126_4448.instantiate_imp);
        effects = (uu___126_4448.effects);
        generalize = (uu___126_4448.generalize);
        letrecs = (uu___126_4448.letrecs);
        top_level = (uu___126_4448.top_level);
        check_uvars = (uu___126_4448.check_uvars);
        use_eq = (uu___126_4448.use_eq);
        is_iface = (uu___126_4448.is_iface);
        admit = (uu___126_4448.admit);
        lax = (uu___126_4448.lax);
        lax_universes = (uu___126_4448.lax_universes);
        failhard = (uu___126_4448.failhard);
        nosynth = (uu___126_4448.nosynth);
        type_of = (uu___126_4448.type_of);
        universe_of = (uu___126_4448.universe_of);
        use_bv_sorts = (uu___126_4448.use_bv_sorts);
        qname_and_index = (uu___126_4448.qname_and_index);
        proof_ns = (uu___126_4448.proof_ns);
        synth = (uu___126_4448.synth);
        is_native_tactic = (uu___126_4448.is_native_tactic);
        identifier_info = (uu___126_4448.identifier_info);
        tc_hooks = hooks
      }
type env_t = env[@@deriving show]
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap[@@deriving show]
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____4463) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4464,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4465,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4466 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4475 . Prims.unit -> 'Auu____4475 FStar_Util.smap =
  fun uu____4481  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4486 . Prims.unit -> 'Auu____4486 FStar_Util.smap =
  fun uu____4492  -> FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
         FStar_Pervasives_Native.tuple3)
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____4541 = new_gamma_cache () in
          let uu____4544 = new_sigtab () in
          let uu____4547 =
            let uu____4548 = FStar_Options.using_facts_from () in
            match uu____4548 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____4558 =
                  let uu____4567 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____4567 [([], false)] in
                [uu____4558]
            | FStar_Pervasives_Native.None  -> [[]] in
          let uu____4640 =
            FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____4541;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____4544;
            is_pattern = false;
            instantiate_imp = true;
            effects = { decls = []; order = []; joins = [] };
            generalize = true;
            letrecs = [];
            top_level = false;
            check_uvars = false;
            use_eq = false;
            is_iface = false;
            admit = false;
            lax = false;
            lax_universes = false;
            failhard = false;
            nosynth = false;
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = FStar_Pervasives_Native.None;
            proof_ns = uu____4547;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____4674  -> false);
            identifier_info = uu____4640;
            tc_hooks = default_tc_hooks
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____4745  ->
    let uu____4746 = FStar_ST.op_Bang query_indices in
    match uu____4746 with
    | [] -> failwith "Empty query indices!"
    | uu____4803 ->
        let uu____4812 =
          let uu____4821 =
            let uu____4828 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____4828 in
          let uu____4885 = FStar_ST.op_Bang query_indices in uu____4821 ::
            uu____4885 in
        FStar_ST.op_Colon_Equals query_indices uu____4812
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____4987  ->
    let uu____4988 = FStar_ST.op_Bang query_indices in
    match uu____4988 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5116  ->
    match uu____5116 with
    | (l,n1) ->
        let uu____5123 = FStar_ST.op_Bang query_indices in
        (match uu____5123 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5248 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5266  ->
    let uu____5267 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5267
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5342 =
       let uu____5345 = FStar_ST.op_Bang stack in env :: uu____5345 in
     FStar_ST.op_Colon_Equals stack uu____5342);
    (let uu___127_5384 = env in
     let uu____5385 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5388 = FStar_Util.smap_copy (sigtab env) in
     let uu____5391 =
       let uu____5394 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5394 in
     {
       solver = (uu___127_5384.solver);
       range = (uu___127_5384.range);
       curmodule = (uu___127_5384.curmodule);
       gamma = (uu___127_5384.gamma);
       gamma_cache = uu____5385;
       modules = (uu___127_5384.modules);
       expected_typ = (uu___127_5384.expected_typ);
       sigtab = uu____5388;
       is_pattern = (uu___127_5384.is_pattern);
       instantiate_imp = (uu___127_5384.instantiate_imp);
       effects = (uu___127_5384.effects);
       generalize = (uu___127_5384.generalize);
       letrecs = (uu___127_5384.letrecs);
       top_level = (uu___127_5384.top_level);
       check_uvars = (uu___127_5384.check_uvars);
       use_eq = (uu___127_5384.use_eq);
       is_iface = (uu___127_5384.is_iface);
       admit = (uu___127_5384.admit);
       lax = (uu___127_5384.lax);
       lax_universes = (uu___127_5384.lax_universes);
       failhard = (uu___127_5384.failhard);
       nosynth = (uu___127_5384.nosynth);
       type_of = (uu___127_5384.type_of);
       universe_of = (uu___127_5384.universe_of);
       use_bv_sorts = (uu___127_5384.use_bv_sorts);
       qname_and_index = (uu___127_5384.qname_and_index);
       proof_ns = (uu___127_5384.proof_ns);
       synth = (uu___127_5384.synth);
       is_native_tactic = (uu___127_5384.is_native_tactic);
       identifier_info = uu____5391;
       tc_hooks = (uu___127_5384.tc_hooks)
     })
let pop_stack: Prims.unit -> env =
  fun uu____5422  ->
    let uu____5423 = FStar_ST.op_Bang stack in
    match uu____5423 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____5467 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____5515 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____5541  ->
                  match uu____5541 with
                  | (m,uu____5547) -> FStar_Ident.lid_equals l m)) in
        (match uu____5515 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___128_5554 = env in
               {
                 solver = (uu___128_5554.solver);
                 range = (uu___128_5554.range);
                 curmodule = (uu___128_5554.curmodule);
                 gamma = (uu___128_5554.gamma);
                 gamma_cache = (uu___128_5554.gamma_cache);
                 modules = (uu___128_5554.modules);
                 expected_typ = (uu___128_5554.expected_typ);
                 sigtab = (uu___128_5554.sigtab);
                 is_pattern = (uu___128_5554.is_pattern);
                 instantiate_imp = (uu___128_5554.instantiate_imp);
                 effects = (uu___128_5554.effects);
                 generalize = (uu___128_5554.generalize);
                 letrecs = (uu___128_5554.letrecs);
                 top_level = (uu___128_5554.top_level);
                 check_uvars = (uu___128_5554.check_uvars);
                 use_eq = (uu___128_5554.use_eq);
                 is_iface = (uu___128_5554.is_iface);
                 admit = (uu___128_5554.admit);
                 lax = (uu___128_5554.lax);
                 lax_universes = (uu___128_5554.lax_universes);
                 failhard = (uu___128_5554.failhard);
                 nosynth = (uu___128_5554.nosynth);
                 type_of = (uu___128_5554.type_of);
                 universe_of = (uu___128_5554.universe_of);
                 use_bv_sorts = (uu___128_5554.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___128_5554.proof_ns);
                 synth = (uu___128_5554.synth);
                 is_native_tactic = (uu___128_5554.is_native_tactic);
                 identifier_info = (uu___128_5554.identifier_info);
                 tc_hooks = (uu___128_5554.tc_hooks)
               }))
         | FStar_Pervasives_Native.Some (uu____5559,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___129_5567 = env in
               {
                 solver = (uu___129_5567.solver);
                 range = (uu___129_5567.range);
                 curmodule = (uu___129_5567.curmodule);
                 gamma = (uu___129_5567.gamma);
                 gamma_cache = (uu___129_5567.gamma_cache);
                 modules = (uu___129_5567.modules);
                 expected_typ = (uu___129_5567.expected_typ);
                 sigtab = (uu___129_5567.sigtab);
                 is_pattern = (uu___129_5567.is_pattern);
                 instantiate_imp = (uu___129_5567.instantiate_imp);
                 effects = (uu___129_5567.effects);
                 generalize = (uu___129_5567.generalize);
                 letrecs = (uu___129_5567.letrecs);
                 top_level = (uu___129_5567.top_level);
                 check_uvars = (uu___129_5567.check_uvars);
                 use_eq = (uu___129_5567.use_eq);
                 is_iface = (uu___129_5567.is_iface);
                 admit = (uu___129_5567.admit);
                 lax = (uu___129_5567.lax);
                 lax_universes = (uu___129_5567.lax_universes);
                 failhard = (uu___129_5567.failhard);
                 nosynth = (uu___129_5567.nosynth);
                 type_of = (uu___129_5567.type_of);
                 universe_of = (uu___129_5567.universe_of);
                 use_bv_sorts = (uu___129_5567.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___129_5567.proof_ns);
                 synth = (uu___129_5567.synth);
                 is_native_tactic = (uu___129_5567.is_native_tactic);
                 identifier_info = (uu___129_5567.identifier_info);
                 tc_hooks = (uu___129_5567.tc_hooks)
               })))
let debug: env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let set_range: env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___130_5589 = e in
         {
           solver = (uu___130_5589.solver);
           range = r;
           curmodule = (uu___130_5589.curmodule);
           gamma = (uu___130_5589.gamma);
           gamma_cache = (uu___130_5589.gamma_cache);
           modules = (uu___130_5589.modules);
           expected_typ = (uu___130_5589.expected_typ);
           sigtab = (uu___130_5589.sigtab);
           is_pattern = (uu___130_5589.is_pattern);
           instantiate_imp = (uu___130_5589.instantiate_imp);
           effects = (uu___130_5589.effects);
           generalize = (uu___130_5589.generalize);
           letrecs = (uu___130_5589.letrecs);
           top_level = (uu___130_5589.top_level);
           check_uvars = (uu___130_5589.check_uvars);
           use_eq = (uu___130_5589.use_eq);
           is_iface = (uu___130_5589.is_iface);
           admit = (uu___130_5589.admit);
           lax = (uu___130_5589.lax);
           lax_universes = (uu___130_5589.lax_universes);
           failhard = (uu___130_5589.failhard);
           nosynth = (uu___130_5589.nosynth);
           type_of = (uu___130_5589.type_of);
           universe_of = (uu___130_5589.universe_of);
           use_bv_sorts = (uu___130_5589.use_bv_sorts);
           qname_and_index = (uu___130_5589.qname_and_index);
           proof_ns = (uu___130_5589.proof_ns);
           synth = (uu___130_5589.synth);
           is_native_tactic = (uu___130_5589.is_native_tactic);
           identifier_info = (uu___130_5589.identifier_info);
           tc_hooks = (uu___130_5589.tc_hooks)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____5602 =
        let uu____5603 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____5603 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5602
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____5636 =
          let uu____5637 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____5637 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5636
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____5670 =
          let uu____5671 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____5671 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5670
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____5705 =
        let uu____5706 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____5706 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5705
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___131_5745 = env in
      {
        solver = (uu___131_5745.solver);
        range = (uu___131_5745.range);
        curmodule = lid;
        gamma = (uu___131_5745.gamma);
        gamma_cache = (uu___131_5745.gamma_cache);
        modules = (uu___131_5745.modules);
        expected_typ = (uu___131_5745.expected_typ);
        sigtab = (uu___131_5745.sigtab);
        is_pattern = (uu___131_5745.is_pattern);
        instantiate_imp = (uu___131_5745.instantiate_imp);
        effects = (uu___131_5745.effects);
        generalize = (uu___131_5745.generalize);
        letrecs = (uu___131_5745.letrecs);
        top_level = (uu___131_5745.top_level);
        check_uvars = (uu___131_5745.check_uvars);
        use_eq = (uu___131_5745.use_eq);
        is_iface = (uu___131_5745.is_iface);
        admit = (uu___131_5745.admit);
        lax = (uu___131_5745.lax);
        lax_universes = (uu___131_5745.lax_universes);
        failhard = (uu___131_5745.failhard);
        nosynth = (uu___131_5745.nosynth);
        type_of = (uu___131_5745.type_of);
        universe_of = (uu___131_5745.universe_of);
        use_bv_sorts = (uu___131_5745.use_bv_sorts);
        qname_and_index = (uu___131_5745.qname_and_index);
        proof_ns = (uu___131_5745.proof_ns);
        synth = (uu___131_5745.synth);
        is_native_tactic = (uu___131_5745.is_native_tactic);
        identifier_info = (uu___131_5745.identifier_info);
        tc_hooks = (uu___131_5745.tc_hooks)
      }
let has_interface: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let find_in_sigtab:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____5776 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____5776
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____5780  ->
    let uu____5781 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____5781
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____5821) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____5845 = FStar_Syntax_Subst.subst vs t in (us, uu____5845)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___113_5859  ->
    match uu___113_5859 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____5883  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____5898 = inst_tscheme t in
      match uu____5898 with
      | (us,t1) ->
          let uu____5909 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____5909)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____5925  ->
          match uu____5925 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____5940 =
                         let uu____5941 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____5942 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____5943 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____5944 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____5941 uu____5942 uu____5943 uu____5944 in
                       failwith uu____5940)
                    else ();
                    (let uu____5946 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____5946))
               | uu____5953 ->
                   let uu____5954 =
                     let uu____5955 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____5955 in
                   failwith uu____5954)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____5960 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____5965 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____5970 -> false
let in_cur_mod: env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident] in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident] in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____6006) -> Maybe
             | (uu____6013,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6032 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____6139 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6139 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___114_6184  ->
                   match uu___114_6184 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____6227 =
                           let uu____6246 =
                             let uu____6261 = inst_tscheme t in
                             FStar_Util.Inl uu____6261 in
                           (uu____6246, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____6227
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6327,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6329);
                                     FStar_Syntax_Syntax.sigrng = uu____6330;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6331;
                                     FStar_Syntax_Syntax.sigmeta = uu____6332;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6333;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6353 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6353
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____6399 ->
                             FStar_Pervasives_Native.Some t
                         | uu____6406 -> cache t in
                       let uu____6407 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6407 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____6482 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6482 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____6568 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____6648 = find_in_sigtab env lid in
         match uu____6648 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6747) ->
          add_sigelts env ses
      | uu____6756 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____6770 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___115_6799  ->
           match uu___115_6799 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____6817 -> FStar_Pervasives_Native.None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let ((uu____6852,lb::[]),uu____6854) ->
          let uu____6867 =
            let uu____6876 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____6885 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____6876, uu____6885) in
          FStar_Pervasives_Native.Some uu____6867
      | FStar_Syntax_Syntax.Sig_let ((uu____6898,lbs),uu____6900) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____6936 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____6948 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____6948
                   then
                     let uu____6959 =
                       let uu____6968 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____6977 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____6968, uu____6977) in
                     FStar_Pervasives_Native.Some uu____6959
                   else FStar_Pervasives_Native.None)
      | uu____6999 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7033 =
          let uu____7042 =
            let uu____7047 =
              let uu____7048 =
                let uu____7051 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7051 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7048) in
            inst_tscheme uu____7047 in
          (uu____7042, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7033
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7071,uu____7072) ->
        let uu____7077 =
          let uu____7086 =
            let uu____7091 =
              let uu____7092 =
                let uu____7095 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7095 in
              (us, uu____7092) in
            inst_tscheme uu____7091 in
          (uu____7086, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7077
    | uu____7112 -> FStar_Pervasives_Native.None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____7172 =
        match uu____7172 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____7268,uvs,t,uu____7271,uu____7272,uu____7273);
                    FStar_Syntax_Syntax.sigrng = uu____7274;
                    FStar_Syntax_Syntax.sigquals = uu____7275;
                    FStar_Syntax_Syntax.sigmeta = uu____7276;
                    FStar_Syntax_Syntax.sigattrs = uu____7277;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7298 =
                   let uu____7307 = inst_tscheme (uvs, t) in
                   (uu____7307, rng) in
                 FStar_Pervasives_Native.Some uu____7298
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7327;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7329;
                    FStar_Syntax_Syntax.sigattrs = uu____7330;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7347 =
                   let uu____7348 = in_cur_mod env l in uu____7348 = Yes in
                 if uu____7347
                 then
                   let uu____7359 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7359
                    then
                      let uu____7372 =
                        let uu____7381 = inst_tscheme (uvs, t) in
                        (uu____7381, rng) in
                      FStar_Pervasives_Native.Some uu____7372
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____7408 =
                      let uu____7417 = inst_tscheme (uvs, t) in
                      (uu____7417, rng) in
                    FStar_Pervasives_Native.Some uu____7408)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7438,uu____7439);
                    FStar_Syntax_Syntax.sigrng = uu____7440;
                    FStar_Syntax_Syntax.sigquals = uu____7441;
                    FStar_Syntax_Syntax.sigmeta = uu____7442;
                    FStar_Syntax_Syntax.sigattrs = uu____7443;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____7482 =
                        let uu____7491 = inst_tscheme (uvs, k) in
                        (uu____7491, rng) in
                      FStar_Pervasives_Native.Some uu____7482
                  | uu____7508 ->
                      let uu____7509 =
                        let uu____7518 =
                          let uu____7523 =
                            let uu____7524 =
                              let uu____7527 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7527 in
                            (uvs, uu____7524) in
                          inst_tscheme uu____7523 in
                        (uu____7518, rng) in
                      FStar_Pervasives_Native.Some uu____7509)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7548,uu____7549);
                    FStar_Syntax_Syntax.sigrng = uu____7550;
                    FStar_Syntax_Syntax.sigquals = uu____7551;
                    FStar_Syntax_Syntax.sigmeta = uu____7552;
                    FStar_Syntax_Syntax.sigattrs = uu____7553;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____7593 =
                        let uu____7602 = inst_tscheme_with (uvs, k) us in
                        (uu____7602, rng) in
                      FStar_Pervasives_Native.Some uu____7593
                  | uu____7619 ->
                      let uu____7620 =
                        let uu____7629 =
                          let uu____7634 =
                            let uu____7635 =
                              let uu____7638 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7638 in
                            (uvs, uu____7635) in
                          inst_tscheme_with uu____7634 us in
                        (uu____7629, rng) in
                      FStar_Pervasives_Native.Some uu____7620)
             | FStar_Util.Inr se ->
                 let uu____7672 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____7693;
                        FStar_Syntax_Syntax.sigrng = uu____7694;
                        FStar_Syntax_Syntax.sigquals = uu____7695;
                        FStar_Syntax_Syntax.sigmeta = uu____7696;
                        FStar_Syntax_Syntax.sigattrs = uu____7697;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____7712 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____7672
                   (FStar_Util.map_option
                      (fun uu____7760  ->
                         match uu____7760 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____7791 =
        let uu____7802 = lookup_qname env lid in
        FStar_Util.bind_opt uu____7802 mapper in
      match uu____7791 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___132_7895 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___132_7895.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___132_7895.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____7922 = lookup_qname env l in
      match uu____7922 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____7961 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8011 = try_lookup_bv env bv in
      match uu____8011 with
      | FStar_Pervasives_Native.None  ->
          let uu____8026 =
            let uu____8027 =
              let uu____8032 = variable_not_found bv in (uu____8032, bvr) in
            FStar_Errors.Error uu____8027 in
          FStar_Exn.raise uu____8026
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8043 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8044 = FStar_Range.set_use_range r bvr in
          (uu____8043, uu____8044)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8063 = try_lookup_lid_aux env l in
      match uu____8063 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____8129 =
            let uu____8138 =
              let uu____8143 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____8143) in
            (uu____8138, r1) in
          FStar_Pervasives_Native.Some uu____8129
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8172 = try_lookup_lid env l in
      match uu____8172 with
      | FStar_Pervasives_Native.None  ->
          let uu____8199 =
            let uu____8200 =
              let uu____8205 = name_not_found l in
              (uu____8205, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____8200 in
          FStar_Exn.raise uu____8199
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___116_8243  ->
              match uu___116_8243 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____8245 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____8262 = lookup_qname env lid in
      match uu____8262 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8291,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8294;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8296;
              FStar_Syntax_Syntax.sigattrs = uu____8297;_},FStar_Pervasives_Native.None
            ),uu____8298)
          ->
          let uu____8347 =
            let uu____8358 =
              let uu____8363 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8363) in
            (uu____8358, q) in
          FStar_Pervasives_Native.Some uu____8347
      | uu____8380 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8419 = lookup_qname env lid in
      match uu____8419 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8444,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8447;
              FStar_Syntax_Syntax.sigquals = uu____8448;
              FStar_Syntax_Syntax.sigmeta = uu____8449;
              FStar_Syntax_Syntax.sigattrs = uu____8450;_},FStar_Pervasives_Native.None
            ),uu____8451)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8500 ->
          let uu____8521 =
            let uu____8522 =
              let uu____8527 = name_not_found lid in
              (uu____8527, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8522 in
          FStar_Exn.raise uu____8521
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8544 = lookup_qname env lid in
      match uu____8544 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8569,uvs,t,uu____8572,uu____8573,uu____8574);
              FStar_Syntax_Syntax.sigrng = uu____8575;
              FStar_Syntax_Syntax.sigquals = uu____8576;
              FStar_Syntax_Syntax.sigmeta = uu____8577;
              FStar_Syntax_Syntax.sigattrs = uu____8578;_},FStar_Pervasives_Native.None
            ),uu____8579)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8632 ->
          let uu____8653 =
            let uu____8654 =
              let uu____8659 = name_not_found lid in
              (uu____8659, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8654 in
          FStar_Exn.raise uu____8653
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8678 = lookup_qname env lid in
      match uu____8678 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____8705,uu____8706,uu____8707,uu____8708,uu____8709,dcs);
              FStar_Syntax_Syntax.sigrng = uu____8711;
              FStar_Syntax_Syntax.sigquals = uu____8712;
              FStar_Syntax_Syntax.sigmeta = uu____8713;
              FStar_Syntax_Syntax.sigattrs = uu____8714;_},uu____8715),uu____8716)
          -> (true, dcs)
      | uu____8777 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____8808 = lookup_qname env lid in
      match uu____8808 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8829,uu____8830,uu____8831,l,uu____8833,uu____8834);
              FStar_Syntax_Syntax.sigrng = uu____8835;
              FStar_Syntax_Syntax.sigquals = uu____8836;
              FStar_Syntax_Syntax.sigmeta = uu____8837;
              FStar_Syntax_Syntax.sigattrs = uu____8838;_},uu____8839),uu____8840)
          -> l
      | uu____8895 ->
          let uu____8916 =
            let uu____8917 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____8917 in
          failwith uu____8916
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        let uu____8954 = lookup_qname env lid in
        match uu____8954 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8982) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9033,lbs),uu____9035) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9063 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9063
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9095 -> FStar_Pervasives_Native.None)
        | uu____9100 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9137 = lookup_qname env ftv in
      match uu____9137 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9161) ->
          let uu____9206 = effect_signature se in
          (match uu____9206 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9227,t),r) ->
               let uu____9242 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____9242)
      | uu____9243 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9272 = try_lookup_effect_lid env ftv in
      match uu____9272 with
      | FStar_Pervasives_Native.None  ->
          let uu____9275 =
            let uu____9276 =
              let uu____9281 = name_not_found ftv in
              (uu____9281, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____9276 in
          FStar_Exn.raise uu____9275
      | FStar_Pervasives_Native.Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____9301 = lookup_qname env lid0 in
        match uu____9301 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____9332);
                FStar_Syntax_Syntax.sigrng = uu____9333;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____9335;
                FStar_Syntax_Syntax.sigattrs = uu____9336;_},FStar_Pervasives_Native.None
              ),uu____9337)
            ->
            let lid1 =
              let uu____9391 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____9391 in
            let uu____9392 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_9396  ->
                      match uu___117_9396 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9397 -> false)) in
            if uu____9392
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____9411 =
                      let uu____9412 =
                        let uu____9413 = get_range env in
                        FStar_Range.string_of_range uu____9413 in
                      let uu____9414 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____9415 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____9412 uu____9414 uu____9415 in
                    failwith uu____9411) in
               match (binders, univs1) with
               | ([],uu____9422) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____9439,uu____9440::uu____9441::uu____9442) ->
                   let uu____9447 =
                     let uu____9448 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____9449 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____9448 uu____9449 in
                   failwith uu____9447
               | uu____9456 ->
                   let uu____9461 =
                     let uu____9466 =
                       let uu____9467 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____9467) in
                     inst_tscheme_with uu____9466 insts in
                   (match uu____9461 with
                    | (uu____9478,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____9481 =
                          let uu____9482 = FStar_Syntax_Subst.compress t1 in
                          uu____9482.FStar_Syntax_Syntax.n in
                        (match uu____9481 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____9529 -> failwith "Impossible")))
        | uu____9536 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____9578 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____9578 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____9591,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____9598 = find1 l2 in
            (match uu____9598 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____9605 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____9605 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____9609 = find1 l in
            (match uu____9609 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____9625 = lookup_qname env l1 in
      match uu____9625 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____9648;
              FStar_Syntax_Syntax.sigrng = uu____9649;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9651;
              FStar_Syntax_Syntax.sigattrs = uu____9652;_},uu____9653),uu____9654)
          -> q
      | uu____9705 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____9741 =
          let uu____9742 =
            let uu____9743 = FStar_Util.string_of_int i in
            let uu____9744 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____9743 uu____9744 in
          failwith uu____9742 in
        let uu____9745 = lookup_datacon env lid in
        match uu____9745 with
        | (uu____9750,t) ->
            let uu____9752 =
              let uu____9753 = FStar_Syntax_Subst.compress t in
              uu____9753.FStar_Syntax_Syntax.n in
            (match uu____9752 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9757) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____9788 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____9788
                      FStar_Pervasives_Native.fst)
             | uu____9797 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9806 = lookup_qname env l in
      match uu____9806 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9827,uu____9828,uu____9829);
              FStar_Syntax_Syntax.sigrng = uu____9830;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9832;
              FStar_Syntax_Syntax.sigattrs = uu____9833;_},uu____9834),uu____9835)
          ->
          FStar_Util.for_some
            (fun uu___118_9888  ->
               match uu___118_9888 with
               | FStar_Syntax_Syntax.Projector uu____9889 -> true
               | uu____9894 -> false) quals
      | uu____9895 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9924 = lookup_qname env lid in
      match uu____9924 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9945,uu____9946,uu____9947,uu____9948,uu____9949,uu____9950);
              FStar_Syntax_Syntax.sigrng = uu____9951;
              FStar_Syntax_Syntax.sigquals = uu____9952;
              FStar_Syntax_Syntax.sigmeta = uu____9953;
              FStar_Syntax_Syntax.sigattrs = uu____9954;_},uu____9955),uu____9956)
          -> true
      | uu____10011 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10040 = lookup_qname env lid in
      match uu____10040 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10061,uu____10062,uu____10063,uu____10064,uu____10065,uu____10066);
              FStar_Syntax_Syntax.sigrng = uu____10067;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10069;
              FStar_Syntax_Syntax.sigattrs = uu____10070;_},uu____10071),uu____10072)
          ->
          FStar_Util.for_some
            (fun uu___119_10133  ->
               match uu___119_10133 with
               | FStar_Syntax_Syntax.RecordType uu____10134 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10143 -> true
               | uu____10152 -> false) quals
      | uu____10153 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10182 = lookup_qname env lid in
      match uu____10182 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____10203,uu____10204);
              FStar_Syntax_Syntax.sigrng = uu____10205;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10207;
              FStar_Syntax_Syntax.sigattrs = uu____10208;_},uu____10209),uu____10210)
          ->
          FStar_Util.for_some
            (fun uu___120_10267  ->
               match uu___120_10267 with
               | FStar_Syntax_Syntax.Action uu____10268 -> true
               | uu____10269 -> false) quals
      | uu____10270 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation] in
  fun env  ->
    fun head1  ->
      let uu____10302 =
        let uu____10303 = FStar_Syntax_Util.un_uinst head1 in
        uu____10303.FStar_Syntax_Syntax.n in
      match uu____10302 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10307 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10374 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10390) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10407 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10414 ->
                 FStar_Pervasives_Native.Some true
             | uu____10431 -> FStar_Pervasives_Native.Some false) in
      let uu____10432 =
        let uu____10435 = lookup_qname env lid in
        FStar_Util.bind_opt uu____10435 mapper in
      match uu____10432 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____10483 = lookup_qname env lid in
      match uu____10483 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10504,uu____10505,tps,uu____10507,uu____10508,uu____10509);
              FStar_Syntax_Syntax.sigrng = uu____10510;
              FStar_Syntax_Syntax.sigquals = uu____10511;
              FStar_Syntax_Syntax.sigmeta = uu____10512;
              FStar_Syntax_Syntax.sigattrs = uu____10513;_},uu____10514),uu____10515)
          -> FStar_List.length tps
      | uu____10578 ->
          let uu____10599 =
            let uu____10600 =
              let uu____10605 = name_not_found lid in
              (uu____10605, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____10600 in
          FStar_Exn.raise uu____10599
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____10647  ->
              match uu____10647 with
              | (d,uu____10655) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____10668 = effect_decl_opt env l in
      match uu____10668 with
      | FStar_Pervasives_Native.None  ->
          let uu____10683 =
            let uu____10684 =
              let uu____10689 = name_not_found l in
              (uu____10689, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____10684 in
          FStar_Exn.raise uu____10683
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid))
          then
            (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____10755 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____10808  ->
                       match uu____10808 with
                       | (m1,m2,uu____10821,uu____10822,uu____10823) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____10755 with
             | FStar_Pervasives_Native.None  ->
                 let uu____10840 =
                   let uu____10841 =
                     let uu____10846 =
                       let uu____10847 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____10848 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____10847
                         uu____10848 in
                     (uu____10846, (env.range)) in
                   FStar_Errors.Error uu____10841 in
                 FStar_Exn.raise uu____10840
             | FStar_Pervasives_Native.Some
                 (uu____10855,uu____10856,m3,j1,j2) -> (m3, j1, j2))
let monad_leq:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux:
  'Auu____10899 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____10899)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____10926 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____10952  ->
                match uu____10952 with
                | (d,uu____10958) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____10926 with
      | FStar_Pervasives_Native.None  ->
          let uu____10969 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____10969
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____10982 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____10982 with
           | (uu____10993,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11003)::(wp,uu____11005)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11041 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m
let null_wp_for_eff:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          if
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Parser_Const.effect_GTot_lid
            then
              FStar_Syntax_Syntax.mk_GTotal' res_t
                (FStar_Pervasives_Native.Some res_u)
            else
              (let eff_name1 = norm_eff_name env eff_name in
               let ed = get_effect_decl env eff_name1 in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp in
               let null_wp_res =
                 let uu____11090 = get_range env in
                 let uu____11091 =
                   let uu____11094 =
                     let uu____11095 =
                       let uu____11110 =
                         let uu____11113 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11113] in
                       (null_wp, uu____11110) in
                     FStar_Syntax_Syntax.Tm_app uu____11095 in
                   FStar_Syntax_Syntax.mk uu____11094 in
                 uu____11091 FStar_Pervasives_Native.None uu____11090 in
               let uu____11119 =
                 let uu____11120 =
                   let uu____11129 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11129] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11120;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11119)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___133_11140 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___133_11140.order);
              joins = (uu___133_11140.joins)
            } in
          let uu___134_11149 = env in
          {
            solver = (uu___134_11149.solver);
            range = (uu___134_11149.range);
            curmodule = (uu___134_11149.curmodule);
            gamma = (uu___134_11149.gamma);
            gamma_cache = (uu___134_11149.gamma_cache);
            modules = (uu___134_11149.modules);
            expected_typ = (uu___134_11149.expected_typ);
            sigtab = (uu___134_11149.sigtab);
            is_pattern = (uu___134_11149.is_pattern);
            instantiate_imp = (uu___134_11149.instantiate_imp);
            effects;
            generalize = (uu___134_11149.generalize);
            letrecs = (uu___134_11149.letrecs);
            top_level = (uu___134_11149.top_level);
            check_uvars = (uu___134_11149.check_uvars);
            use_eq = (uu___134_11149.use_eq);
            is_iface = (uu___134_11149.is_iface);
            admit = (uu___134_11149.admit);
            lax = (uu___134_11149.lax);
            lax_universes = (uu___134_11149.lax_universes);
            failhard = (uu___134_11149.failhard);
            nosynth = (uu___134_11149.nosynth);
            type_of = (uu___134_11149.type_of);
            universe_of = (uu___134_11149.universe_of);
            use_bv_sorts = (uu___134_11149.use_bv_sorts);
            qname_and_index = (uu___134_11149.qname_and_index);
            proof_ns = (uu___134_11149.proof_ns);
            synth = (uu___134_11149.synth);
            is_native_tactic = (uu___134_11149.is_native_tactic);
            identifier_info = (uu___134_11149.identifier_info);
            tc_hooks = (uu___134_11149.tc_hooks)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____11166 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____11166 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____11256 = (e1.mlift).mlift_wp t wp in
                              let uu____11257 = l1 t wp e in
                              l2 t uu____11256 uu____11257))
                | uu____11258 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____11297 = inst_tscheme lift_t in
            match uu____11297 with
            | (uu____11304,lift_t1) ->
                let uu____11306 =
                  let uu____11309 =
                    let uu____11310 =
                      let uu____11325 =
                        let uu____11328 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11329 =
                          let uu____11332 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____11332] in
                        uu____11328 :: uu____11329 in
                      (lift_t1, uu____11325) in
                    FStar_Syntax_Syntax.Tm_app uu____11310 in
                  FStar_Syntax_Syntax.mk uu____11309 in
                uu____11306 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____11373 = inst_tscheme lift_t in
            match uu____11373 with
            | (uu____11380,lift_t1) ->
                let uu____11382 =
                  let uu____11385 =
                    let uu____11386 =
                      let uu____11401 =
                        let uu____11404 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11405 =
                          let uu____11408 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____11409 =
                            let uu____11412 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11412] in
                          uu____11408 :: uu____11409 in
                        uu____11404 :: uu____11405 in
                      (lift_t1, uu____11401) in
                    FStar_Syntax_Syntax.Tm_app uu____11386 in
                  FStar_Syntax_Syntax.mk uu____11385 in
                uu____11382 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            } in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            } in
          let print_mlift l =
            let bogus_term s =
              let uu____11450 =
                let uu____11451 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____11451
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____11450 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____11455 =
              let uu____11456 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____11456 in
            let uu____11457 =
              let uu____11458 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11476 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____11476) in
              FStar_Util.dflt "none" uu____11458 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11455
              uu____11457 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11502  ->
                    match uu____11502 with
                    | (e,uu____11510) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____11529 =
            match uu____11529 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____11567 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____11588 =
                                       let uu____11597 =
                                         find_edge order1 (i, k) in
                                       let uu____11600 =
                                         find_edge order1 (k, j) in
                                       (uu____11597, uu____11600) in
                                     match uu____11588 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____11615 =
                                           compose_edges e1 e2 in
                                         [uu____11615]
                                     | uu____11616 -> []))))) in
              FStar_List.append order1 uu____11567 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____11645 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____11647 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____11647
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____11645
                   then
                     let uu____11652 =
                       let uu____11653 =
                         let uu____11658 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____11659 = get_range env in
                         (uu____11658, uu____11659) in
                       FStar_Errors.Error uu____11653 in
                     FStar_Exn.raise uu____11652
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____11784 =
                                              let uu____11793 =
                                                find_edge order2 (i, k) in
                                              let uu____11796 =
                                                find_edge order2 (j, k) in
                                              (uu____11793, uu____11796) in
                                            match uu____11784 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____11838,uu____11839)
                                                     ->
                                                     let uu____11846 =
                                                       let uu____11851 =
                                                         let uu____11852 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____11852 in
                                                       let uu____11855 =
                                                         let uu____11856 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____11856 in
                                                       (uu____11851,
                                                         uu____11855) in
                                                     (match uu____11846 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate";
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____11891 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___135_11964 = env.effects in
              { decls = (uu___135_11964.decls); order = order2; joins } in
            let uu___136_11965 = env in
            {
              solver = (uu___136_11965.solver);
              range = (uu___136_11965.range);
              curmodule = (uu___136_11965.curmodule);
              gamma = (uu___136_11965.gamma);
              gamma_cache = (uu___136_11965.gamma_cache);
              modules = (uu___136_11965.modules);
              expected_typ = (uu___136_11965.expected_typ);
              sigtab = (uu___136_11965.sigtab);
              is_pattern = (uu___136_11965.is_pattern);
              instantiate_imp = (uu___136_11965.instantiate_imp);
              effects;
              generalize = (uu___136_11965.generalize);
              letrecs = (uu___136_11965.letrecs);
              top_level = (uu___136_11965.top_level);
              check_uvars = (uu___136_11965.check_uvars);
              use_eq = (uu___136_11965.use_eq);
              is_iface = (uu___136_11965.is_iface);
              admit = (uu___136_11965.admit);
              lax = (uu___136_11965.lax);
              lax_universes = (uu___136_11965.lax_universes);
              failhard = (uu___136_11965.failhard);
              nosynth = (uu___136_11965.nosynth);
              type_of = (uu___136_11965.type_of);
              universe_of = (uu___136_11965.universe_of);
              use_bv_sorts = (uu___136_11965.use_bv_sorts);
              qname_and_index = (uu___136_11965.qname_and_index);
              proof_ns = (uu___136_11965.proof_ns);
              synth = (uu___136_11965.synth);
              is_native_tactic = (uu___136_11965.is_native_tactic);
              identifier_info = (uu___136_11965.identifier_info);
              tc_hooks = (uu___136_11965.tc_hooks)
            }))
      | uu____11966 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____11992 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12002 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12002 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12019 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12019 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12037 =
                     let uu____12038 =
                       let uu____12043 =
                         let uu____12044 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12049 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12056 =
                           let uu____12057 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12057 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12044 uu____12049 uu____12056 in
                       (uu____12043, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12038 in
                   FStar_Exn.raise uu____12037)
                else ();
                (let inst1 =
                   let uu____12062 =
                     let uu____12071 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12071 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12088  ->
                        fun uu____12089  ->
                          match (uu____12088, uu____12089) with
                          | ((x,uu____12111),(t,uu____12113)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12062 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12132 =
                     let uu___137_12133 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___137_12133.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___137_12133.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___137_12133.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___137_12133.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12132
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux:
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
          let uu____12159 = effect_decl_opt env effect_name in
          match uu____12159 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12192 =
                only_reifiable &&
                  (let uu____12194 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____12194) in
              if uu____12192
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12210 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____12229 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____12258 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____12258
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____12259 =
                             let uu____12260 =
                               let uu____12265 = get_range env in
                               (message, uu____12265) in
                             FStar_Errors.Error uu____12260 in
                           FStar_Exn.raise uu____12259 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____12275 =
                       let uu____12278 = get_range env in
                       let uu____12279 =
                         let uu____12282 =
                           let uu____12283 =
                             let uu____12298 =
                               let uu____12301 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____12301; wp] in
                             (repr, uu____12298) in
                           FStar_Syntax_Syntax.Tm_app uu____12283 in
                         FStar_Syntax_Syntax.mk uu____12282 in
                       uu____12279 FStar_Pervasives_Native.None uu____12278 in
                     FStar_Pervasives_Native.Some uu____12275)
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____12353 =
            let uu____12354 =
              let uu____12359 =
                let uu____12360 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____12360 in
              let uu____12361 = get_range env in (uu____12359, uu____12361) in
            FStar_Errors.Error uu____12354 in
          FStar_Exn.raise uu____12353 in
        let uu____12362 = effect_repr_aux true env c u_c in
        match uu____12362 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable: env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____12402 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____12411 =
        let uu____12412 = FStar_Syntax_Subst.compress t in
        uu____12412.FStar_Syntax_Syntax.n in
      match uu____12411 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12415,c) ->
          is_reifiable_comp env c
      | uu____12433 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12457)::uu____12458 -> x :: rest
        | (Binding_sig_inst uu____12467)::uu____12468 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12483 = push1 x rest1 in local :: uu____12483 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___138_12487 = env in
       let uu____12488 = push1 s env.gamma in
       {
         solver = (uu___138_12487.solver);
         range = (uu___138_12487.range);
         curmodule = (uu___138_12487.curmodule);
         gamma = uu____12488;
         gamma_cache = (uu___138_12487.gamma_cache);
         modules = (uu___138_12487.modules);
         expected_typ = (uu___138_12487.expected_typ);
         sigtab = (uu___138_12487.sigtab);
         is_pattern = (uu___138_12487.is_pattern);
         instantiate_imp = (uu___138_12487.instantiate_imp);
         effects = (uu___138_12487.effects);
         generalize = (uu___138_12487.generalize);
         letrecs = (uu___138_12487.letrecs);
         top_level = (uu___138_12487.top_level);
         check_uvars = (uu___138_12487.check_uvars);
         use_eq = (uu___138_12487.use_eq);
         is_iface = (uu___138_12487.is_iface);
         admit = (uu___138_12487.admit);
         lax = (uu___138_12487.lax);
         lax_universes = (uu___138_12487.lax_universes);
         failhard = (uu___138_12487.failhard);
         nosynth = (uu___138_12487.nosynth);
         type_of = (uu___138_12487.type_of);
         universe_of = (uu___138_12487.universe_of);
         use_bv_sorts = (uu___138_12487.use_bv_sorts);
         qname_and_index = (uu___138_12487.qname_and_index);
         proof_ns = (uu___138_12487.proof_ns);
         synth = (uu___138_12487.synth);
         is_native_tactic = (uu___138_12487.is_native_tactic);
         identifier_info = (uu___138_12487.identifier_info);
         tc_hooks = (uu___138_12487.tc_hooks)
       })
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let push_sigelt_inst:
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let push_local_binding: env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___139_12525 = env in
      {
        solver = (uu___139_12525.solver);
        range = (uu___139_12525.range);
        curmodule = (uu___139_12525.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___139_12525.gamma_cache);
        modules = (uu___139_12525.modules);
        expected_typ = (uu___139_12525.expected_typ);
        sigtab = (uu___139_12525.sigtab);
        is_pattern = (uu___139_12525.is_pattern);
        instantiate_imp = (uu___139_12525.instantiate_imp);
        effects = (uu___139_12525.effects);
        generalize = (uu___139_12525.generalize);
        letrecs = (uu___139_12525.letrecs);
        top_level = (uu___139_12525.top_level);
        check_uvars = (uu___139_12525.check_uvars);
        use_eq = (uu___139_12525.use_eq);
        is_iface = (uu___139_12525.is_iface);
        admit = (uu___139_12525.admit);
        lax = (uu___139_12525.lax);
        lax_universes = (uu___139_12525.lax_universes);
        failhard = (uu___139_12525.failhard);
        nosynth = (uu___139_12525.nosynth);
        type_of = (uu___139_12525.type_of);
        universe_of = (uu___139_12525.universe_of);
        use_bv_sorts = (uu___139_12525.use_bv_sorts);
        qname_and_index = (uu___139_12525.qname_and_index);
        proof_ns = (uu___139_12525.proof_ns);
        synth = (uu___139_12525.synth);
        is_native_tactic = (uu___139_12525.is_native_tactic);
        identifier_info = (uu___139_12525.identifier_info);
        tc_hooks = (uu___139_12525.tc_hooks)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv:
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___140_12559 = env in
             {
               solver = (uu___140_12559.solver);
               range = (uu___140_12559.range);
               curmodule = (uu___140_12559.curmodule);
               gamma = rest;
               gamma_cache = (uu___140_12559.gamma_cache);
               modules = (uu___140_12559.modules);
               expected_typ = (uu___140_12559.expected_typ);
               sigtab = (uu___140_12559.sigtab);
               is_pattern = (uu___140_12559.is_pattern);
               instantiate_imp = (uu___140_12559.instantiate_imp);
               effects = (uu___140_12559.effects);
               generalize = (uu___140_12559.generalize);
               letrecs = (uu___140_12559.letrecs);
               top_level = (uu___140_12559.top_level);
               check_uvars = (uu___140_12559.check_uvars);
               use_eq = (uu___140_12559.use_eq);
               is_iface = (uu___140_12559.is_iface);
               admit = (uu___140_12559.admit);
               lax = (uu___140_12559.lax);
               lax_universes = (uu___140_12559.lax_universes);
               failhard = (uu___140_12559.failhard);
               nosynth = (uu___140_12559.nosynth);
               type_of = (uu___140_12559.type_of);
               universe_of = (uu___140_12559.universe_of);
               use_bv_sorts = (uu___140_12559.use_bv_sorts);
               qname_and_index = (uu___140_12559.qname_and_index);
               proof_ns = (uu___140_12559.proof_ns);
               synth = (uu___140_12559.synth);
               is_native_tactic = (uu___140_12559.is_native_tactic);
               identifier_info = (uu___140_12559.identifier_info);
               tc_hooks = (uu___140_12559.tc_hooks)
             }))
    | uu____12560 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12584  ->
             match uu____12584 with | (x,uu____12590) -> push_bv env1 x) env
        bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___141_12620 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_12620.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_12620.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let push_let_binding:
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
let push_module: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___142_12655 = env in
       {
         solver = (uu___142_12655.solver);
         range = (uu___142_12655.range);
         curmodule = (uu___142_12655.curmodule);
         gamma = [];
         gamma_cache = (uu___142_12655.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___142_12655.sigtab);
         is_pattern = (uu___142_12655.is_pattern);
         instantiate_imp = (uu___142_12655.instantiate_imp);
         effects = (uu___142_12655.effects);
         generalize = (uu___142_12655.generalize);
         letrecs = (uu___142_12655.letrecs);
         top_level = (uu___142_12655.top_level);
         check_uvars = (uu___142_12655.check_uvars);
         use_eq = (uu___142_12655.use_eq);
         is_iface = (uu___142_12655.is_iface);
         admit = (uu___142_12655.admit);
         lax = (uu___142_12655.lax);
         lax_universes = (uu___142_12655.lax_universes);
         failhard = (uu___142_12655.failhard);
         nosynth = (uu___142_12655.nosynth);
         type_of = (uu___142_12655.type_of);
         universe_of = (uu___142_12655.universe_of);
         use_bv_sorts = (uu___142_12655.use_bv_sorts);
         qname_and_index = (uu___142_12655.qname_and_index);
         proof_ns = (uu___142_12655.proof_ns);
         synth = (uu___142_12655.synth);
         is_native_tactic = (uu___142_12655.is_native_tactic);
         identifier_info = (uu___142_12655.identifier_info);
         tc_hooks = (uu___142_12655.tc_hooks)
       })
let push_univ_vars: env -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let open_universes_in:
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____12692 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____12692 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____12720 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____12720)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___143_12735 = env in
      {
        solver = (uu___143_12735.solver);
        range = (uu___143_12735.range);
        curmodule = (uu___143_12735.curmodule);
        gamma = (uu___143_12735.gamma);
        gamma_cache = (uu___143_12735.gamma_cache);
        modules = (uu___143_12735.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___143_12735.sigtab);
        is_pattern = (uu___143_12735.is_pattern);
        instantiate_imp = (uu___143_12735.instantiate_imp);
        effects = (uu___143_12735.effects);
        generalize = (uu___143_12735.generalize);
        letrecs = (uu___143_12735.letrecs);
        top_level = (uu___143_12735.top_level);
        check_uvars = (uu___143_12735.check_uvars);
        use_eq = false;
        is_iface = (uu___143_12735.is_iface);
        admit = (uu___143_12735.admit);
        lax = (uu___143_12735.lax);
        lax_universes = (uu___143_12735.lax_universes);
        failhard = (uu___143_12735.failhard);
        nosynth = (uu___143_12735.nosynth);
        type_of = (uu___143_12735.type_of);
        universe_of = (uu___143_12735.universe_of);
        use_bv_sorts = (uu___143_12735.use_bv_sorts);
        qname_and_index = (uu___143_12735.qname_and_index);
        proof_ns = (uu___143_12735.proof_ns);
        synth = (uu___143_12735.synth);
        is_native_tactic = (uu___143_12735.is_native_tactic);
        identifier_info = (uu___143_12735.identifier_info);
        tc_hooks = (uu___143_12735.tc_hooks)
      }
let expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let clear_expected_typ:
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun env_  ->
    let uu____12761 = expected_typ env_ in
    ((let uu___144_12767 = env_ in
      {
        solver = (uu___144_12767.solver);
        range = (uu___144_12767.range);
        curmodule = (uu___144_12767.curmodule);
        gamma = (uu___144_12767.gamma);
        gamma_cache = (uu___144_12767.gamma_cache);
        modules = (uu___144_12767.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___144_12767.sigtab);
        is_pattern = (uu___144_12767.is_pattern);
        instantiate_imp = (uu___144_12767.instantiate_imp);
        effects = (uu___144_12767.effects);
        generalize = (uu___144_12767.generalize);
        letrecs = (uu___144_12767.letrecs);
        top_level = (uu___144_12767.top_level);
        check_uvars = (uu___144_12767.check_uvars);
        use_eq = false;
        is_iface = (uu___144_12767.is_iface);
        admit = (uu___144_12767.admit);
        lax = (uu___144_12767.lax);
        lax_universes = (uu___144_12767.lax_universes);
        failhard = (uu___144_12767.failhard);
        nosynth = (uu___144_12767.nosynth);
        type_of = (uu___144_12767.type_of);
        universe_of = (uu___144_12767.universe_of);
        use_bv_sorts = (uu___144_12767.use_bv_sorts);
        qname_and_index = (uu___144_12767.qname_and_index);
        proof_ns = (uu___144_12767.proof_ns);
        synth = (uu___144_12767.synth);
        is_native_tactic = (uu___144_12767.is_native_tactic);
        identifier_info = (uu___144_12767.identifier_info);
        tc_hooks = (uu___144_12767.tc_hooks)
      }), uu____12761)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____12782 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___121_12792  ->
                    match uu___121_12792 with
                    | Binding_sig (uu____12795,se) -> [se]
                    | uu____12801 -> [])) in
          FStar_All.pipe_right uu____12782 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___145_12808 = env in
       {
         solver = (uu___145_12808.solver);
         range = (uu___145_12808.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___145_12808.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___145_12808.expected_typ);
         sigtab = (uu___145_12808.sigtab);
         is_pattern = (uu___145_12808.is_pattern);
         instantiate_imp = (uu___145_12808.instantiate_imp);
         effects = (uu___145_12808.effects);
         generalize = (uu___145_12808.generalize);
         letrecs = (uu___145_12808.letrecs);
         top_level = (uu___145_12808.top_level);
         check_uvars = (uu___145_12808.check_uvars);
         use_eq = (uu___145_12808.use_eq);
         is_iface = (uu___145_12808.is_iface);
         admit = (uu___145_12808.admit);
         lax = (uu___145_12808.lax);
         lax_universes = (uu___145_12808.lax_universes);
         failhard = (uu___145_12808.failhard);
         nosynth = (uu___145_12808.nosynth);
         type_of = (uu___145_12808.type_of);
         universe_of = (uu___145_12808.universe_of);
         use_bv_sorts = (uu___145_12808.use_bv_sorts);
         qname_and_index = (uu___145_12808.qname_and_index);
         proof_ns = (uu___145_12808.proof_ns);
         synth = (uu___145_12808.synth);
         is_native_tactic = (uu___145_12808.is_native_tactic);
         identifier_info = (uu___145_12808.identifier_info);
         tc_hooks = (uu___145_12808.tc_hooks)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____12890)::tl1 -> aux out tl1
      | (Binding_lid (uu____12894,(uu____12895,t)))::tl1 ->
          let uu____12910 =
            let uu____12917 = FStar_Syntax_Free.uvars t in
            ext out uu____12917 in
          aux uu____12910 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12924;
            FStar_Syntax_Syntax.index = uu____12925;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12932 =
            let uu____12939 = FStar_Syntax_Free.uvars t in
            ext out uu____12939 in
          aux uu____12932 tl1
      | (Binding_sig uu____12946)::uu____12947 -> out
      | (Binding_sig_inst uu____12956)::uu____12957 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13013)::tl1 -> aux out tl1
      | (Binding_univ uu____13025)::tl1 -> aux out tl1
      | (Binding_lid (uu____13029,(uu____13030,t)))::tl1 ->
          let uu____13045 =
            let uu____13048 = FStar_Syntax_Free.univs t in
            ext out uu____13048 in
          aux uu____13045 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13051;
            FStar_Syntax_Syntax.index = uu____13052;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13059 =
            let uu____13062 = FStar_Syntax_Free.univs t in
            ext out uu____13062 in
          aux uu____13059 tl1
      | (Binding_sig uu____13065)::uu____13066 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13120)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13136 = FStar_Util.fifo_set_add uname out in
          aux uu____13136 tl1
      | (Binding_lid (uu____13139,(uu____13140,t)))::tl1 ->
          let uu____13155 =
            let uu____13158 = FStar_Syntax_Free.univnames t in
            ext out uu____13158 in
          aux uu____13155 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13161;
            FStar_Syntax_Syntax.index = uu____13162;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13169 =
            let uu____13172 = FStar_Syntax_Free.univnames t in
            ext out uu____13172 in
          aux uu____13169 tl1
      | (Binding_sig uu____13175)::uu____13176 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___122_13201  ->
            match uu___122_13201 with
            | Binding_var x -> [x]
            | Binding_lid uu____13205 -> []
            | Binding_sig uu____13210 -> []
            | Binding_univ uu____13217 -> []
            | Binding_sig_inst uu____13218 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____13235 =
      let uu____13238 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____13238
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____13235 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____13263 =
      let uu____13264 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___123_13274  ->
                match uu___123_13274 with
                | Binding_var x ->
                    let uu____13276 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____13276
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13279) ->
                    let uu____13280 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____13280
                | Binding_sig (ls,uu____13282) ->
                    let uu____13287 =
                      let uu____13288 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13288
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____13287
                | Binding_sig_inst (ls,uu____13298,uu____13299) ->
                    let uu____13304 =
                      let uu____13305 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13305
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____13304)) in
      FStar_All.pipe_right uu____13264 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____13263 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____13324 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____13324
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13352  ->
                 fun uu____13353  ->
                   match (uu____13352, uu____13353) with
                   | ((b1,uu____13371),(b2,uu____13373)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___124_13420  ->
    match uu___124_13420 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____13421 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___125_13440  ->
             match uu___125_13440 with
             | Binding_sig (lids,uu____13446) -> FStar_List.append lids keys
             | uu____13451 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13457  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13493) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13512,uu____13513) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13550 = list_prefix p path1 in
            if uu____13550 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13564 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13564
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___146_13594 = e in
            {
              solver = (uu___146_13594.solver);
              range = (uu___146_13594.range);
              curmodule = (uu___146_13594.curmodule);
              gamma = (uu___146_13594.gamma);
              gamma_cache = (uu___146_13594.gamma_cache);
              modules = (uu___146_13594.modules);
              expected_typ = (uu___146_13594.expected_typ);
              sigtab = (uu___146_13594.sigtab);
              is_pattern = (uu___146_13594.is_pattern);
              instantiate_imp = (uu___146_13594.instantiate_imp);
              effects = (uu___146_13594.effects);
              generalize = (uu___146_13594.generalize);
              letrecs = (uu___146_13594.letrecs);
              top_level = (uu___146_13594.top_level);
              check_uvars = (uu___146_13594.check_uvars);
              use_eq = (uu___146_13594.use_eq);
              is_iface = (uu___146_13594.is_iface);
              admit = (uu___146_13594.admit);
              lax = (uu___146_13594.lax);
              lax_universes = (uu___146_13594.lax_universes);
              failhard = (uu___146_13594.failhard);
              nosynth = (uu___146_13594.nosynth);
              type_of = (uu___146_13594.type_of);
              universe_of = (uu___146_13594.universe_of);
              use_bv_sorts = (uu___146_13594.use_bv_sorts);
              qname_and_index = (uu___146_13594.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___146_13594.synth);
              is_native_tactic = (uu___146_13594.is_native_tactic);
              identifier_info = (uu___146_13594.identifier_info);
              tc_hooks = (uu___146_13594.tc_hooks)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___147_13621 = e in
    {
      solver = (uu___147_13621.solver);
      range = (uu___147_13621.range);
      curmodule = (uu___147_13621.curmodule);
      gamma = (uu___147_13621.gamma);
      gamma_cache = (uu___147_13621.gamma_cache);
      modules = (uu___147_13621.modules);
      expected_typ = (uu___147_13621.expected_typ);
      sigtab = (uu___147_13621.sigtab);
      is_pattern = (uu___147_13621.is_pattern);
      instantiate_imp = (uu___147_13621.instantiate_imp);
      effects = (uu___147_13621.effects);
      generalize = (uu___147_13621.generalize);
      letrecs = (uu___147_13621.letrecs);
      top_level = (uu___147_13621.top_level);
      check_uvars = (uu___147_13621.check_uvars);
      use_eq = (uu___147_13621.use_eq);
      is_iface = (uu___147_13621.is_iface);
      admit = (uu___147_13621.admit);
      lax = (uu___147_13621.lax);
      lax_universes = (uu___147_13621.lax_universes);
      failhard = (uu___147_13621.failhard);
      nosynth = (uu___147_13621.nosynth);
      type_of = (uu___147_13621.type_of);
      universe_of = (uu___147_13621.universe_of);
      use_bv_sorts = (uu___147_13621.use_bv_sorts);
      qname_and_index = (uu___147_13621.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___147_13621.synth);
      is_native_tactic = (uu___147_13621.is_native_tactic);
      identifier_info = (uu___147_13621.identifier_info);
      tc_hooks = (uu___147_13621.tc_hooks)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____13636::rest ->
        let uu___148_13640 = e in
        {
          solver = (uu___148_13640.solver);
          range = (uu___148_13640.range);
          curmodule = (uu___148_13640.curmodule);
          gamma = (uu___148_13640.gamma);
          gamma_cache = (uu___148_13640.gamma_cache);
          modules = (uu___148_13640.modules);
          expected_typ = (uu___148_13640.expected_typ);
          sigtab = (uu___148_13640.sigtab);
          is_pattern = (uu___148_13640.is_pattern);
          instantiate_imp = (uu___148_13640.instantiate_imp);
          effects = (uu___148_13640.effects);
          generalize = (uu___148_13640.generalize);
          letrecs = (uu___148_13640.letrecs);
          top_level = (uu___148_13640.top_level);
          check_uvars = (uu___148_13640.check_uvars);
          use_eq = (uu___148_13640.use_eq);
          is_iface = (uu___148_13640.is_iface);
          admit = (uu___148_13640.admit);
          lax = (uu___148_13640.lax);
          lax_universes = (uu___148_13640.lax_universes);
          failhard = (uu___148_13640.failhard);
          nosynth = (uu___148_13640.nosynth);
          type_of = (uu___148_13640.type_of);
          universe_of = (uu___148_13640.universe_of);
          use_bv_sorts = (uu___148_13640.use_bv_sorts);
          qname_and_index = (uu___148_13640.qname_and_index);
          proof_ns = rest;
          synth = (uu___148_13640.synth);
          is_native_tactic = (uu___148_13640.is_native_tactic);
          identifier_info = (uu___148_13640.identifier_info);
          tc_hooks = (uu___148_13640.tc_hooks)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___149_13653 = e in
      {
        solver = (uu___149_13653.solver);
        range = (uu___149_13653.range);
        curmodule = (uu___149_13653.curmodule);
        gamma = (uu___149_13653.gamma);
        gamma_cache = (uu___149_13653.gamma_cache);
        modules = (uu___149_13653.modules);
        expected_typ = (uu___149_13653.expected_typ);
        sigtab = (uu___149_13653.sigtab);
        is_pattern = (uu___149_13653.is_pattern);
        instantiate_imp = (uu___149_13653.instantiate_imp);
        effects = (uu___149_13653.effects);
        generalize = (uu___149_13653.generalize);
        letrecs = (uu___149_13653.letrecs);
        top_level = (uu___149_13653.top_level);
        check_uvars = (uu___149_13653.check_uvars);
        use_eq = (uu___149_13653.use_eq);
        is_iface = (uu___149_13653.is_iface);
        admit = (uu___149_13653.admit);
        lax = (uu___149_13653.lax);
        lax_universes = (uu___149_13653.lax_universes);
        failhard = (uu___149_13653.failhard);
        nosynth = (uu___149_13653.nosynth);
        type_of = (uu___149_13653.type_of);
        universe_of = (uu___149_13653.universe_of);
        use_bv_sorts = (uu___149_13653.use_bv_sorts);
        qname_and_index = (uu___149_13653.qname_and_index);
        proof_ns = ns;
        synth = (uu___149_13653.synth);
        is_native_tactic = (uu___149_13653.is_native_tactic);
        identifier_info = (uu___149_13653.identifier_info);
        tc_hooks = (uu___149_13653.tc_hooks)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____13682 =
        FStar_List.map
          (fun fpns  ->
             let uu____13704 =
               let uu____13705 =
                 let uu____13706 =
                   FStar_List.map
                     (fun uu____13718  ->
                        match uu____13718 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____13706 in
               Prims.strcat uu____13705 "]" in
             Prims.strcat "[" uu____13704) pns in
      FStar_String.concat ";" uu____13682 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____13734  -> ());
    push = (fun uu____13736  -> ());
    pop = (fun uu____13738  -> ());
    encode_modul = (fun uu____13741  -> fun uu____13742  -> ());
    encode_sig = (fun uu____13745  -> fun uu____13746  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____13752 =
             let uu____13759 = FStar_Options.peek () in (e, g, uu____13759) in
           [uu____13752]);
    solve = (fun uu____13775  -> fun uu____13776  -> fun uu____13777  -> ());
    is_trivial = (fun uu____13784  -> fun uu____13785  -> false);
    finish = (fun uu____13787  -> ());
    refresh = (fun uu____13789  -> ())
  }