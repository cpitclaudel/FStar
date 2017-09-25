open Prims
let tc_one_file:
  Prims.string Prims.list ->
    FStar_Universal.uenv ->
      ((Prims.string FStar_Pervasives_Native.option,Prims.string)
         FStar_Pervasives_Native.tuple2,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                          FStar_Pervasives_Native.tuple2,
        Prims.string Prims.list) FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun uenv  ->
      let uu____31 = uenv in
      match uu____31 with
      | (dsenv,env) ->
          let uu____52 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____90 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl in
                (match uu____90 with
                 | (uu____117,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____142 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____142 with
                 | (uu____169,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____52 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2[@@deriving show]
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
[@@deriving show]
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun msg  ->
      let res = FStar_Universal.push_context env msg in
      FStar_Options.push (); res
let pop:
  'Auu____295 .
    ('Auu____295,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.string -> Prims.unit
  =
  fun env  ->
    fun msg  ->
      FStar_Universal.pop_context (FStar_Pervasives_Native.snd env) msg;
      FStar_Options.pop ()
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck[@@deriving show]
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____317 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____322 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____327 -> false
let set_check_kind:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____342  ->
    fun check_kind  ->
      match uu____342 with
      | (dsenv,tcenv) ->
          let tcenv1 =
            let uu___243_355 = tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___243_355.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___243_355.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___243_355.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___243_355.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___243_355.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___243_355.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___243_355.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___243_355.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___243_355.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___243_355.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___243_355.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___243_355.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___243_355.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___243_355.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___243_355.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___243_355.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___243_355.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___243_355.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
              FStar_TypeChecker_Env.lax_universes =
                (uu___243_355.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___243_355.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___243_355.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.type_of =
                (uu___243_355.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___243_355.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___243_355.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___243_355.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___243_355.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___243_355.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___243_355.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___243_355.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___243_355.FStar_TypeChecker_Env.tc_hooks)
            } in
          let dsenv1 =
            FStar_ToSyntax_Env.set_syntax_only dsenv
              (check_kind = SyntaxCheck) in
          (dsenv1, tcenv1)
let cleanup:
  'Auu____361 .
    ('Auu____361,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____369  ->
    match uu____369 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let with_captured_errors':
  'Auu____384 'Auu____385 .
    ('Auu____385,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      (('Auu____385,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
         -> 'Auu____384 FStar_Pervasives_Native.option)
        -> 'Auu____384 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      let tcenv = FStar_Pervasives_Native.snd env in
      try f env
      with
      | FStar_All.Failure msg ->
          let msg1 =
            Prims.strcat "ASSERTION FAILURE: "
              (Prims.strcat msg
                 (Prims.strcat "\n"
                    (Prims.strcat "F* may be in an inconsistent state.\n"
                       (Prims.strcat
                          "Please file a bug report, ideally with a "
                          "minimized version of the program that triggered the error.")))) in
          ((let uu____439 =
              let uu____446 =
                let uu____451 = FStar_TypeChecker_Env.get_range tcenv in
                (msg1, uu____451) in
              [uu____446] in
            FStar_TypeChecker_Err.add_errors tcenv uu____439);
           FStar_Util.print_error msg1;
           FStar_Pervasives_Native.None)
      | FStar_Errors.Error (msg,r) ->
          (FStar_TypeChecker_Err.add_errors tcenv [(msg, r)];
           FStar_Pervasives_Native.None)
      | FStar_Errors.Err msg ->
          ((let uu____474 =
              let uu____481 =
                let uu____486 = FStar_TypeChecker_Env.get_range tcenv in
                (msg, uu____486) in
              [uu____481] in
            FStar_TypeChecker_Err.add_errors tcenv uu____474);
           FStar_Pervasives_Native.None)
let with_captured_errors:
  'Auu____503 'Auu____504 .
    ('Auu____504,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      (('Auu____504,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
         -> 'Auu____503 FStar_Pervasives_Native.option)
        -> 'Auu____503 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      let uu____540 = FStar_Options.trace_error () in
      if uu____540 then f env else with_captured_errors' env f
let check_frag:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      (FStar_Parser_ParseIt.input_frag,Prims.bool)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,(FStar_ToSyntax_Env.env,
                                                                    FStar_TypeChecker_Env.env)
                                                                    FStar_Pervasives_Native.tuple2,
          Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option
  =
  fun uu____577  ->
    fun curmod  ->
      fun frag  ->
        match uu____577 with
        | (dsenv,tcenv) ->
            with_captured_errors (dsenv, tcenv)
              (fun uu____626  ->
                 match uu____626 with
                 | (dsenv1,tcenv1) ->
                     let uu____647 =
                       FStar_Universal.tc_one_fragment curmod dsenv1 tcenv1
                         frag in
                     (match uu____647 with
                      | FStar_Pervasives_Native.Some (m,dsenv2,env) ->
                          let uu____687 =
                            let uu____700 = FStar_Errors.get_err_count () in
                            (m, (dsenv2, env), uu____700) in
                          FStar_Pervasives_Native.Some uu____687
                      | uu____719 -> FStar_Pervasives_Native.None))
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____757 =
      FStar_List.partition
        (fun x  ->
           let uu____770 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____771 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____770 <> uu____771) deps in
    match uu____757 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____798 =
                  (let uu____801 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____801) ||
                    (let uu____803 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____803) in
                if uu____798
                then
                  let uu____804 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____804
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____807 ->
              ((let uu____811 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____811);
               FStar_Pervasives_Native.None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list[@@deriving
                                                                show]
type deps_stack_t = env_t Prims.list[@@deriving show]
let rec push_then_do_or_revert_all:
  'Auu____840 .
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
           FStar_Pervasives_Native.tuple2 ->
           'Auu____840 FStar_Pervasives_Native.option)
          ->
          (((FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
              FStar_Pervasives_Native.tuple2 Prims.list,'Auu____840)
             FStar_Pervasives_Native.tuple2,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                              FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun env  ->
    fun stack  ->
      fun fn  ->
        let revert1 env1 stack1 =
          (let uu____940 =
             FStar_Util.string_of_int (FStar_List.length stack1) in
           FStar_Util.print1 "Reverting %s entries" uu____940);
          (let rec aux env2 stack2 =
             match stack2 with
             | [] -> env2
             | env'::stack' -> (pop env2 "typecheck_modul"; aux env' stack') in
           aux env1 stack1) in
        let stack1 = env :: stack in
        let env' = push env "tc prims, deps, or interface" in
        let uu____1017 = with_captured_errors env' fn in
        match uu____1017 with
        | FStar_Pervasives_Native.None  ->
            let uu____1038 = revert1 env' stack1 in FStar_Util.Inr uu____1038
        | FStar_Pervasives_Native.Some res -> FStar_Util.Inl (stack1, res)
let tc_deps:
  env_t ->
    deps_stack_t ->
      Prims.string Prims.list ->
        ((deps_stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3,
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2)
          FStar_Util.either
  =
  fun env  ->
    fun stack  ->
      fun dependencies  ->
        let rec aux env1 stack1 ts remaining =
          match remaining with
          | [] -> FStar_Util.Inl (stack1, env1, ts)
          | uu____1163 ->
              let stack2 = env1 :: stack1 in
              let push_kind =
                let uu____1170 = FStar_Options.lax () in
                if uu____1170 then LaxCheck else FullCheck in
              ((let uu____1173 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____1173 FStar_Pervasives.ignore);
               (let uu____1174 =
                  push_then_do_or_revert_all env1 stack2
                    (fun env2  ->
                       let uu____1236 =
                         let uu____1255 = set_check_kind env2 push_kind in
                         tc_one_file remaining uu____1255 in
                       FStar_All.pipe_left
                         (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                         uu____1236) in
                match uu____1174 with
                | FStar_Util.Inr env2 -> FStar_Util.Inr env2
                | FStar_Util.Inl (stack3,((intf,impl),env2,remaining1)) ->
                    let intf_t =
                      FStar_All.pipe_right intf
                        (FStar_Util.map_option
                           FStar_Util.get_file_last_modification_time) in
                    let impl_t =
                      FStar_Util.get_file_last_modification_time impl in
                    aux env2 stack3 ((intf, impl, intf_t, impl_t) :: ts)
                      remaining1)) in
        aux env stack [] dependencies
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___229_1501  ->
    match uu___229_1501 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1505 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1505
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1507 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1510 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1528 -> true
    | uu____1533 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1549 -> uu____1549
let js_fail: 'Auu____1560 . Prims.string -> FStar_Util.json -> 'Auu____1560 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___230_1572  ->
    match uu___230_1572 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___231_1578  ->
    match uu___231_1578 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1587 .
    (FStar_Util.json -> 'Auu____1587) ->
      FStar_Util.json -> 'Auu____1587 Prims.list
  =
  fun k  ->
    fun uu___232_1600  ->
      match uu___232_1600 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___233_1618  ->
    match uu___233_1618 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1643 = js_str s in
    match uu____1643 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1644 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1649 = js_str s in
    match uu____1649 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____1650 -> js_fail "reduction rule" s
type completion_context =
  | CKCode
  | CKOption of Prims.bool
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_CKCode: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____1667 -> false
let uu___is_CKOption: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____1673 -> false
let __proj__CKOption__item___0: completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____1691 -> false
let __proj__CKModuleOrNamespace__item___0:
  completion_context ->
    (Prims.bool,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0
let js_optional_completion_context:
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1721 = js_str k1 in
        (match uu____1721 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1722 ->
             js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type lookup_context =
  | LKSymbolOnly
  | LKModule
  | LKOption
  | LKCode[@@deriving show]
let uu___is_LKSymbolOnly: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKSymbolOnly  -> true | uu____1727 -> false
let uu___is_LKModule: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____1732 -> false
let uu___is_LKOption: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____1737 -> false
let uu___is_LKCode: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____1742 -> false
let js_optional_lookup_context:
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1752 = js_str k1 in
        (match uu____1752 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____1753 ->
             js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type position =
  (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type push_query =
  {
  push_kind: push_kind;
  push_code: Prims.string;
  push_line: Prims.int;
  push_column: Prims.int;
  push_peek_only: Prims.bool;}[@@deriving show]
let __proj__Mkpush_query__item__push_kind: push_query -> push_kind =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_kind
let __proj__Mkpush_query__item__push_code: push_query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_code
let __proj__Mkpush_query__item__push_line: push_query -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_line
let __proj__Mkpush_query__item__push_column: push_query -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_column
let __proj__Mkpush_query__item__push_peek_only: push_query -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} ->
        __fname__push_peek_only
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of push_query
  | VfsAdd of (Prims.string FStar_Pervasives_Native.option,Prims.string)
  FStar_Pervasives_Native.tuple2
  | AutoComplete of (Prims.string,completion_context)
  FStar_Pervasives_Native.tuple2
  | Lookup of
  (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
  Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  | Compute of
  (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Search of Prims.string
  | GenericError of Prims.string
  | ProtocolViolation of Prims.string[@@deriving show]
and query = {
  qq: query';
  qid: Prims.string;}[@@deriving show]
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1899 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1904 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1909 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1914 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1920 -> false
let __proj__Push__item___0: query' -> push_query =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_VfsAdd: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____1940 -> false
let __proj__VfsAdd__item___0:
  query' ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | VfsAdd _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1976 -> false
let __proj__AutoComplete__item___0:
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2014 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2072 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2110 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_GenericError: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____2124 -> false
let __proj__GenericError__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | GenericError _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2138 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let __proj__Mkquery__item__qq: query -> query' =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qq
let __proj__Mkquery__item__qid: query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qid
let query_needs_current_module: query' -> Prims.bool =
  fun uu___234_2162  ->
    match uu___234_2162 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push
        { push_kind = uu____2163; push_code = uu____2164;
          push_line = uu____2165; push_column = uu____2166;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____2167 -> false
    | GenericError uu____2174 -> false
    | ProtocolViolation uu____2175 -> false
    | Push uu____2176 -> true
    | AutoComplete uu____2177 -> true
    | Lookup uu____2182 -> true
    | Compute uu____2195 -> true
    | Search uu____2204 -> true
let interactive_protocol_vernum: Prims.int = Prims.parse_int "2"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "autocomplete/context";
  "compute";
  "compute/reify";
  "compute/pure-subterms";
  "describe-protocol";
  "describe-repl";
  "exit";
  "vfs-add";
  "lookup";
  "lookup/context";
  "lookup/documentation";
  "lookup/definition";
  "peek";
  "pop";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2214 -> true
    | uu____2215 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2223 -> uu____2223
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol[@@deriving show]
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2228 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2233 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2238 -> false
let try_assoc:
  'Auu____2247 'Auu____2248 .
    'Auu____2248 ->
      ('Auu____2248,'Auu____2247) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2247 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2271 =
        FStar_Util.try_find
          (fun uu____2285  ->
             match uu____2285 with | (k,uu____2291) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2271
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2308 =
          let uu____2309 =
            let uu____2310 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2310 in
          ProtocolViolation uu____2309 in
        { qq = uu____2308; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2337 = try_assoc key a in
      match uu____2337 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2341 =
            let uu____2342 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2342 in
          FStar_Exn.raise uu____2341 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2357 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2357 js_str in
    try
      let query =
        let uu____2366 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2366 js_str in
      let args =
        let uu____2374 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2374 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2391 = try_assoc k args in
        match uu____2391 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2399 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2400 =
              let uu____2401 =
                let uu____2402 = arg "kind" in
                FStar_All.pipe_right uu____2402 js_pushkind in
              let uu____2403 =
                let uu____2404 = arg "code" in
                FStar_All.pipe_right uu____2404 js_str in
              let uu____2405 =
                let uu____2406 = arg "line" in
                FStar_All.pipe_right uu____2406 js_int in
              let uu____2407 =
                let uu____2408 = arg "column" in
                FStar_All.pipe_right uu____2408 js_int in
              {
                push_kind = uu____2401;
                push_code = uu____2403;
                push_line = uu____2405;
                push_column = uu____2407;
                push_peek_only = (query = "peek")
              } in
            Push uu____2400
        | "push" ->
            let uu____2409 =
              let uu____2410 =
                let uu____2411 = arg "kind" in
                FStar_All.pipe_right uu____2411 js_pushkind in
              let uu____2412 =
                let uu____2413 = arg "code" in
                FStar_All.pipe_right uu____2413 js_str in
              let uu____2414 =
                let uu____2415 = arg "line" in
                FStar_All.pipe_right uu____2415 js_int in
              let uu____2416 =
                let uu____2417 = arg "column" in
                FStar_All.pipe_right uu____2417 js_int in
              {
                push_kind = uu____2410;
                push_code = uu____2412;
                push_line = uu____2414;
                push_column = uu____2416;
                push_peek_only = (query = "peek")
              } in
            Push uu____2409
        | "autocomplete" ->
            let uu____2418 =
              let uu____2423 =
                let uu____2424 = arg "partial-symbol" in
                FStar_All.pipe_right uu____2424 js_str in
              let uu____2425 =
                let uu____2426 = try_arg "context" in
                FStar_All.pipe_right uu____2426
                  js_optional_completion_context in
              (uu____2423, uu____2425) in
            AutoComplete uu____2418
        | "lookup" ->
            let uu____2431 =
              let uu____2444 =
                let uu____2445 = arg "symbol" in
                FStar_All.pipe_right uu____2445 js_str in
              let uu____2446 =
                let uu____2447 = try_arg "context" in
                FStar_All.pipe_right uu____2447 js_optional_lookup_context in
              let uu____2452 =
                let uu____2461 =
                  let uu____2470 = try_arg "location" in
                  FStar_All.pipe_right uu____2470
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2461
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2528 =
                          let uu____2529 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2529 js_str in
                        let uu____2530 =
                          let uu____2531 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2531 js_int in
                        let uu____2532 =
                          let uu____2533 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2533 js_int in
                        (uu____2528, uu____2530, uu____2532))) in
              let uu____2534 =
                let uu____2537 = arg "requested-info" in
                FStar_All.pipe_right uu____2537 (js_list js_str) in
              (uu____2444, uu____2446, uu____2452, uu____2534) in
            Lookup uu____2431
        | "compute" ->
            let uu____2550 =
              let uu____2559 =
                let uu____2560 = arg "term" in
                FStar_All.pipe_right uu____2560 js_str in
              let uu____2561 =
                let uu____2566 = try_arg "rules" in
                FStar_All.pipe_right uu____2566
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2559, uu____2561) in
            Compute uu____2550
        | "search" ->
            let uu____2581 =
              let uu____2582 = arg "terms" in
              FStar_All.pipe_right uu____2582 js_str in
            Search uu____2581
        | "vfs-add" ->
            let uu____2583 =
              let uu____2590 =
                let uu____2593 = try_arg "filename" in
                FStar_All.pipe_right uu____2593
                  (FStar_Util.map_option js_str) in
              let uu____2600 =
                let uu____2601 = arg "contents" in
                FStar_All.pipe_right uu____2601 js_str in
              (uu____2590, uu____2600) in
            VfsAdd uu____2583
        | uu____2604 ->
            let uu____2605 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2605 in
      { qq = uu____2399; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2619 = FStar_Util.read_line stream in
      match uu____2619 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2623 = FStar_Util.json_of_string line in
          (match uu____2623 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let json_of_opt:
  'Auu____2639 .
    ('Auu____2639 -> FStar_Util.json) ->
      'Auu____2639 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2657 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2657
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2664 =
      let uu____2667 =
        let uu____2668 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2668 in
      let uu____2669 =
        let uu____2672 =
          let uu____2673 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2673 in
        [uu____2672] in
      uu____2667 :: uu____2669 in
    FStar_Util.JsonList uu____2664
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2686 =
          let uu____2693 =
            let uu____2700 =
              let uu____2705 = json_of_pos b in ("beg", uu____2705) in
            let uu____2706 =
              let uu____2713 =
                let uu____2718 = json_of_pos e in ("end", uu____2718) in
              [uu____2713] in
            uu____2700 :: uu____2706 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2693 in
        FStar_Util.JsonAssoc uu____2686
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2739 = FStar_Range.file_of_use_range r in
    let uu____2740 = FStar_Range.start_of_use_range r in
    let uu____2741 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2739 uu____2740 uu____2741
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2746 = FStar_Range.file_of_range r in
    let uu____2747 = FStar_Range.start_of_range r in
    let uu____2748 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2746 uu____2747 uu____2748
let json_of_issue_level: FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
let json_of_issue: FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____2757 =
      let uu____2764 =
        let uu____2771 =
          let uu____2778 =
            let uu____2783 =
              let uu____2784 =
                let uu____2787 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2793 = json_of_use_range r in [uu____2793] in
                let uu____2794 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2800 = json_of_def_range r in [uu____2800]
                  | uu____2801 -> [] in
                FStar_List.append uu____2787 uu____2794 in
              FStar_Util.JsonList uu____2784 in
            ("ranges", uu____2783) in
          [uu____2778] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2771 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2764 in
    FStar_Util.JsonAssoc uu____2757
type symbol_lookup_result =
  {
  slr_name: Prims.string;
  slr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  slr_typ: Prims.string FStar_Pervasives_Native.option;
  slr_doc: Prims.string FStar_Pervasives_Native.option;
  slr_def: Prims.string FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mksymbol_lookup_result__item__slr_name:
  symbol_lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_name
let __proj__Mksymbol_lookup_result__item__slr_def_range:
  symbol_lookup_result -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_def_range
let __proj__Mksymbol_lookup_result__item__slr_typ:
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_typ
let __proj__Mksymbol_lookup_result__item__slr_doc:
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_doc
let __proj__Mksymbol_lookup_result__item__slr_def:
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_def
let alist_of_symbol_lookup_result:
  symbol_lookup_result ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun lr  ->
    let uu____2959 =
      let uu____2966 =
        let uu____2971 = json_of_opt json_of_def_range lr.slr_def_range in
        ("defined-at", uu____2971) in
      let uu____2972 =
        let uu____2979 =
          let uu____2984 =
            json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43) lr.slr_typ in
          ("type", uu____2984) in
        let uu____2985 =
          let uu____2992 =
            let uu____2997 =
              json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44) lr.slr_doc in
            ("documentation", uu____2997) in
          let uu____2998 =
            let uu____3005 =
              let uu____3010 =
                json_of_opt (fun _0_45  -> FStar_Util.JsonStr _0_45)
                  lr.slr_def in
              ("definition", uu____3010) in
            [uu____3005] in
          uu____2992 :: uu____2998 in
        uu____2979 :: uu____2985 in
      uu____2966 :: uu____2972 in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____2959
let alist_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3043 =
      FStar_List.map (fun _0_46  -> FStar_Util.JsonStr _0_46)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_47  -> FStar_Util.JsonList _0_47) uu____3043 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet
  | OptReset
  | OptReadOnly[@@deriving show]
let uu___is_OptSet: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3064 -> false
let uu___is_OptReset: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3069 -> false
let uu___is_OptReadOnly: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3074 -> false
let string_of_option_permission_level:
  fstar_option_permission_level -> Prims.string =
  fun uu___235_3078  ->
    match uu___235_3078 with
    | OptSet  -> ""
    | OptReset  -> "requires #reset-options"
    | OptReadOnly  -> "read-only"
type fstar_option =
  {
  opt_name: Prims.string;
  opt_sig: Prims.string;
  opt_value: FStar_Options.option_val;
  opt_default: FStar_Options.option_val;
  opt_type: FStar_Options.opt_type;
  opt_snippets: Prims.string Prims.list;
  opt_documentation: Prims.string FStar_Pervasives_Native.option;
  opt_permission_level: fstar_option_permission_level;}[@@deriving show]
let __proj__Mkfstar_option__item__opt_name: fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_name
let __proj__Mkfstar_option__item__opt_sig: fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_sig
let __proj__Mkfstar_option__item__opt_value:
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_value
let __proj__Mkfstar_option__item__opt_default:
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_default
let __proj__Mkfstar_option__item__opt_type:
  fstar_option -> FStar_Options.opt_type =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_type
let __proj__Mkfstar_option__item__opt_snippets:
  fstar_option -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_snippets
let __proj__Mkfstar_option__item__opt_documentation:
  fstar_option -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_documentation
let __proj__Mkfstar_option__item__opt_permission_level:
  fstar_option -> fstar_option_permission_level =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_permission_level
let rec kind_of_fstar_option_type: FStar_Options.opt_type -> Prims.string =
  fun uu___236_3254  ->
    match uu___236_3254 with
    | FStar_Options.Const uu____3255 -> "flag"
    | FStar_Options.IntStr uu____3256 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3257 -> "path"
    | FStar_Options.SimpleStr uu____3258 -> "string"
    | FStar_Options.EnumStr uu____3259 -> "enum"
    | FStar_Options.OpenEnumStr uu____3262 -> "open enum"
    | FStar_Options.PostProcessed (uu____3269,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3277,typ) ->
        kind_of_fstar_option_type typ
let rec snippets_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string Prims.list =
  fun name  ->
    fun typ  ->
      let mk_field field_name =
        Prims.strcat "${" (Prims.strcat field_name "}") in
      let mk_snippet name1 argstring =
        Prims.strcat "--"
          (Prims.strcat name1
             (if argstring <> "" then Prims.strcat " " argstring else "")) in
      let rec arg_snippets_of_type typ1 =
        match typ1 with
        | FStar_Options.Const uu____3313 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3326,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3334,elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____3340 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____3340
let rec json_of_fstar_option_value:
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___237_3346  ->
    match uu___237_3346 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3354 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____3354
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let alist_of_fstar_option:
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____3367 =
      let uu____3374 =
        let uu____3381 =
          let uu____3386 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3386) in
        let uu____3387 =
          let uu____3394 =
            let uu____3399 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3399) in
          let uu____3400 =
            let uu____3407 =
              let uu____3412 =
                json_of_opt (fun _0_48  -> FStar_Util.JsonStr _0_48)
                  opt.opt_documentation in
              ("documentation", uu____3412) in
            let uu____3413 =
              let uu____3420 =
                let uu____3425 =
                  let uu____3426 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____3426 in
                ("type", uu____3425) in
              [uu____3420;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____3407 :: uu____3413 in
          uu____3394 :: uu____3400 in
        uu____3381 :: uu____3387 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3374 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3367
let json_of_fstar_option: fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____3463 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____3463
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3475 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3475);
    FStar_Util.print_raw "\n"
let write_response:
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation" in
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
let write_message: Prims.string -> FStar_Util.json -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", contents)])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____3537  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3540 =
        FStar_List.map (fun _0_49  -> FStar_Util.JsonStr _0_49)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3540 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: alist_of_protocol_info))
let sig_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name in
      let uu____3556 = FStar_Options.desc_of_opt_type typ in
      match uu____3556 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
let fstar_options_list_cache: fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____3565 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3594  ->
            match uu____3594 with
            | (_shortname,name,typ,doc1) ->
                let uu____3609 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____3609
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____3621 = sig_of_fstar_option name typ in
                        let uu____3622 = snippets_of_fstar_option name typ in
                        let uu____3625 =
                          let uu____3626 = FStar_Options.settable name in
                          if uu____3626
                          then OptSet
                          else
                            (let uu____3628 = FStar_Options.resettable name in
                             if uu____3628 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____3621;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____3622;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____3625
                        })))) in
  FStar_All.pipe_right uu____3565
    (FStar_List.sortWith
       (fun o1  ->
          fun o2  ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
let fstar_options_map_cache: fstar_option FStar_Util.smap =
  let cache = FStar_Util.smap_create (Prims.parse_int "50") in
  FStar_List.iter (fun opt  -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache
let update_option: fstar_option -> fstar_option =
  fun opt  ->
    let uu___250_3653 = opt in
    let uu____3654 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___250_3653.opt_name);
      opt_sig = (uu___250_3653.opt_sig);
      opt_value = uu____3654;
      opt_default = (uu___250_3653.opt_default);
      opt_type = (uu___250_3653.opt_type);
      opt_snippets = (uu___250_3653.opt_snippets);
      opt_documentation = (uu___250_3653.opt_documentation);
      opt_permission_level = (uu___250_3653.opt_permission_level)
    }
let current_fstar_options:
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____3666 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____3666
let trim_option_name:
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____3682 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____3682)
    else ("", opt_name)
type partial_repl_state =
  {
  prepl_env: env_t;
  prepl_fname: Prims.string;
  prepl_stdin: FStar_Util.stream_reader;}[@@deriving show]
let __proj__Mkpartial_repl_state__item__prepl_env:
  partial_repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { prepl_env = __fname__prepl_env; prepl_fname = __fname__prepl_fname;
        prepl_stdin = __fname__prepl_stdin;_} -> __fname__prepl_env
let __proj__Mkpartial_repl_state__item__prepl_fname:
  partial_repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { prepl_env = __fname__prepl_env; prepl_fname = __fname__prepl_fname;
        prepl_stdin = __fname__prepl_stdin;_} -> __fname__prepl_fname
let __proj__Mkpartial_repl_state__item__prepl_stdin:
  partial_repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { prepl_env = __fname__prepl_env; prepl_fname = __fname__prepl_fname;
        prepl_stdin = __fname__prepl_stdin;_} -> __fname__prepl_stdin
type full_repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_deps: (deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2;
  repl_curmod: modul_t;
  repl_env: env_t;
  repl_stdin: FStar_Util.stream_reader;
  repl_names: FStar_Interactive_CompletionTable.table;}[@@deriving show]
let __proj__Mkfull_repl_state__item__repl_line: full_repl_state -> Prims.int
  =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_line
let __proj__Mkfull_repl_state__item__repl_column:
  full_repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_column
let __proj__Mkfull_repl_state__item__repl_fname:
  full_repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_fname
let __proj__Mkfull_repl_state__item__repl_deps:
  full_repl_state ->
    (deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_deps
let __proj__Mkfull_repl_state__item__repl_curmod: full_repl_state -> modul_t
  =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_curmod
let __proj__Mkfull_repl_state__item__repl_env: full_repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_env
let __proj__Mkfull_repl_state__item__repl_stdin:
  full_repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_stdin
let __proj__Mkfull_repl_state__item__repl_names:
  full_repl_state -> FStar_Interactive_CompletionTable.table =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_names
type repl_state =
  | PartialReplState of partial_repl_state
  | FullReplState of full_repl_state[@@deriving show]
let uu___is_PartialReplState: repl_state -> Prims.bool =
  fun projectee  ->
    match projectee with | PartialReplState _0 -> true | uu____3902 -> false
let __proj__PartialReplState__item___0: repl_state -> partial_repl_state =
  fun projectee  -> match projectee with | PartialReplState _0 -> _0
let uu___is_FullReplState: repl_state -> Prims.bool =
  fun projectee  ->
    match projectee with | FullReplState _0 -> true | uu____3916 -> false
let __proj__FullReplState__item___0: repl_state -> full_repl_state =
  fun projectee  -> match projectee with | FullReplState _0 -> _0
let wrap_repl_state:
  'Auu____3937 'Auu____3938 'Auu____3939 'Auu____3940 .
    ('Auu____3940 -> 'Auu____3939) ->
      ('Auu____3938,('Auu____3940,'Auu____3937) FStar_Util.either)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____3938,('Auu____3939,'Auu____3937) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun fn  ->
    fun r  ->
      match r with
      | (status,FStar_Util.Inr n1) -> (status, (FStar_Util.Inr n1))
      | (status,FStar_Util.Inl full_st) ->
          let uu____3994 =
            let uu____3999 = fn full_st in FStar_Util.Inl uu____3999 in
          (status, uu____3994)
let repl_stdin: repl_state -> FStar_Util.stream_reader =
  fun uu___238_4007  ->
    match uu___238_4007 with
    | PartialReplState st -> st.prepl_stdin
    | FullReplState st -> st.repl_stdin
let repl_fname: repl_state -> Prims.string =
  fun uu___239_4013  ->
    match uu___239_4013 with
    | PartialReplState st -> st.prepl_fname
    | FullReplState st -> st.repl_fname
let repl_stack: full_repl_state Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let repl_stack_empty: Prims.unit -> Prims.bool =
  fun uu____4032  ->
    let uu____4033 = FStar_ST.op_Bang repl_stack in
    match uu____4033 with | [] -> true | uu____4054 -> false
let pop_repl:
  'Auu____4061 .
    ('Auu____4061,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
      -> full_repl_state
  =
  fun env  ->
    let uu____4074 = FStar_ST.op_Bang repl_stack in
    match uu____4074 with
    | [] -> failwith "Too many pops"
    | st'::stack ->
        (pop env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         (let uu____4120 = repl_stack_empty () in
          if uu____4120 then cleanup st'.repl_env else ());
         st')
let push_repl:
  push_kind ->
    full_repl_state ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun push_kind  ->
    fun st  ->
      (let uu____4135 =
         let uu____4138 = FStar_ST.op_Bang repl_stack in st :: uu____4138 in
       FStar_ST.op_Colon_Equals repl_stack uu____4135);
      (let uu____4177 = set_check_kind st.repl_env push_kind in
       push uu____4177 "")
let json_of_repl_state: repl_state -> FStar_Util.json =
  fun st  ->
    let deps =
      match st with
      | PartialReplState pst -> []
      | FullReplState st1 -> FStar_Pervasives_Native.snd st1.repl_deps in
    let uu____4229 =
      let uu____4236 =
        let uu____4241 =
          let uu____4242 =
            FStar_List.map
              (fun uu____4262  ->
                 match uu____4262 with
                 | (uu____4275,fstname,uu____4277,uu____4278) ->
                     FStar_Util.JsonStr fstname) deps in
          FStar_Util.JsonList uu____4242 in
        ("loaded-dependencies", uu____4241) in
      let uu____4287 =
        let uu____4294 =
          let uu____4299 =
            let uu____4300 =
              let uu____4303 =
                current_fstar_options (fun uu____4308  -> true) in
              FStar_List.map json_of_fstar_option uu____4303 in
            FStar_Util.JsonList uu____4300 in
          ("options", uu____4299) in
        [uu____4294] in
      uu____4236 :: uu____4287 in
    FStar_Util.JsonAssoc uu____4229
let with_printed_effect_args:
  'Auu____4325 . (Prims.unit -> 'Auu____4325) -> 'Auu____4325 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4337  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4348  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4354  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____4359 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4359,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____4388 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4388) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____4417 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4417) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4434 =
      let uu____4439 = json_of_repl_state st in (QueryOK, uu____4439) in
    (uu____4434, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____4454 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4454) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error:
  'Auu____4489 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4489) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let run_vfs_add:
  'Auu____4526 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____4526) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt (repl_fname st) opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop:
  'Auu____4569 .
    full_repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (full_repl_state,'Auu____4569) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4586 = repl_stack_empty () in
    if uu____4586
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let uu____4608 =
         let uu____4613 = pop_repl st.repl_env in FStar_Util.Inl uu____4613 in
       ((QueryOK, FStar_Util.JsonNull), uu____4608))
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple3
  | NTOpen of (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
  FStar_Pervasives_Native.tuple2
  | NTInclude of (FStar_Ident.lid,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2
  | NTBinding of FStar_TypeChecker_Env.binding[@@deriving show]
let uu___is_NTAlias: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____4663 -> false
let __proj__NTAlias__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____4699 -> false
let __proj__NTOpen__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____4729 -> false
let __proj__NTInclude__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____4755 -> false
let __proj__NTBinding__item___0:
  name_tracking_event -> FStar_TypeChecker_Env.binding =
  fun projectee  -> match projectee with | NTBinding _0 -> _0
let query_of_ids:
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query =
  fun ids  -> FStar_List.map FStar_Ident.text_of_id ids
let query_of_lid:
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query =
  fun lid  ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
let update_names_from_event:
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table
  =
  fun cur_mod_str  ->
    fun table  ->
      fun evt  ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str in
        match evt with
        | NTAlias (host,id,included) ->
            if is_cur_mod host
            then
              let uu____4795 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id) [] uu____4795
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____4804 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____4804
            else table
        | NTInclude (host,included) ->
            let uu____4808 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____4810 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____4808 uu____4810
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____4818) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____4820) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____4826,uu____4827) -> lids
              | uu____4832 -> [] in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     (FStar_Ident.text_of_id lid.FStar_Ident.ident) lid)
              table lids
let commit_name_tracking:
  modul_t ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table
  =
  fun cur_mod  ->
    fun names1  ->
      fun name_events  ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____4862 = FStar_Syntax_Syntax.mod_name md in
              uu____4862.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let fresh_name_tracking_hooks:
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____4881  ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____4893 =
        let uu____4896 = FStar_ST.op_Bang events in evt :: uu____4896 in
      FStar_ST.op_Colon_Equals events uu____4893 in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____4989 =
                 let uu____4990 =
                   let uu____4995 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____4995, op) in
                 NTOpen uu____4990 in
               push_event uu____4989);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____5001 =
                 let uu____5002 =
                   let uu____5007 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____5007, ns) in
                 NTInclude uu____5002 in
               push_event uu____5001);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____5015 =
                   let uu____5016 =
                     let uu____5023 = FStar_ToSyntax_Env.current_module dsenv in
                     (uu____5023, x, l) in
                   NTAlias uu____5016 in
                 push_event uu____5015)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____5028  -> fun s  -> push_event (NTBinding s))
      })
let track_name_changes:
  env_t ->
    (env_t,env_t ->
             (env_t,name_tracking_event Prims.list)
               FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5045  ->
    match uu____5045 with
    | (dsenv,tcenv) ->
        let uu____5072 =
          let uu____5077 = FStar_ToSyntax_Env.ds_hooks dsenv in
          let uu____5078 = FStar_TypeChecker_Env.tc_hooks tcenv in
          (uu____5077, uu____5078) in
        (match uu____5072 with
         | (dsenv_old_hooks,tcenv_old_hooks) ->
             let uu____5093 = fresh_name_tracking_hooks () in
             (match uu____5093 with
              | (events,dsenv_new_hooks,tcenv_new_hooks) ->
                  let uu____5127 =
                    let uu____5132 =
                      FStar_ToSyntax_Env.set_ds_hooks dsenv dsenv_new_hooks in
                    let uu____5133 =
                      FStar_TypeChecker_Env.set_tc_hooks tcenv
                        tcenv_new_hooks in
                    (uu____5132, uu____5133) in
                  (uu____5127,
                    ((fun uu____5159  ->
                        match uu____5159 with
                        | (dsenv1,tcenv1) ->
                            let uu____5176 =
                              let uu____5181 =
                                FStar_ToSyntax_Env.set_ds_hooks dsenv1
                                  dsenv_old_hooks in
                              let uu____5182 =
                                FStar_TypeChecker_Env.set_tc_hooks tcenv1
                                  tcenv_old_hooks in
                              (uu____5181, uu____5182) in
                            let uu____5183 =
                              let uu____5186 = FStar_ST.op_Bang events in
                              FStar_List.rev uu____5186 in
                            (uu____5176, uu____5183))))))
let collect_errors: Prims.unit -> FStar_Errors.issue Prims.list =
  fun uu____5232  ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_regular_push:
  'Auu____5243 .
    full_repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (full_repl_state,'Auu____5243) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____5264 = query in
      match uu____5264 with
      | { push_kind = kind; push_code = text1; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let env = push_repl kind st in
          let uu____5287 = track_name_changes env in
          (match uu____5287 with
           | (env1,finish_name_tracking) ->
               let uu____5330 =
                 let uu____5343 = repl_stack_empty () in
                 if uu____5343
                 then (true, (env1, (st.repl_deps)))
                 else (false, (env1, (st.repl_deps))) in
               (match uu____5330 with
                | (restore_cmd_line_options1,(env2,deps)) ->
                    (if restore_cmd_line_options1
                     then
                       (let uu____5413 =
                          FStar_Options.restore_cmd_line_options false in
                        FStar_All.pipe_right uu____5413
                          FStar_Pervasives.ignore)
                     else ();
                     (let frag =
                        {
                          FStar_Parser_ParseIt.frag_text = text1;
                          FStar_Parser_ParseIt.frag_line = line;
                          FStar_Parser_ParseIt.frag_col = column
                        } in
                      let res = check_frag env2 st.repl_curmod (frag, false) in
                      let errors =
                        let uu____5434 = collect_errors () in
                        FStar_All.pipe_right uu____5434
                          (FStar_List.map json_of_issue) in
                      let st' =
                        let uu___251_5442 = st in
                        {
                          repl_line = line;
                          repl_column = column;
                          repl_fname = (uu___251_5442.repl_fname);
                          repl_deps = deps;
                          repl_curmod = (uu___251_5442.repl_curmod);
                          repl_env = (uu___251_5442.repl_env);
                          repl_stdin = (uu___251_5442.repl_stdin);
                          repl_names = (uu___251_5442.repl_names)
                        } in
                      match res with
                      | FStar_Pervasives_Native.Some (curmod,env3,nerrs) when
                          (nerrs = (Prims.parse_int "0")) &&
                            (peek_only = false)
                          ->
                          let uu____5482 = finish_name_tracking env3 in
                          (match uu____5482 with
                           | (env4,name_events) ->
                               let uu____5507 =
                                 let uu____5512 =
                                   let uu___252_5513 = st' in
                                   let uu____5514 =
                                     commit_name_tracking curmod
                                       st'.repl_names name_events in
                                   {
                                     repl_line = (uu___252_5513.repl_line);
                                     repl_column =
                                       (uu___252_5513.repl_column);
                                     repl_fname = (uu___252_5513.repl_fname);
                                     repl_deps = (uu___252_5513.repl_deps);
                                     repl_curmod = curmod;
                                     repl_env = env4;
                                     repl_stdin = (uu___252_5513.repl_stdin);
                                     repl_names = uu____5514
                                   } in
                                 FStar_Util.Inl uu____5512 in
                               ((QueryOK, (FStar_Util.JsonList errors)),
                                 uu____5507))
                      | uu____5523 ->
                          let uu____5538 = finish_name_tracking env2 in
                          (match uu____5538 with
                           | (env3,uu____5558) ->
                               let uu____5563 =
                                 run_pop
                                   (let uu___253_5577 = st' in
                                    {
                                      repl_line = (uu___253_5577.repl_line);
                                      repl_column =
                                        (uu___253_5577.repl_column);
                                      repl_fname = (uu___253_5577.repl_fname);
                                      repl_deps = (uu___253_5577.repl_deps);
                                      repl_curmod =
                                        (uu___253_5577.repl_curmod);
                                      repl_env = env3;
                                      repl_stdin = (uu___253_5577.repl_stdin);
                                      repl_names = (uu___253_5577.repl_names)
                                    }) in
                               (match uu____5563 with
                                | (uu____5590,st'') ->
                                    let status =
                                      if peek_only then QueryOK else QueryNOK in
                                    ((status, (FStar_Util.JsonList errors)),
                                      st'')))))))
let capitalize: Prims.string -> Prims.string =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1") in
       let uu____5624 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.strcat (FStar_String.uppercase first) uu____5624)
let add_module_completions:
  Prims.string ->
    Prims.string Prims.list ->
      FStar_Interactive_CompletionTable.table ->
        FStar_Interactive_CompletionTable.table
  =
  fun this_fname  ->
    fun deps  ->
      fun table  ->
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
        let loaded_mods_set =
          let uu____5651 = FStar_Util.psmap_empty () in
          let uu____5654 =
            let uu____5657 = FStar_Options.prims () in uu____5657 :: deps in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____5667 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____5667 true) uu____5651
            uu____5654 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____5683  ->
               match uu____5683 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____5695 = capitalize modname in
                        FStar_Util.split uu____5695 "." in
                      let uu____5696 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____5696 mod_path ns_query)) table
          (FStar_List.rev mods)
let tc_prims_and_deps:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string ->
      ((Prims.string Prims.list,(deps_stack_t,m_timestamps)
                                  FStar_Pervasives_Native.tuple2,env_t)
         FStar_Pervasives_Native.tuple3,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                          FStar_Pervasives_Native.tuple2)
        FStar_Util.either
  =
  fun env  ->
    fun filename  ->
      let uu____5737 =
        push_then_do_or_revert_all env []
          (fun env1  ->
             let uu____5787 = FStar_Universal.tc_prims env1 in
             FStar_All.pipe_left
               (fun _0_50  -> FStar_Pervasives_Native.Some _0_50) uu____5787) in
      match uu____5737 with
      | FStar_Util.Inr env1 -> FStar_Util.Inr env1
      | FStar_Util.Inl (stack,(uu____5896,dsenv,tcenv)) ->
          let env1 = (dsenv, tcenv) in
          let uu____5958 =
            push_then_do_or_revert_all env1 stack
              (fun _env  ->
                 let uu____6000 = deps_of_our_file filename in
                 FStar_All.pipe_left
                   (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                   uu____6000) in
          (match uu____5958 with
           | FStar_Util.Inr env2 -> FStar_Util.Inr env2
           | FStar_Util.Inl (stack1,(deps,maybe_interface)) ->
               let uu____6151 = tc_deps env1 stack1 deps in
               (match uu____6151 with
                | FStar_Util.Inr env2 -> FStar_Util.Inr env2
                | FStar_Util.Inl (stack2,env2,ts) ->
                    (match maybe_interface with
                     | FStar_Pervasives_Native.None  ->
                         FStar_Util.Inl (deps, (stack2, ts), env2)
                     | FStar_Pervasives_Native.Some intf ->
                         let uu____6273 =
                           push_then_do_or_revert_all env2 stack2
                             (fun env3  ->
                                let uu____6307 =
                                  FStar_Universal.load_interface_decls env3
                                    intf in
                                FStar_All.pipe_left
                                  (fun _0_52  ->
                                     FStar_Pervasives_Native.Some _0_52)
                                  uu____6307) in
                         (match uu____6273 with
                          | FStar_Util.Inr env3 -> FStar_Util.Inr env3
                          | FStar_Util.Inl (stack3,env3) ->
                              FStar_Util.Inl (deps, (stack3, ts), env3)))))
let rephrase_dependency_error: FStar_Errors.issue -> FStar_Errors.issue =
  fun issue  ->
    let uu___254_6477 = issue in
    let uu____6478 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____6478;
      FStar_Errors.issue_level = (uu___254_6477.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___254_6477.FStar_Errors.issue_range)
    }
let run_initial_push:
  'Auu____6485 .
    partial_repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6485) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let env = st.prepl_env in
      let on_successful_init uu____6545 deps repl_deps =
        match uu____6545 with
        | (env1,name_events) ->
            (FStar_TypeChecker_Env.toggle_id_info
               (FStar_Pervasives_Native.snd env1) true;
             (let initial_names =
                add_module_completions st.prepl_fname deps
                  FStar_Interactive_CompletionTable.empty in
              let full_st =
                let uu____6593 =
                  commit_name_tracking FStar_Pervasives_Native.None
                    initial_names name_events in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = (st.prepl_fname);
                  repl_deps;
                  repl_curmod = FStar_Pervasives_Native.None;
                  repl_env = env1;
                  repl_stdin = (st.prepl_stdin);
                  repl_names = uu____6593
                } in
              let uu____6594 = run_regular_push full_st query in
              FStar_All.pipe_left
                (wrap_repl_state (fun _0_53  -> FullReplState _0_53))
                uu____6594)) in
      let on_failed_init uu____6656 =
        match uu____6656 with
        | (env1,name_events) ->
            let errors =
              let uu____6684 = collect_errors () in
              FStar_List.map rephrase_dependency_error uu____6684 in
            let js_errors =
              FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
            ((QueryNOK, (FStar_Util.JsonList js_errors)),
              (FStar_Util.Inl (PartialReplState st))) in
      let uu____6702 = track_name_changes env in
      match uu____6702 with
      | (env1,finish_name_tracking) ->
          let uu____6745 = tc_prims_and_deps env1 st.prepl_fname in
          (match uu____6745 with
           | FStar_Util.Inl (deps,repl_deps,env2) ->
               let uu____6809 = finish_name_tracking env2 in
               on_successful_init uu____6809 deps repl_deps
           | FStar_Util.Inr env2 ->
               let uu____6841 = finish_name_tracking env2 in
               on_failed_init uu____6841)
let run_push:
  'Auu____6854 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6854) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      match st with
      | PartialReplState st1 -> run_initial_push st1 query
      | FullReplState st1 ->
          let uu____6877 = run_regular_push st1 query in
          FStar_All.pipe_left
            (wrap_repl_state (fun _0_54  -> FullReplState _0_54)) uu____6877
let run_symbol_lookup:
  full_repl_state ->
    Prims.string ->
      (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
                          FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____6968 = st.repl_env in
          match uu____6968 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____7002 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____7002 in
                let lid1 =
                  let uu____7006 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____7006 in
                let uu____7011 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____7011
                  (FStar_Util.map_option
                     (fun uu____7066  ->
                        match uu____7066 with
                        | ((uu____7085,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____7102 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____7102
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____7131 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____7131
                  (fun uu___240_7175  ->
                     match uu___240_7175 with
                     | (FStar_Util.Inr (se,uu____7197),uu____7198) ->
                         let uu____7227 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____7227
                     | uu____7228 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____7280  ->
                     match uu____7280 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____7327 -> info_at_pos_opt
                | FStar_Pervasives_Native.None  ->
                    if symbol = ""
                    then FStar_Pervasives_Native.None
                    else info_of_lid_str symbol in
              let response =
                match info_opt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                    let name =
                      match name_or_lid with
                      | FStar_Util.Inl name -> name
                      | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
                    let typ_str =
                      if FStar_List.mem "type" requested_info
                      then
                        let uu____7455 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____7455
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____7463 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____7474 -> FStar_Pervasives_Native.None in
                    let def_range =
                      if FStar_List.mem "defined-at" requested_info
                      then FStar_Pervasives_Native.Some rng
                      else FStar_Pervasives_Native.None in
                    let result =
                      {
                        slr_name = name;
                        slr_def_range = def_range;
                        slr_typ = typ_str;
                        slr_doc = doc_str;
                        slr_def = def_str
                      } in
                    let uu____7486 =
                      let uu____7497 = alist_of_symbol_lookup_result result in
                      ("symbol", uu____7497) in
                    FStar_Pervasives_Native.Some uu____7486 in
              (match response with
               | FStar_Pervasives_Native.None  ->
                   FStar_Util.Inl "Symbol not found"
               | FStar_Pervasives_Native.Some info -> FStar_Util.Inr info)
let run_option_lookup:
  Prims.string ->
    (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
                    FStar_Pervasives_Native.tuple2)
      FStar_Util.either
  =
  fun opt_name  ->
    let uu____7603 = trim_option_name opt_name in
    match uu____7603 with
    | (uu____7622,trimmed_name) ->
        let uu____7624 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____7624 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____7652 =
               let uu____7663 =
                 let uu____7670 = update_option opt in
                 alist_of_fstar_option uu____7670 in
               ("option", uu____7663) in
             FStar_Util.Inr uu____7652)
let run_module_lookup:
  full_repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                    FStar_Pervasives_Native.tuple2 Prims.list)
                      FStar_Pervasives_Native.tuple2)
        FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      let query = FStar_Util.split symbol "." in
      let uu____7712 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____7712 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____7740 =
            let uu____7751 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____7751) in
          FStar_Util.Inr uu____7740
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____7775 =
            let uu____7786 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____7786) in
          FStar_Util.Inr uu____7775
let run_code_lookup:
  full_repl_state ->
    Prims.string ->
      (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
                          FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____7859 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____7859 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____7919 ->
              let uu____7930 = run_module_lookup st symbol in
              (match uu____7930 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let run_lookup':
  full_repl_state ->
    Prims.string ->
      lookup_context ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list)
                            FStar_Pervasives_Native.tuple2)
              FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            match context with
            | LKSymbolOnly  ->
                run_symbol_lookup st symbol pos_opt requested_info
            | LKModule  -> run_module_lookup st symbol
            | LKOption  -> run_option_lookup symbol
            | LKCode  -> run_code_lookup st symbol pos_opt requested_info
let run_lookup:
  'Auu____8091 .
    full_repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (full_repl_state,'Auu____8091) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____8144 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____8144 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter:
  'Auu____8230 .
    ('Auu____8230,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____8230,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___241_8244  ->
    match uu___241_8244 with
    | (uu____8249,FStar_Interactive_CompletionTable.Namespace uu____8250) ->
        FStar_Pervasives_Native.None
    | (uu____8255,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____8256;
         FStar_Interactive_CompletionTable.mod_path = uu____8257;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____8264 =
          let uu____8269 =
            let uu____8270 =
              let uu___255_8271 = md in
              let uu____8272 =
                let uu____8273 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.strcat uu____8273 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____8272;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___255_8271.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___255_8271.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____8270 in
          (pth, uu____8269) in
        FStar_Pervasives_Native.Some uu____8264
let run_code_autocomplete:
  'Auu____8284 .
    full_repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (full_repl_state,'Auu____8284) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      let needle = FStar_Util.split search_term "." in
      let mods_and_nss =
        FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
          st.repl_names needle code_autocomplete_mod_filter in
      let lids =
        FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names
          needle in
      let json =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result
          (FStar_List.append lids mods_and_nss) in
      ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let run_module_autocomplete:
  'Auu____8339 'Auu____8340 'Auu____8341 .
    full_repl_state ->
      Prims.string ->
        'Auu____8341 ->
          'Auu____8340 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (full_repl_state,'Auu____8339) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun modules1  ->
        fun namespaces  ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.repl_names needle
              (fun _0_55  -> FStar_Pervasives_Native.Some _0_55) in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let candidates_of_fstar_option:
  Prims.int ->
    Prims.bool ->
      fstar_option ->
        FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____8405 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only") in
        match uu____8405 with
        | (may_set,explanation) ->
            let opt_type = kind_of_fstar_option_type opt.opt_type in
            let annot =
              if may_set
              then opt_type
              else
                Prims.strcat "("
                  (Prims.strcat explanation
                     (Prims.strcat " " (Prims.strcat opt_type ")"))) in
            FStar_All.pipe_right opt.opt_snippets
              (FStar_List.map
                 (fun snippet  ->
                    {
                      FStar_Interactive_CompletionTable.completion_match_length
                        = match_len;
                      FStar_Interactive_CompletionTable.completion_candidate
                        = snippet;
                      FStar_Interactive_CompletionTable.completion_annotation
                        = annot
                    }))
let run_option_autocomplete:
  'Auu____8435 .
    full_repl_state ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (full_repl_state,'Auu____8435) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____8460 = trim_option_name search_term in
        match uu____8460 with
        | ("--",trimmed_name) ->
            let matcher opt =
              FStar_Util.starts_with opt.opt_name trimmed_name in
            let options = current_fstar_options matcher in
            let match_len = FStar_String.length search_term in
            let collect_candidates =
              candidates_of_fstar_option match_len is_reset in
            let results = FStar_List.concatMap collect_candidates options in
            let json =
              FStar_List.map
                FStar_Interactive_CompletionTable.json_of_completion_result
                results in
            ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
        | (uu____8511,uu____8512) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete:
  'Auu____8529 .
    full_repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (full_repl_state,'Auu____8529) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun context  ->
        match context with
        | CKCode  -> run_code_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules1,namespaces) ->
            run_module_autocomplete st search_term modules1 namespaces
let run_compute:
  'Auu____8565 .
    full_repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (full_repl_state,'Auu____8565) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let run_and_rewind st1 task =
          let env' = push st1.repl_env "#compute" in
          let results = task st1 in
          pop env' "#compute"; (results, (FStar_Util.Inl st1)) in
        let dummy_let_fragment term1 =
          let dummy_decl =
            FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
          {
            FStar_Parser_ParseIt.frag_text = dummy_decl;
            FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
            FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
          } in
        let normalize_term1 tcenv rules1 t =
          FStar_TypeChecker_Normalize.normalize rules1 tcenv t in
        let find_let_body ses =
          match ses with
          | {
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                ((uu____8692,{ FStar_Syntax_Syntax.lbname = uu____8693;
                               FStar_Syntax_Syntax.lbunivs = univs1;
                               FStar_Syntax_Syntax.lbtyp = uu____8695;
                               FStar_Syntax_Syntax.lbeff = uu____8696;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____8698);
              FStar_Syntax_Syntax.sigrng = uu____8699;
              FStar_Syntax_Syntax.sigquals = uu____8700;
              FStar_Syntax_Syntax.sigmeta = uu____8701;
              FStar_Syntax_Syntax.sigattrs = uu____8702;_}::[] ->
              FStar_Pervasives_Native.Some (univs1, def)
          | uu____8741 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____8760 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____8760 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____8784) ->
              FStar_Pervasives_Native.Some decls
          | uu____8829 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____8861 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____8861 in
        let typecheck tcenv decls =
          let uu____8879 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____8879 with | (ses,uu____8893,uu____8894) -> ses in
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Normalize.Beta;
                 FStar_TypeChecker_Normalize.Iota;
                 FStar_TypeChecker_Normalize.Zeta;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant])
            [FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.Primops] in
        run_and_rewind st
          (fun st1  ->
             let uu____8922 = st1.repl_env in
             match uu____8922 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____8934 ->
                      let uu____8935 = parse1 frag in
                      (match uu____8935 with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr "Could not parse this term"))
                       | FStar_Pervasives_Native.Some decls ->
                           let aux uu____8958 =
                             let decls1 = desugar dsenv decls in
                             let ses = typecheck tcenv decls1 in
                             match find_let_body ses with
                             | FStar_Pervasives_Native.None  ->
                                 (QueryNOK,
                                   (FStar_Util.JsonStr
                                      "Typechecking yielded an unexpected term"))
                             | FStar_Pervasives_Native.Some (univs1,def) ->
                                 let uu____8993 =
                                   FStar_Syntax_Subst.open_univ_vars univs1
                                     def in
                                 (match uu____8993 with
                                  | (univs2,def1) ->
                                      let tcenv1 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          tcenv univs2 in
                                      let normalized =
                                        normalize_term1 tcenv1 rules1 def1 in
                                      let uu____9006 =
                                        let uu____9007 =
                                          term_to_string tcenv1 normalized in
                                        FStar_Util.JsonStr uu____9007 in
                                      (QueryOK, uu____9006)) in
                           let uu____9008 = FStar_Options.trace_error () in
                           if uu____9008
                           then aux ()
                           else
                             (try aux ()
                              with
                              | e ->
                                  let uu____9033 =
                                    let uu____9034 =
                                      FStar_Errors.issue_of_exn e in
                                    match uu____9034 with
                                    | FStar_Pervasives_Native.Some issue ->
                                        let uu____9038 =
                                          FStar_Errors.format_issue issue in
                                        FStar_Util.JsonStr uu____9038
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Exn.raise e in
                                  (QueryNOK, uu____9033)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid[@@deriving show]
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}[@@deriving show]
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____9060 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____9074 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let __proj__Mksearch_term__item__st_negate: search_term -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_negate
let __proj__Mksearch_term__item__st_term: search_term -> search_term' =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_term
let st_cost: search_term' -> Prims.int =
  fun uu___242_9098  ->
    match uu___242_9098 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ:
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref;}[@@deriving show]
let __proj__Mksearch_candidate__item__sc_lid:
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
let __proj__Mksearch_candidate__item__sc_typ:
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
let __proj__Mksearch_candidate__item__sc_fvars:
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____9266 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____9273 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____9266; sc_fvars = uu____9273 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____9322 = FStar_ST.op_Bang sc.sc_typ in
      match uu____9322 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____9347 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____9347 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____9368,typ),uu____9370) ->
                typ in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____9414 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____9414 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____9457 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____9457 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____9500 = sc_typ tcenv sc in term_to_string tcenv uu____9500 in
        let uu____9501 =
          let uu____9508 =
            let uu____9513 =
              let uu____9514 =
                let uu____9515 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____9515.FStar_Ident.str in
              FStar_Util.JsonStr uu____9514 in
            ("lid", uu____9513) in
          [uu____9508; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____9501
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____9535 -> true
    | uu____9536 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____9544 -> uu____9544
let run_search:
  'Auu____9551 .
    full_repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (full_repl_state,'Auu____9551) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____9572 = st.repl_env in
      match uu____9572 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____9600 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____9600 in
            found <> term.st_negate in
          let parse1 search_str1 =
            let parse_one term =
              let negate = FStar_Util.starts_with term "-" in
              let term1 =
                if negate
                then FStar_Util.substring_from term (Prims.parse_int "1")
                else term in
              let beg_quote = FStar_Util.starts_with term1 "\"" in
              let end_quote = FStar_Util.ends_with term1 "\"" in
              let strip_quotes str =
                if (FStar_String.length str) < (Prims.parse_int "2")
                then FStar_Exn.raise (InvalidSearch "Empty search term")
                else
                  FStar_Util.substring str (Prims.parse_int "1")
                    ((FStar_String.length term1) - (Prims.parse_int "2")) in
              let parsed =
                if beg_quote <> end_quote
                then
                  let uu____9624 =
                    let uu____9625 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____9625 in
                  FStar_Exn.raise uu____9624
                else
                  if beg_quote
                  then
                    (let uu____9627 = strip_quotes term1 in
                     NameContainsStr uu____9627)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____9630 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____9630 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____9633 =
                           let uu____9634 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____9634 in
                         FStar_Exn.raise uu____9633
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____9650 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____9650 in
          let results =
            try
              let terms = parse1 search_str in
              let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
              let all_candidates = FStar_List.map sc_of_lid all_lidents in
              let matches_all candidate =
                FStar_List.for_all (st_matches candidate) terms in
              let cmp r1 r2 =
                FStar_Util.compare (r1.sc_lid).FStar_Ident.str
                  (r2.sc_lid).FStar_Ident.str in
              let results = FStar_List.filter matches_all all_candidates in
              let sorted1 = FStar_Util.sort_with cmp results in
              let js =
                FStar_List.map (json_of_search_result dsenv tcenv) sorted1 in
              match results with
              | [] ->
                  let kwds =
                    let uu____9713 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____9713 in
                  let uu____9716 =
                    let uu____9717 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____9717 in
                  FStar_Exn.raise uu____9716
              | uu____9722 -> (QueryOK, (FStar_Util.JsonList js))
            with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
          (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun q  ->
      match q with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | GenericError message -> run_generic_error st message
      | ProtocolViolation query -> run_protocol_violation st query
      | VfsAdd (fname,contents) -> run_vfs_add st fname contents
      | Push pquery when pquery.push_peek_only = false -> run_push st pquery
      | uu____9782 ->
          (match st with
           | PartialReplState uu____9795 ->
               run_generic_error st
                 "Please send a code fragment before running this query"
           | FullReplState st1 ->
               let uu____9797 =
                 match q with
                 | Pop  -> run_pop st1
                 | AutoComplete (search_term,context) ->
                     run_autocomplete st1 search_term context
                 | Lookup (symbol,context,pos_opt,rq_info) ->
                     run_lookup st1 symbol context pos_opt rq_info
                 | Compute (term,rules) -> run_compute st1 term rules
                 | Search term -> run_search st1 term
                 | Push pquery when pquery.push_peek_only = true ->
                     run_regular_push st1 pquery
                 | Exit  -> failwith "impossible"
                 | DescribeProtocol  -> failwith "impossible"
                 | DescribeRepl  -> failwith "impossible"
                 | GenericError uu____9884 -> failwith "impossible"
                 | ProtocolViolation uu____9897 -> failwith "impossible"
                 | Push uu____9910 -> failwith "impossible"
                 | VfsAdd uu____9923 -> failwith "impossible" in
               wrap_repl_state (fun _0_56  -> FullReplState _0_56) uu____9797)
let validate_query: repl_state -> query -> query =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push
          { push_kind = SyntaxCheck ; push_code = uu____9954;
            push_line = uu____9955; push_column = uu____9956;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____9957 ->
          (match st with
           | FullReplState
               { repl_line = uu____9958; repl_column = uu____9959;
                 repl_fname = uu____9960; repl_deps = uu____9961;
                 repl_curmod = FStar_Pervasives_Native.None ;
                 repl_env = uu____9962; repl_stdin = uu____9963;
                 repl_names = uu____9964;_}
               when query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____9969 -> q)
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query =
      let uu____9975 = read_interactive_query (repl_stdin st) in
      validate_query st uu____9975 in
    let uu____9976 = run_query st query.qq in
    match uu____9976 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____10018 =
      let uu____10021 = FStar_ST.op_Bang issues in e :: uu____10021 in
    FStar_ST.op_Colon_Equals issues uu____10018 in
  let count_errors uu____10091 =
    let uu____10092 =
      let uu____10095 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____10095 in
    FStar_List.length uu____10092 in
  let report1 uu____10137 =
    let uu____10138 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____10138 in
  let clear1 uu____10176 = FStar_ST.op_Colon_Equals issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo =
      (fun s  -> write_message "info" (FStar_Util.JsonStr s));
    FStar_Util.printer_prwarning =
      (fun s  -> write_message "warning" (FStar_Util.JsonStr s));
    FStar_Util.printer_prerror =
      (fun s  -> write_message "error" (FStar_Util.JsonStr s));
    FStar_Util.printer_prgeneric =
      (fun label1  ->
         fun get_string  ->
           fun get_json  ->
             let uu____10231 = get_json () in
             write_message label1 uu____10231)
  }
let initial_range: FStar_Range.range =
  let uu____10232 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____10233 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____10232 uu____10233
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let env = FStar_Universal.init_env () in
     let env1 =
       let uu____10249 =
         FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env)
           initial_range in
       ((FStar_Pervasives_Native.fst env), uu____10249) in
     let init_st =
       let uu____10251 =
         let uu____10252 = FStar_Util.open_stdin () in
         {
           prepl_env = env1;
           prepl_fname = filename;
           prepl_stdin = uu____10252
         } in
       PartialReplState uu____10251 in
     let uu____10253 =
       (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
     if uu____10253
     then
       let uu____10254 =
         let uu____10255 = FStar_Options.file_list () in
         FStar_List.hd uu____10255 in
       FStar_SMTEncoding_Solver.with_hints_db uu____10254
         (fun uu____10259  -> go init_st)
     else go init_st)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____10267 =
       let uu____10268 = FStar_Options.codegen () in
       FStar_Option.isSome uu____10268 in
     if uu____10267
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____10272 = FStar_Options.trace_error () in
     if uu____10272
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))