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
let tc_prims:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let uu____273 = FStar_Universal.tc_prims env in
    match uu____273 with | (uu____288,dsenv,env1) -> (dsenv, env1)
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
  'Auu____337 .
    ('Auu____337,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
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
    match projectee with | SyntaxCheck  -> true | uu____359 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____364 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____369 -> false
let set_check_kind:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____384  ->
    fun check_kind  ->
      match uu____384 with
      | (dsenv,tcenv) ->
          let tcenv1 =
            let uu___241_397 = tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___241_397.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___241_397.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___241_397.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___241_397.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___241_397.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___241_397.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___241_397.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___241_397.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___241_397.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___241_397.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___241_397.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___241_397.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___241_397.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___241_397.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___241_397.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___241_397.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___241_397.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___241_397.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
              FStar_TypeChecker_Env.lax_universes =
                (uu___241_397.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___241_397.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___241_397.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.type_of =
                (uu___241_397.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___241_397.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___241_397.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___241_397.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___241_397.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___241_397.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___241_397.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___241_397.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___241_397.FStar_TypeChecker_Env.tc_hooks)
            } in
          let dsenv1 =
            FStar_ToSyntax_Env.set_syntax_only dsenv
              (check_kind = SyntaxCheck) in
          (dsenv1, tcenv1)
let cleanup:
  'Auu____403 .
    ('Auu____403,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2 ->
      Prims.unit
  =
  fun uu____411  ->
    match uu____411 with
    | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
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
  fun uu____451  ->
    fun curmod  ->
      fun frag  ->
        match uu____451 with
        | (dsenv,env) ->
            (try
               let uu____515 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____515 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____555 =
                     let uu____568 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____568) in
                   FStar_Pervasives_Native.Some uu____555
               | uu____587 -> FStar_Pervasives_Native.None
             with
             | FStar_All.Failure msg when
                 let uu____631 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____631 ->
                 let msg1 =
                   Prims.strcat "ASSERTION FAILURE: "
                     (Prims.strcat msg
                        (Prims.strcat "\n"
                           (Prims.strcat
                              "F* may be in an inconsistent state.\n"
                              (Prims.strcat
                                 "Please file a bug report, ideally with a "
                                 "minimized version of the program that triggered the error.")))) in
                 ((let uu____634 =
                     let uu____641 =
                       let uu____646 = FStar_TypeChecker_Env.get_range env in
                       (msg1, uu____646) in
                     [uu____641] in
                   FStar_TypeChecker_Err.add_errors env uu____634);
                  FStar_Util.print_error msg1;
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Error (msg,r) when
                 let uu____670 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____670 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____693 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____693 ->
                 ((let uu____695 =
                     let uu____702 =
                       let uu____707 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____707) in
                     [uu____702] in
                   FStar_TypeChecker_Err.add_errors env uu____695);
                  FStar_Pervasives_Native.None))
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____743 =
      FStar_List.partition
        (fun x  ->
           let uu____756 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____757 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____756 <> uu____757) deps in
    match uu____743 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____784 =
                  (let uu____787 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____787) ||
                    (let uu____789 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____789) in
                if uu____784
                then
                  let uu____790 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____790
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____793 ->
              ((let uu____797 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____797);
               FStar_Pervasives_Native.None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list[@@deriving
                                                                show]
type deps_stack_t = env_t Prims.list[@@deriving show]
let rec tc_deps:
  deps_stack_t ->
    env_t ->
      Prims.string Prims.list ->
        m_timestamps ->
          (env_t,(deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2)
            FStar_Pervasives_Native.tuple2
  =
  fun deps_stack  ->
    fun env  ->
      fun remaining  ->
        fun ts  ->
          match remaining with
          | [] -> (env, (deps_stack, ts))
          | uu____858 ->
              let deps_stack1 = env :: deps_stack in
              let push_kind =
                let uu____865 = FStar_Options.lax () in
                if uu____865 then LaxCheck else FullCheck in
              let env1 =
                let uu____872 = set_check_kind env push_kind in
                push uu____872 "typecheck_modul" in
              ((let uu____878 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____878 FStar_Pervasives.ignore);
               (let uu____879 = tc_one_file remaining env1 in
                match uu____879 with
                | ((intf,impl),env2,remaining1) ->
                    let uu____932 =
                      let intf_t =
                        match intf with
                        | FStar_Pervasives_Native.Some intf1 ->
                            let uu____945 =
                              FStar_Util.get_file_last_modification_time
                                intf1 in
                            FStar_Pervasives_Native.Some uu____945
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None in
                      let impl_t =
                        FStar_Util.get_file_last_modification_time impl in
                      (intf_t, impl_t) in
                    (match uu____932 with
                     | (intf_t,impl_t) ->
                         tc_deps deps_stack1 env2 remaining1
                           ((intf, impl, intf_t, impl_t) :: ts))))
let update_deps:
  Prims.string ->
    env_t ->
      (deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2 ->
        (env_t,(deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    fun env  ->
      fun uu____1002  ->
        match uu____1002 with
        | (stk,ts) ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt = FStar_Util.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____1065,uu____1066) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1175 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____1203 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____1278::ts3 ->
                    (pop env1 "";
                     (let uu____1319 =
                        let uu____1326 = FStar_List.hd stack in
                        let uu____1327 = FStar_List.tl stack in
                        (uu____1326, uu____1327) in
                      match uu____1319 with
                      | (env2,stack1) -> pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____1392 = ts_elt in
                  (match uu____1392 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____1427 = match_dep depnames intf impl in
                       (match uu____1427 with
                        | (b,depnames') ->
                            let uu____1450 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____1450
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps good_stack env1 depnames good_ts
                            else
                              (let uu____1467 =
                                 let uu____1474 = FStar_List.hd st in
                                 let uu____1475 = FStar_List.tl st in
                                 (uu____1474, uu____1475) in
                               match uu____1467 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps good_stack env' depnames good_ts in
            let uu____1520 = deps_of_our_file filename in
            (match uu____1520 with
             | (filenames,uu____1538) ->
                 iterate filenames (FStar_List.rev_append stk []) env
                   (FStar_List.rev_append ts []) [] [])
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___228_1586  ->
    match uu___228_1586 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1590 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1590
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1592 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1595 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1613 -> true
    | uu____1618 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1634 -> uu____1634
let js_fail: 'Auu____1645 . Prims.string -> FStar_Util.json -> 'Auu____1645 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___229_1657  ->
    match uu___229_1657 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___230_1663  ->
    match uu___230_1663 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____1672 .
    (FStar_Util.json -> 'Auu____1672) ->
      FStar_Util.json -> 'Auu____1672 Prims.list
  =
  fun k  ->
    fun uu___231_1685  ->
      match uu___231_1685 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___232_1703  ->
    match uu___232_1703 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1728 = js_str s in
    match uu____1728 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1729 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1734 = js_str s in
    match uu____1734 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____1735 -> js_fail "reduction rule" s
type completion_context =
  | CKCode
  | CKOption of Prims.bool
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_CKCode: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____1752 -> false
let uu___is_CKOption: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____1758 -> false
let __proj__CKOption__item___0: completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____1776 -> false
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
        let uu____1806 = js_str k1 in
        (match uu____1806 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____1807 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____1812 -> false
let uu___is_LKModule: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____1817 -> false
let uu___is_LKOption: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____1822 -> false
let uu___is_LKCode: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____1827 -> false
let js_optional_lookup_context:
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____1837 = js_str k1 in
        (match uu____1837 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____1838 ->
             js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type position =
  (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
  FStar_Pervasives_Native.tuple5
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
  | MissingCurrentModule
  | ProtocolViolation of Prims.string[@@deriving show]
and query = {
  qq: query';
  qid: Prims.string;}[@@deriving show]
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1915 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1920 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1925 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1930 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1946 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1994 -> false
let __proj__AutoComplete__item___0:
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2032 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2090 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2128 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_MissingCurrentModule: query' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingCurrentModule  -> true
    | uu____2141 -> false
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2147 -> false
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
  fun uu___233_2171  ->
    match uu___233_2171 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push uu____2172 -> false
    | MissingCurrentModule  -> false
    | ProtocolViolation uu____2183 -> false
    | AutoComplete uu____2184 -> true
    | Lookup uu____2189 -> true
    | Compute uu____2202 -> true
    | Search uu____2211 -> true
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
    | InvalidQuery uu____2221 -> true
    | uu____2222 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2230 -> uu____2230
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol[@@deriving show]
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2235 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2240 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2245 -> false
let try_assoc:
  'Auu____2254 'Auu____2255 .
    'Auu____2255 ->
      ('Auu____2255,'Auu____2254) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2254 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2278 =
        FStar_Util.try_find
          (fun uu____2292  ->
             match uu____2292 with | (k,uu____2298) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2278
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2315 =
          let uu____2316 =
            let uu____2317 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2317 in
          ProtocolViolation uu____2316 in
        { qq = uu____2315; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2344 = try_assoc key a in
      match uu____2344 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2348 =
            let uu____2349 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2349 in
          FStar_Exn.raise uu____2348 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2364 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2364 js_str in
    try
      let query =
        let uu____2373 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2373 js_str in
      let args =
        let uu____2381 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2381 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2398 = try_assoc k args in
        match uu____2398 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2406 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____2407 =
              let uu____2418 =
                let uu____2419 = arg "kind" in
                FStar_All.pipe_right uu____2419 js_pushkind in
              let uu____2420 =
                let uu____2421 = arg "code" in
                FStar_All.pipe_right uu____2421 js_str in
              let uu____2422 =
                let uu____2423 = arg "line" in
                FStar_All.pipe_right uu____2423 js_int in
              let uu____2424 =
                let uu____2425 = arg "column" in
                FStar_All.pipe_right uu____2425 js_int in
              (uu____2418, uu____2420, uu____2422, uu____2424,
                (query = "peek")) in
            Push uu____2407
        | "push" ->
            let uu____2426 =
              let uu____2437 =
                let uu____2438 = arg "kind" in
                FStar_All.pipe_right uu____2438 js_pushkind in
              let uu____2439 =
                let uu____2440 = arg "code" in
                FStar_All.pipe_right uu____2440 js_str in
              let uu____2441 =
                let uu____2442 = arg "line" in
                FStar_All.pipe_right uu____2442 js_int in
              let uu____2443 =
                let uu____2444 = arg "column" in
                FStar_All.pipe_right uu____2444 js_int in
              (uu____2437, uu____2439, uu____2441, uu____2443,
                (query = "peek")) in
            Push uu____2426
        | "autocomplete" ->
            let uu____2445 =
              let uu____2450 =
                let uu____2451 = arg "partial-symbol" in
                FStar_All.pipe_right uu____2451 js_str in
              let uu____2452 =
                let uu____2453 = try_arg "context" in
                FStar_All.pipe_right uu____2453
                  js_optional_completion_context in
              (uu____2450, uu____2452) in
            AutoComplete uu____2445
        | "lookup" ->
            let uu____2458 =
              let uu____2471 =
                let uu____2472 = arg "symbol" in
                FStar_All.pipe_right uu____2472 js_str in
              let uu____2473 =
                let uu____2474 = try_arg "context" in
                FStar_All.pipe_right uu____2474 js_optional_lookup_context in
              let uu____2479 =
                let uu____2488 =
                  let uu____2497 = try_arg "location" in
                  FStar_All.pipe_right uu____2497
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2488
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2555 =
                          let uu____2556 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2556 js_str in
                        let uu____2557 =
                          let uu____2558 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2558 js_int in
                        let uu____2559 =
                          let uu____2560 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2560 js_int in
                        (uu____2555, uu____2557, uu____2559))) in
              let uu____2561 =
                let uu____2564 = arg "requested-info" in
                FStar_All.pipe_right uu____2564 (js_list js_str) in
              (uu____2471, uu____2473, uu____2479, uu____2561) in
            Lookup uu____2458
        | "compute" ->
            let uu____2577 =
              let uu____2586 =
                let uu____2587 = arg "term" in
                FStar_All.pipe_right uu____2587 js_str in
              let uu____2588 =
                let uu____2593 = try_arg "rules" in
                FStar_All.pipe_right uu____2593
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2586, uu____2588) in
            Compute uu____2577
        | "search" ->
            let uu____2608 =
              let uu____2609 = arg "terms" in
              FStar_All.pipe_right uu____2609 js_str in
            Search uu____2608
        | uu____2610 ->
            let uu____2611 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____2611 in
      { qq = uu____2406; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____2625 = FStar_Util.read_line stream in
      match uu____2625 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____2629 = FStar_Util.json_of_string line in
          (match uu____2629 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let json_of_opt:
  'Auu____2645 .
    ('Auu____2645 -> FStar_Util.json) ->
      'Auu____2645 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____2663 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____2663
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____2670 =
      let uu____2673 =
        let uu____2674 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____2674 in
      let uu____2675 =
        let uu____2678 =
          let uu____2679 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____2679 in
        [uu____2678] in
      uu____2673 :: uu____2675 in
    FStar_Util.JsonList uu____2670
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____2692 =
          let uu____2699 =
            let uu____2706 =
              let uu____2711 = json_of_pos b in ("beg", uu____2711) in
            let uu____2712 =
              let uu____2719 =
                let uu____2724 = json_of_pos e in ("end", uu____2724) in
              [uu____2719] in
            uu____2706 :: uu____2712 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____2699 in
        FStar_Util.JsonAssoc uu____2692
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2745 = FStar_Range.file_of_use_range r in
    let uu____2746 = FStar_Range.start_of_use_range r in
    let uu____2747 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____2745 uu____2746 uu____2747
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____2752 = FStar_Range.file_of_range r in
    let uu____2753 = FStar_Range.start_of_range r in
    let uu____2754 = FStar_Range.end_of_range r in
    json_of_range_fields uu____2752 uu____2753 uu____2754
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
    let uu____2763 =
      let uu____2770 =
        let uu____2777 =
          let uu____2784 =
            let uu____2789 =
              let uu____2790 =
                let uu____2793 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____2799 = json_of_use_range r in [uu____2799] in
                let uu____2800 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____2806 = json_of_def_range r in [uu____2806]
                  | uu____2807 -> [] in
                FStar_List.append uu____2793 uu____2800 in
              FStar_Util.JsonList uu____2790 in
            ("ranges", uu____2789) in
          [uu____2784] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____2777 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____2770 in
    FStar_Util.JsonAssoc uu____2763
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
    let uu____2965 =
      let uu____2972 =
        let uu____2977 = json_of_opt json_of_def_range lr.slr_def_range in
        ("defined-at", uu____2977) in
      let uu____2978 =
        let uu____2985 =
          let uu____2990 =
            json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42) lr.slr_typ in
          ("type", uu____2990) in
        let uu____2991 =
          let uu____2998 =
            let uu____3003 =
              json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43) lr.slr_doc in
            ("documentation", uu____3003) in
          let uu____3004 =
            let uu____3011 =
              let uu____3016 =
                json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44)
                  lr.slr_def in
              ("definition", uu____3016) in
            [uu____3011] in
          uu____2998 :: uu____3004 in
        uu____2985 :: uu____2991 in
      uu____2972 :: uu____2978 in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____2965
let alist_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3049 =
      FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_46  -> FStar_Util.JsonList _0_46) uu____3049 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet
  | OptReset
  | OptReadOnly[@@deriving show]
let uu___is_OptSet: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3070 -> false
let uu___is_OptReset: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3075 -> false
let uu___is_OptReadOnly: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3080 -> false
let string_of_option_permission_level:
  fstar_option_permission_level -> Prims.string =
  fun uu___234_3084  ->
    match uu___234_3084 with
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
  fun uu___235_3260  ->
    match uu___235_3260 with
    | FStar_Options.Const uu____3261 -> "flag"
    | FStar_Options.IntStr uu____3262 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3263 -> "path"
    | FStar_Options.SimpleStr uu____3264 -> "string"
    | FStar_Options.EnumStr uu____3265 -> "enum"
    | FStar_Options.OpenEnumStr uu____3268 -> "open enum"
    | FStar_Options.PostProcessed (uu____3275,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3283,typ) ->
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
        | FStar_Options.Const uu____3319 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3332,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3340,elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____3346 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____3346
let rec json_of_fstar_option_value:
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___236_3352  ->
    match uu___236_3352 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3360 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____3360
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let alist_of_fstar_option:
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____3373 =
      let uu____3380 =
        let uu____3387 =
          let uu____3392 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3392) in
        let uu____3393 =
          let uu____3400 =
            let uu____3405 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3405) in
          let uu____3406 =
            let uu____3413 =
              let uu____3418 =
                json_of_opt (fun _0_47  -> FStar_Util.JsonStr _0_47)
                  opt.opt_documentation in
              ("documentation", uu____3418) in
            let uu____3419 =
              let uu____3426 =
                let uu____3431 =
                  let uu____3432 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____3432 in
                ("type", uu____3431) in
              [uu____3426;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____3413 :: uu____3419 in
          uu____3400 :: uu____3406 in
        uu____3387 :: uu____3393 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3380 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3373
let json_of_fstar_option: fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____3469 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____3469
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3481 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3481);
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
  fun uu____3543  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3546 =
        FStar_List.map (fun _0_48  -> FStar_Util.JsonStr _0_48)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3546 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: alist_of_protocol_info))
let sig_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name in
      let uu____3562 = FStar_Options.desc_of_opt_type typ in
      match uu____3562 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
let fstar_options_list_cache: fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____3571 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3600  ->
            match uu____3600 with
            | (_shortname,name,typ,doc1) ->
                let uu____3615 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____3615
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____3627 = sig_of_fstar_option name typ in
                        let uu____3628 = snippets_of_fstar_option name typ in
                        let uu____3631 =
                          let uu____3632 = FStar_Options.settable name in
                          if uu____3632
                          then OptSet
                          else
                            (let uu____3634 = FStar_Options.resettable name in
                             if uu____3634 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____3627;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____3628;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____3631
                        })))) in
  FStar_All.pipe_right uu____3571
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
    let uu___248_3659 = opt in
    let uu____3660 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___248_3659.opt_name);
      opt_sig = (uu___248_3659.opt_sig);
      opt_value = uu____3660;
      opt_default = (uu___248_3659.opt_default);
      opt_type = (uu___248_3659.opt_type);
      opt_snippets = (uu___248_3659.opt_snippets);
      opt_documentation = (uu___248_3659.opt_documentation);
      opt_permission_level = (uu___248_3659.opt_permission_level)
    }
let current_fstar_options:
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____3672 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____3672
let trim_option_name:
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____3688 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____3688)
    else ("", opt_name)
type repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_deps: (deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2;
  repl_curmod: modul_t;
  repl_env: env_t;
  repl_stdin: FStar_Util.stream_reader;
  repl_names: FStar_Interactive_CompletionTable.table;}[@@deriving show]
let __proj__Mkrepl_state__item__repl_line: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_line
let __proj__Mkrepl_state__item__repl_column: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_column
let __proj__Mkrepl_state__item__repl_fname: repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_fname
let __proj__Mkrepl_state__item__repl_deps:
  repl_state -> (deps_stack_t,m_timestamps) FStar_Pervasives_Native.tuple2 =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_deps
let __proj__Mkrepl_state__item__repl_curmod: repl_state -> modul_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_curmod
let __proj__Mkrepl_state__item__repl_env: repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_env
let __proj__Mkrepl_state__item__repl_stdin:
  repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_stdin
let __proj__Mkrepl_state__item__repl_names:
  repl_state -> FStar_Interactive_CompletionTable.table =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_names
let repl_stack: repl_state Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let repl_stack_empty: Prims.unit -> Prims.bool =
  fun uu____3878  ->
    let uu____3879 = FStar_ST.op_Bang repl_stack in
    match uu____3879 with | [] -> true | uu____3900 -> false
let pop_repl:
  'Auu____3907 .
    ('Auu____3907,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
      -> repl_state
  =
  fun env  ->
    let uu____3920 = FStar_ST.op_Bang repl_stack in
    match uu____3920 with
    | [] -> failwith "Too many pops"
    | st'::stack ->
        (pop env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         (let uu____3966 = repl_stack_empty () in
          if uu____3966 then cleanup st'.repl_env else ());
         st')
let push_repl:
  push_kind ->
    repl_state ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun push_kind  ->
    fun st  ->
      (let uu____3981 =
         let uu____3984 = FStar_ST.op_Bang repl_stack in st :: uu____3984 in
       FStar_ST.op_Colon_Equals repl_stack uu____3981);
      (let uu____4023 = set_check_kind st.repl_env push_kind in
       push uu____4023 "")
let json_of_repl_state: repl_state -> FStar_Util.json =
  fun st  ->
    let uu____4032 =
      let uu____4039 =
        let uu____4044 =
          let uu____4045 =
            FStar_List.map
              (fun uu____4065  ->
                 match uu____4065 with
                 | (uu____4078,fstname,uu____4080,uu____4081) ->
                     FStar_Util.JsonStr fstname)
              (FStar_Pervasives_Native.snd st.repl_deps) in
          FStar_Util.JsonList uu____4045 in
        ("loaded-dependencies", uu____4044) in
      let uu____4090 =
        let uu____4097 =
          let uu____4102 =
            let uu____4103 =
              let uu____4106 =
                current_fstar_options (fun uu____4111  -> true) in
              FStar_List.map json_of_fstar_option uu____4106 in
            FStar_Util.JsonList uu____4103 in
          ("options", uu____4102) in
        [uu____4097] in
      uu____4039 :: uu____4090 in
    FStar_Util.JsonAssoc uu____4032
let with_printed_effect_args:
  'Auu____4128 . (Prims.unit -> 'Auu____4128) -> 'Auu____4128 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4140  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4151  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4157  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____4164 'Auu____4165 .
    'Auu____4165 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4164,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____4196 'Auu____4197 .
    'Auu____4197 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4197,'Auu____4196) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____4226 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4226) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4243 =
      let uu____4248 = json_of_repl_state st in (QueryOK, uu____4248) in
    (uu____4243, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____4265 'Auu____4266 .
    'Auu____4266 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4266,'Auu____4265) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_missing_current_module:
  'Auu____4305 'Auu____4306 'Auu____4307 .
    'Auu____4307 ->
      'Auu____4306 ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4307,'Auu____4305) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr "Current module unset")),
        (FStar_Util.Inl st))
let run_pop:
  'Auu____4340 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4340) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4357 = repl_stack_empty () in
    if uu____4357
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let uu____4379 =
         let uu____4384 = pop_repl st.repl_env in FStar_Util.Inl uu____4384 in
       ((QueryOK, FStar_Util.JsonNull), uu____4379))
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
    match projectee with | NTAlias _0 -> true | uu____4434 -> false
let __proj__NTAlias__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____4470 -> false
let __proj__NTOpen__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____4500 -> false
let __proj__NTInclude__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____4526 -> false
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
              let uu____4566 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id) [] uu____4566
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____4575 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____4575
            else table
        | NTInclude (host,included) ->
            let uu____4579 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____4581 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____4579 uu____4581
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____4589) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____4591) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____4597,uu____4598) -> lids
              | uu____4603 -> [] in
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
              let uu____4633 = FStar_Syntax_Syntax.mod_name md in
              uu____4633.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let fresh_name_tracking_hooks:
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____4652  ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____4664 =
        let uu____4667 = FStar_ST.op_Bang events in evt :: uu____4667 in
      FStar_ST.op_Colon_Equals events uu____4664 in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____4760 =
                 let uu____4761 =
                   let uu____4766 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____4766, op) in
                 NTOpen uu____4761 in
               push_event uu____4760);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____4772 =
                 let uu____4773 =
                   let uu____4778 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____4778, ns) in
                 NTInclude uu____4773 in
               push_event uu____4772);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____4786 =
                   let uu____4787 =
                     let uu____4794 = FStar_ToSyntax_Env.current_module dsenv in
                     (uu____4794, x, l) in
                   NTAlias uu____4787 in
                 push_event uu____4786)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____4799  -> fun s  -> push_event (NTBinding s))
      })
let track_name_changes:
  env_t ->
    (env_t,env_t ->
             (env_t,name_tracking_event Prims.list)
               FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4816  ->
    match uu____4816 with
    | (dsenv,tcenv) ->
        let uu____4843 =
          let uu____4848 = FStar_ToSyntax_Env.ds_hooks dsenv in
          let uu____4849 = FStar_TypeChecker_Env.tc_hooks tcenv in
          (uu____4848, uu____4849) in
        (match uu____4843 with
         | (dsenv_old_hooks,tcenv_old_hooks) ->
             let uu____4864 = fresh_name_tracking_hooks () in
             (match uu____4864 with
              | (events,dsenv_new_hooks,tcenv_new_hooks) ->
                  let uu____4898 =
                    let uu____4903 =
                      FStar_ToSyntax_Env.set_ds_hooks dsenv dsenv_new_hooks in
                    let uu____4904 =
                      FStar_TypeChecker_Env.set_tc_hooks tcenv
                        tcenv_new_hooks in
                    (uu____4903, uu____4904) in
                  (uu____4898,
                    ((fun uu____4930  ->
                        match uu____4930 with
                        | (dsenv1,tcenv1) ->
                            let uu____4947 =
                              let uu____4952 =
                                FStar_ToSyntax_Env.set_ds_hooks dsenv1
                                  dsenv_old_hooks in
                              let uu____4953 =
                                FStar_TypeChecker_Env.set_tc_hooks tcenv1
                                  tcenv_old_hooks in
                              (uu____4952, uu____4953) in
                            let uu____4954 =
                              let uu____4957 = FStar_ST.op_Bang events in
                              FStar_List.rev uu____4957 in
                            (uu____4947, uu____4954))))))
let run_push:
  'Auu____5012 .
    repl_state ->
      push_kind ->
        Prims.string ->
          Prims.int ->
            Prims.int ->
              Prims.bool ->
                ((query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2,(repl_state,'Auu____5012)
                                                    FStar_Util.either)
                  FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun kind  ->
      fun text1  ->
        fun line  ->
          fun column  ->
            fun peek_only  ->
              let env = push_repl kind st in
              let uu____5054 = track_name_changes env in
              match uu____5054 with
              | (env1,finish_name_tracking) ->
                  let uu____5097 =
                    let uu____5110 = repl_stack_empty () in
                    if uu____5110
                    then
                      let uu____5123 =
                        update_deps st.repl_fname env1 st.repl_deps in
                      (true, uu____5123)
                    else (false, (env1, (st.repl_deps))) in
                  (match uu____5097 with
                   | (restore_cmd_line_options1,(env2,deps)) ->
                       (if restore_cmd_line_options1
                        then
                          (let uu____5185 =
                             FStar_Options.restore_cmd_line_options false in
                           FStar_All.pipe_right uu____5185
                             FStar_Pervasives.ignore)
                        else ();
                        (let frag =
                           {
                             FStar_Parser_ParseIt.frag_text = text1;
                             FStar_Parser_ParseIt.frag_line = line;
                             FStar_Parser_ParseIt.frag_col = column
                           } in
                         let res =
                           check_frag env2 st.repl_curmod (frag, false) in
                         let errors =
                           let uu____5206 = FStar_Errors.report_all () in
                           FStar_All.pipe_right uu____5206
                             (FStar_List.map json_of_issue) in
                         FStar_Errors.clear ();
                         (let st' =
                            let uu___249_5215 = st in
                            {
                              repl_line = line;
                              repl_column = column;
                              repl_fname = (uu___249_5215.repl_fname);
                              repl_deps = deps;
                              repl_curmod = (uu___249_5215.repl_curmod);
                              repl_env = (uu___249_5215.repl_env);
                              repl_stdin = (uu___249_5215.repl_stdin);
                              repl_names = (uu___249_5215.repl_names)
                            } in
                          match res with
                          | FStar_Pervasives_Native.Some (curmod,env3,nerrs)
                              when
                              (nerrs = (Prims.parse_int "0")) &&
                                (peek_only = false)
                              ->
                              let uu____5255 = finish_name_tracking env3 in
                              (match uu____5255 with
                               | (env4,name_events) ->
                                   let uu____5280 =
                                     let uu____5285 =
                                       let uu___250_5286 = st' in
                                       let uu____5287 =
                                         commit_name_tracking curmod
                                           st'.repl_names name_events in
                                       {
                                         repl_line =
                                           (uu___250_5286.repl_line);
                                         repl_column =
                                           (uu___250_5286.repl_column);
                                         repl_fname =
                                           (uu___250_5286.repl_fname);
                                         repl_deps =
                                           (uu___250_5286.repl_deps);
                                         repl_curmod = curmod;
                                         repl_env = env4;
                                         repl_stdin =
                                           (uu___250_5286.repl_stdin);
                                         repl_names = uu____5287
                                       } in
                                     FStar_Util.Inl uu____5285 in
                                   ((QueryOK, (FStar_Util.JsonList errors)),
                                     uu____5280))
                          | uu____5296 ->
                              let uu____5311 = finish_name_tracking env2 in
                              (match uu____5311 with
                               | (env3,uu____5331) ->
                                   let uu____5336 =
                                     run_pop
                                       (let uu___251_5350 = st' in
                                        {
                                          repl_line =
                                            (uu___251_5350.repl_line);
                                          repl_column =
                                            (uu___251_5350.repl_column);
                                          repl_fname =
                                            (uu___251_5350.repl_fname);
                                          repl_deps =
                                            (uu___251_5350.repl_deps);
                                          repl_curmod =
                                            (uu___251_5350.repl_curmod);
                                          repl_env = env3;
                                          repl_stdin =
                                            (uu___251_5350.repl_stdin);
                                          repl_names =
                                            (uu___251_5350.repl_names)
                                        }) in
                                   (match uu____5336 with
                                    | (uu____5363,st'') ->
                                        let status =
                                          if peek_only
                                          then QueryOK
                                          else QueryNOK in
                                        ((status,
                                           (FStar_Util.JsonList errors)),
                                          st'')))))))
let run_symbol_lookup:
  repl_state ->
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
          let uu____5441 = st.repl_env in
          match uu____5441 with
          | (dsenv,tcenv) ->
              let info_of_lid_str lid_str =
                let lid =
                  let uu____5475 =
                    FStar_List.map FStar_Ident.id_of_text
                      (FStar_Util.split lid_str ".") in
                  FStar_Ident.lid_of_ids uu____5475 in
                let lid1 =
                  let uu____5479 =
                    FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                      lid in
                  FStar_All.pipe_left (FStar_Util.dflt lid) uu____5479 in
                let uu____5484 =
                  FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
                FStar_All.pipe_right uu____5484
                  (FStar_Util.map_option
                     (fun uu____5539  ->
                        match uu____5539 with
                        | ((uu____5558,typ),r) ->
                            ((FStar_Util.Inr lid1), typ, r))) in
              let docs_of_lid lid =
                let uu____5575 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
                FStar_All.pipe_right uu____5575
                  (FStar_Util.map_option FStar_Pervasives_Native.fst) in
              let def_of_lid lid =
                let uu____5604 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
                FStar_Util.bind_opt uu____5604
                  (fun uu___237_5648  ->
                     match uu___237_5648 with
                     | (FStar_Util.Inr (se,uu____5670),uu____5671) ->
                         let uu____5700 = sigelt_to_string se in
                         FStar_Pervasives_Native.Some uu____5700
                     | uu____5701 -> FStar_Pervasives_Native.None) in
              let info_at_pos_opt =
                FStar_Util.bind_opt pos_opt
                  (fun uu____5753  ->
                     match uu____5753 with
                     | (file,row,col) ->
                         FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
              let info_opt =
                match info_at_pos_opt with
                | FStar_Pervasives_Native.Some uu____5800 -> info_at_pos_opt
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
                        let uu____5928 = term_to_string tcenv typ in
                        FStar_Pervasives_Native.Some uu____5928
                      else FStar_Pervasives_Native.None in
                    let doc_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "documentation" requested_info ->
                          docs_of_lid lid
                      | uu____5936 -> FStar_Pervasives_Native.None in
                    let def_str =
                      match name_or_lid with
                      | FStar_Util.Inr lid when
                          FStar_List.mem "definition" requested_info ->
                          def_of_lid lid
                      | uu____5947 -> FStar_Pervasives_Native.None in
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
                    let uu____5959 =
                      let uu____5970 = alist_of_symbol_lookup_result result in
                      ("symbol", uu____5970) in
                    FStar_Pervasives_Native.Some uu____5959 in
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
    let uu____6076 = trim_option_name opt_name in
    match uu____6076 with
    | (uu____6095,trimmed_name) ->
        let uu____6097 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____6097 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____6125 =
               let uu____6136 =
                 let uu____6143 = update_option opt in
                 alist_of_fstar_option uu____6143 in
               ("option", uu____6136) in
             FStar_Util.Inr uu____6125)
let run_module_lookup:
  repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                    FStar_Pervasives_Native.tuple2 Prims.list)
                      FStar_Pervasives_Native.tuple2)
        FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      let query = FStar_Util.split symbol "." in
      let uu____6185 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____6185 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____6213 =
            let uu____6224 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____6224) in
          FStar_Util.Inr uu____6213
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____6248 =
            let uu____6259 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____6259) in
          FStar_Util.Inr uu____6248
let run_code_lookup:
  repl_state ->
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
          let uu____6332 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____6332 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6392 ->
              let uu____6403 = run_module_lookup st symbol in
              (match uu____6403 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let run_lookup':
  repl_state ->
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
  'Auu____6564 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6564) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____6617 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____6617 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter:
  'Auu____6703 .
    ('Auu____6703,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____6703,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___238_6717  ->
    match uu___238_6717 with
    | (uu____6722,FStar_Interactive_CompletionTable.Namespace uu____6723) ->
        FStar_Pervasives_Native.None
    | (uu____6728,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____6729;
         FStar_Interactive_CompletionTable.mod_path = uu____6730;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____6737 =
          let uu____6742 =
            let uu____6743 =
              let uu___252_6744 = md in
              let uu____6745 =
                let uu____6746 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.strcat uu____6746 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____6745;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___252_6744.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___252_6744.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____6743 in
          (pth, uu____6742) in
        FStar_Pervasives_Native.Some uu____6737
let run_code_autocomplete:
  'Auu____6757 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6757) FStar_Util.either)
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
  'Auu____6812 'Auu____6813 'Auu____6814 .
    repl_state ->
      Prims.string ->
        'Auu____6814 ->
          'Auu____6813 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____6812) FStar_Util.either)
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
              (fun _0_49  -> FStar_Pervasives_Native.Some _0_49) in
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
        let uu____6878 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only") in
        match uu____6878 with
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
  'Auu____6910 'Auu____6911 .
    'Auu____6911 ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____6911,'Auu____6910) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____6936 = trim_option_name search_term in
        match uu____6936 with
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
        | (uu____6987,uu____6988) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete:
  'Auu____7005 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7005) FStar_Util.either)
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
  'Auu____7041 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7041) FStar_Util.either)
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
                ((uu____7168,{ FStar_Syntax_Syntax.lbname = uu____7169;
                               FStar_Syntax_Syntax.lbunivs = univs1;
                               FStar_Syntax_Syntax.lbtyp = uu____7171;
                               FStar_Syntax_Syntax.lbeff = uu____7172;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____7174);
              FStar_Syntax_Syntax.sigrng = uu____7175;
              FStar_Syntax_Syntax.sigquals = uu____7176;
              FStar_Syntax_Syntax.sigmeta = uu____7177;
              FStar_Syntax_Syntax.sigattrs = uu____7178;_}::[] ->
              FStar_Pervasives_Native.Some (univs1, def)
          | uu____7217 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____7236 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____7236 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____7260) ->
              FStar_Pervasives_Native.Some decls
          | uu____7305 -> FStar_Pervasives_Native.None in
        let desugar dsenv decls =
          let uu____7337 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
          FStar_Pervasives_Native.snd uu____7337 in
        let typecheck tcenv decls =
          let uu____7355 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____7355 with | (ses,uu____7369,uu____7370) -> ses in
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
             let uu____7398 = st1.repl_env in
             match uu____7398 with
             | (dsenv,tcenv) ->
                 let frag = dummy_let_fragment term in
                 (match st1.repl_curmod with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                  | uu____7410 ->
                      let uu____7411 = parse1 frag in
                      (match uu____7411 with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr "Could not parse this term"))
                       | FStar_Pervasives_Native.Some decls ->
                           let aux uu____7434 =
                             let decls1 = desugar dsenv decls in
                             let ses = typecheck tcenv decls1 in
                             match find_let_body ses with
                             | FStar_Pervasives_Native.None  ->
                                 (QueryNOK,
                                   (FStar_Util.JsonStr
                                      "Typechecking yielded an unexpected term"))
                             | FStar_Pervasives_Native.Some (univs1,def) ->
                                 let uu____7469 =
                                   FStar_Syntax_Subst.open_univ_vars univs1
                                     def in
                                 (match uu____7469 with
                                  | (univs2,def1) ->
                                      let tcenv1 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          tcenv univs2 in
                                      let normalized =
                                        normalize_term1 tcenv1 rules1 def1 in
                                      let uu____7482 =
                                        let uu____7483 =
                                          term_to_string tcenv1 normalized in
                                        FStar_Util.JsonStr uu____7483 in
                                      (QueryOK, uu____7482)) in
                           let uu____7484 = FStar_Options.trace_error () in
                           if uu____7484
                           then aux ()
                           else
                             (try aux ()
                              with
                              | e ->
                                  let uu____7509 =
                                    let uu____7510 =
                                      FStar_Errors.issue_of_exn e in
                                    match uu____7510 with
                                    | FStar_Pervasives_Native.Some issue ->
                                        let uu____7514 =
                                          FStar_Errors.format_issue issue in
                                        FStar_Util.JsonStr uu____7514
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Exn.raise e in
                                  (QueryNOK, uu____7509)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid[@@deriving show]
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}[@@deriving show]
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____7536 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____7550 -> false
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
  fun uu___239_7574  ->
    match uu___239_7574 with
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
    let uu____7742 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____7749 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____7742; sc_fvars = uu____7749 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____7798 = FStar_ST.op_Bang sc.sc_typ in
      match uu____7798 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7823 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7823 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7844,typ),uu____7846) ->
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
      let uu____7890 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7890 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7933 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7933 in
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
          let uu____7976 = sc_typ tcenv sc in term_to_string tcenv uu____7976 in
        let uu____7977 =
          let uu____7984 =
            let uu____7989 =
              let uu____7990 =
                let uu____7991 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____7991.FStar_Ident.str in
              FStar_Util.JsonStr uu____7990 in
            ("lid", uu____7989) in
          [uu____7984; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____7977
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____8011 -> true
    | uu____8012 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____8020 -> uu____8020
let run_search:
  'Auu____8027 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____8027) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let uu____8048 = st.repl_env in
      match uu____8048 with
      | (dsenv,tcenv) ->
          let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
          let st_matches candidate term =
            let found =
              match term.st_term with
              | NameContainsStr str ->
                  FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
              | TypeContainsLid lid ->
                  let uu____8076 = sc_fvars tcenv candidate in
                  FStar_Util.set_mem lid uu____8076 in
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
                  let uu____8100 =
                    let uu____8101 =
                      FStar_Util.format1 "Improperly quoted search term: %s"
                        term1 in
                    InvalidSearch uu____8101 in
                  FStar_Exn.raise uu____8100
                else
                  if beg_quote
                  then
                    (let uu____8103 = strip_quotes term1 in
                     NameContainsStr uu____8103)
                  else
                    (let lid = FStar_Ident.lid_of_str term1 in
                     let uu____8106 =
                       FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                         dsenv lid in
                     match uu____8106 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____8109 =
                           let uu____8110 =
                             FStar_Util.format1 "Unknown identifier: %s"
                               term1 in
                           InvalidSearch uu____8110 in
                         FStar_Exn.raise uu____8109
                     | FStar_Pervasives_Native.Some lid1 ->
                         TypeContainsLid lid1) in
              { st_negate = negate; st_term = parsed } in
            let terms =
              FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
            let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
            FStar_Util.sort_with cmp terms in
          let pprint_one term =
            let uu____8126 =
              match term.st_term with
              | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
              | TypeContainsLid l ->
                  FStar_Util.format1 "%s" l.FStar_Ident.str in
            Prims.strcat (if term.st_negate then "-" else "") uu____8126 in
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
                    let uu____8189 = FStar_List.map pprint_one terms in
                    FStar_Util.concat_l " " uu____8189 in
                  let uu____8192 =
                    let uu____8193 =
                      FStar_Util.format1 "No results found for query [%s]"
                        kwds in
                    InvalidSearch uu____8193 in
                  FStar_Exn.raise uu____8192
              | uu____8198 -> (QueryOK, (FStar_Util.JsonList js))
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
    fun uu___240_8249  ->
      match uu___240_8249 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek1) -> run_push st kind text1 l c peek1
      | AutoComplete (search_term,context) ->
          run_autocomplete st search_term context
      | Lookup (symbol,context,pos_opt,rq_info) ->
          run_lookup st symbol context pos_opt rq_info
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | MissingCurrentModule  -> run_missing_current_module st (Obj.magic ())
      | ProtocolViolation query -> run_protocol_violation st query
let validate_query: repl_state -> query -> query =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push (SyntaxCheck ,uu____8301,uu____8302,uu____8303,false ) ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____8304 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = MissingCurrentModule; qid = (q.qid) }
           | uu____8305 -> q)
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query =
      let uu____8311 = read_interactive_query st.repl_stdin in
      validate_query st uu____8311 in
    let uu____8312 = let uu____8325 = run_query st in uu____8325 query.qq in
    match uu____8312 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____8369 =
      let uu____8372 = FStar_ST.op_Bang issues in e :: uu____8372 in
    FStar_ST.op_Colon_Equals issues uu____8369 in
  let count_errors uu____8442 =
    let uu____8443 =
      let uu____8446 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8446 in
    FStar_List.length uu____8443 in
  let report1 uu____8488 =
    let uu____8489 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8489 in
  let clear1 uu____8527 = FStar_ST.op_Colon_Equals issues [] in
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
             let uu____8582 = get_json () in write_message label1 uu____8582)
  }
let capitalize: Prims.string -> Prims.string =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1") in
       let uu____8589 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.strcat (FStar_String.uppercase first) uu____8589)
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
          let uu____8616 = FStar_Util.psmap_empty () in
          let uu____8619 =
            let uu____8622 = FStar_Options.prims () in uu____8622 :: deps in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____8632 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____8632 true) uu____8616
            uu____8619 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____8648  ->
               match uu____8648 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____8660 = capitalize modname in
                        FStar_Util.split uu____8660 "." in
                      let uu____8661 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____8661 mod_path ns_query)) table
          (FStar_List.rev mods)
let initial_range: FStar_Range.range =
  let uu____8666 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____8667 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____8666 uu____8667
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let env = FStar_Universal.init_env () in
     let env1 =
       let uu____8683 =
         FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env)
           initial_range in
       ((FStar_Pervasives_Native.fst env), uu____8683) in
     let uu____8684 = track_name_changes env1 in
     match uu____8684 with
     | (env2,finish_name_tracking) ->
         let env3 = tc_prims env2 in
         let uu____8720 = deps_of_our_file filename in
         (match uu____8720 with
          | (deps,maybe_inferface) ->
              let uu____8739 = tc_deps [] env3 deps [] in
              (match uu____8739 with
               | (env4,repl_deps) ->
                   let env5 =
                     match maybe_inferface with
                     | FStar_Pervasives_Native.None  -> env4
                     | FStar_Pervasives_Native.Some intf ->
                         FStar_Universal.load_interface_decls env4 intf in
                   let uu____8772 = finish_name_tracking env5 in
                   (match uu____8772 with
                    | (env6,name_events) ->
                        (FStar_TypeChecker_Env.toggle_id_info
                           (FStar_Pervasives_Native.snd env6) true;
                         (let initial_names =
                            add_module_completions filename deps
                              FStar_Interactive_CompletionTable.empty in
                          let init_st =
                            let uu____8788 = FStar_Util.open_stdin () in
                            let uu____8789 =
                              commit_name_tracking
                                FStar_Pervasives_Native.None initial_names
                                name_events in
                            {
                              repl_line = (Prims.parse_int "1");
                              repl_column = (Prims.parse_int "0");
                              repl_fname = filename;
                              repl_deps;
                              repl_curmod = FStar_Pervasives_Native.None;
                              repl_env = env6;
                              repl_stdin = uu____8788;
                              repl_names = uu____8789
                            } in
                          let uu____8790 =
                            (FStar_Options.record_hints ()) ||
                              (FStar_Options.use_hints ()) in
                          if uu____8790
                          then
                            let uu____8791 =
                              let uu____8792 = FStar_Options.file_list () in
                              FStar_List.hd uu____8792 in
                            FStar_SMTEncoding_Solver.with_hints_db uu____8791
                              (fun uu____8796  -> go init_st)
                          else go init_st))))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____8804 =
       let uu____8805 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8805 in
     if uu____8804
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____8809 = FStar_Options.trace_error () in
     if uu____8809
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))