open Prims
type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of Prims.string[@@deriving show]
let uu___is_Low: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____9 -> false
let uu___is_Medium: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____14 -> false
let uu___is_High: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____19 -> false
let uu___is_Extreme: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____24 -> false
let uu___is_Other: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____30 -> false
let __proj__Other__item___0: debug_level_t -> Prims.string =
  fun projectee  -> match projectee with | Other _0 -> _0
type option_val =
  | Bool of Prims.bool
  | String of Prims.string
  | Path of Prims.string
  | Int of Prims.int
  | List of option_val Prims.list
  | Unset[@@deriving show]
let uu___is_Bool: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____66 -> false
let __proj__Bool__item___0: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_String: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____80 -> false
let __proj__String__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0
let uu___is_Path: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____94 -> false
let __proj__Path__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0
let uu___is_Int: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____108 -> false
let __proj__Int__item___0: option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_List: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____124 -> false
let __proj__List__item___0: option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0
let uu___is_Unset: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____143 -> false
let mk_bool: Prims.bool -> option_val = fun _0_28  -> Bool _0_28
let mk_string: Prims.string -> option_val = fun _0_29  -> String _0_29
let mk_path: Prims.string -> option_val = fun _0_30  -> Path _0_30
let mk_int: Prims.int -> option_val = fun _0_31  -> Int _0_31
let mk_list: option_val Prims.list -> option_val = fun _0_32  -> List _0_32
type options =
  | Set
  | Reset
  | Restore[@@deriving show]
let uu___is_Set: options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____165 -> false
let uu___is_Reset: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____170 -> false
let uu___is_Restore: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____175 -> false
let __unit_tests__: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let __unit_tests: Prims.unit -> Prims.bool =
  fun uu____188  -> FStar_ST.op_Bang __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____202  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____216  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___48_230  ->
    match uu___48_230 with
    | Bool b -> b
    | uu____232 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___49_236  ->
    match uu___49_236 with
    | Int b -> b
    | uu____238 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___50_242  ->
    match uu___50_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___51_251  ->
    match uu___51_251 with
    | List ts -> ts
    | uu____257 -> failwith "Impos: expected List"
let as_list:
  'Auu____266 .
    (option_val -> 'Auu____266) -> option_val -> 'Auu____266 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____282 = as_list' x in
      FStar_All.pipe_right uu____282 (FStar_List.map as_t)
let as_option:
  'Auu____295 .
    (option_val -> 'Auu____295) ->
      option_val -> 'Auu____295 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___52_308  ->
      match uu___52_308 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____312 = as_t v1 in FStar_Pervasives_Native.Some uu____312
type optionstate = option_val FStar_Util.smap[@@deriving show]
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____331  ->
    let uu____332 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____332
let pop: Prims.unit -> Prims.unit =
  fun uu____356  ->
    let uu____357 = FStar_ST.op_Bang fstar_options in
    match uu____357 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____378::[] -> failwith "TOO MANY POPS!"
    | uu____379::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____404  ->
    let uu____405 =
      let uu____408 =
        let uu____411 = peek () in FStar_Util.smap_copy uu____411 in
      let uu____414 = FStar_ST.op_Bang fstar_options in uu____408 ::
        uu____414 in
    FStar_ST.op_Colon_Equals fstar_options uu____405
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____461 = FStar_ST.op_Bang fstar_options in
    match uu____461 with
    | [] -> failwith "set on empty option stack"
    | uu____482::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____512 = peek () in FStar_Util.smap_add uu____512 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____522  -> match uu____522 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____563 =
      let uu____566 = FStar_ST.op_Bang light_off_files in filename ::
        uu____566 in
    FStar_ST.op_Colon_Equals light_off_files uu____563
let defaults:
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("doc", (Bool false));
  ("dump_module", (List []));
  ("eager_inference", (Bool false));
  ("explicit_deps", (Bool false));
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("fstar_home", Unset);
  ("full_context_dependency", (Bool true));
  ("gen_native_tactics", Unset);
  ("hide_genident_nums", (Bool false));
  ("hide_uvar_nums", (Bool false));
  ("hint_info", (Bool false));
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("include", (List []));
  ("indent", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
  ("lax", (Bool false));
  ("load", (List []));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.parse_int "8")));
  ("max_ifuel", (Int (Prims.parse_int "2")));
  ("min_fuel", (Int (Prims.parse_int "1")));
  ("MLish", (Bool false));
  ("n_cores", (Int (Prims.parse_int "1")));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("no_tactics", (Bool false));
  ("odir", Unset);
  ("prims", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("print_bound_var_types", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("query_stats", (Bool false));
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("show_signatures", (List []));
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("split_cases", (Int (Prims.parse_int "0")));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("unsafe_tactic_exec", (Bool false));
  ("use_native_tactics", Unset);
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("using_facts_from", Unset);
  ("verify", (Bool true));
  ("verify_all", (Bool false));
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false))]
let init: Prims.unit -> Prims.unit =
  fun uu____970  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____986  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1036 =
      let uu____1039 = peek () in FStar_Util.smap_try_find uu____1039 s in
    match uu____1036 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1049 . Prims.string -> (option_val -> 'Auu____1049) -> 'Auu____1049
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1066  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1072  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1078  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1084  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1092  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1100  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1108  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1116  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1122  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1126  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1130  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1136  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1142  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____1146  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____1150  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1156  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1164  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1170  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1176  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1184  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____1190  -> lookup_opt "hide_genident_nums" as_bool
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1194  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1198  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1204  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1210  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1214  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1220  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1226  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1230  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1234  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1238  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1244  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1250  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1254  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1258  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1262  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1266  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1270  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1274  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1278  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1284  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1290  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1296  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1302  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1308  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1314  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1318  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1322  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1326  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1330  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1334  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1338  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1342  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1346  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1352  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_show_signatures: Prims.unit -> Prims.string Prims.list =
  fun uu____1360  -> lookup_opt "show_signatures" (as_list as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1366  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1372  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1378  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1382  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1386  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1390  -> lookup_opt "split_cases" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1394  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1398  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1402  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1406  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1410  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1414  -> lookup_opt "use_hints" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1420  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1426  ->
    let uu____1427 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1427
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1435  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____1445  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1451  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1459  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1465  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1469  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1475  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1481  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1485  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1489  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1493  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1497  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1501  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___53_1505  ->
    match uu___53_1505 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1515 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1520 = get_debug_level () in
    FStar_All.pipe_right uu____1520
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1612  ->
    let uu____1613 =
      let uu____1614 = FStar_ST.op_Bang _version in
      let uu____1625 = FStar_ST.op_Bang _platform in
      let uu____1636 = FStar_ST.op_Bang _compiler in
      let uu____1647 = FStar_ST.op_Bang _date in
      let uu____1658 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1614
        uu____1625 uu____1636 uu____1647 uu____1658 in
    FStar_Util.print_string uu____1613
let display_usage_aux:
  'Auu____1675 'Auu____1676 .
    ('Auu____1676,Prims.string,'Auu____1675 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1723  ->
         match uu____1723 with
         | (uu____1734,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1745 =
                      let uu____1746 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____1746 in
                    FStar_Util.print_string uu____1745
                  else
                    (let uu____1748 =
                       let uu____1749 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____1749 doc in
                     FStar_Util.print_string uu____1748)
              | FStar_Getopt.OneArg (uu____1750,argname) ->
                  if doc = ""
                  then
                    let uu____1756 =
                      let uu____1757 = FStar_Util.colorize_bold flag in
                      let uu____1758 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____1757 uu____1758 in
                    FStar_Util.print_string uu____1756
                  else
                    (let uu____1760 =
                       let uu____1761 = FStar_Util.colorize_bold flag in
                       let uu____1762 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1761
                         uu____1762 doc in
                     FStar_Util.print_string uu____1760))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1787 = o in
    match uu____1787 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1817 =
                let uu____1818 = f () in set_option name uu____1818 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1829 = f x in set_option name uu____1829 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1845 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____1845 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____1866 =
        let uu____1869 = lookup_opt name as_list' in
        FStar_List.append uu____1869 [value] in
      mk_list uu____1866
let accumulate_string:
  'Auu____1882 .
    Prims.string ->
      ('Auu____1882 -> Prims.string) -> 'Auu____1882 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1900 =
          let uu____1901 =
            let uu____1902 = post_processor value in mk_string uu____1902 in
          accumulated_option name uu____1901 in
        set_option name uu____1900
let add_extract_module: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s
let add_extract_namespace: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s
let add_verify_module: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "verify_module" FStar_String.lowercase s
type opt_type =
  | Const of option_val
  | IntStr of Prims.string
  | BoolStr
  | PathStr of Prims.string
  | SimpleStr of Prims.string
  | EnumStr of Prims.string Prims.list
  | OpenEnumStr of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2
  | PostProcessed of (option_val -> option_val,opt_type)
  FStar_Pervasives_Native.tuple2
  | Accumulated of opt_type
  | ReverseAccumulated of opt_type
  | WithSideEffect of (Prims.unit -> Prims.unit,opt_type)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Const: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1984 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____1998 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2011 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2017 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2031 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2047 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2073 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2111 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2143 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2157 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2177 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2211 -> true
    | uu____2212 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2220 -> uu____2220
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2237 ->
              let uu____2238 = FStar_Util.int_of_string str_val in
              mk_int uu____2238
          | BoolStr  ->
              let uu____2239 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2239
          | PathStr uu____2242 -> mk_path str_val
          | SimpleStr uu____2243 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2248 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2261 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2261
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect,elem_spec) ->
              (side_effect (); parse_opt_val opt_name elem_spec str_val)
        with
        | InvalidArgument opt_name1 ->
            let uu____2278 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2278
let rec desc_of_opt_type:
  opt_type -> Prims.string FStar_Pervasives_Native.option =
  fun typ  ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some
        (Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]")) in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____2312,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2320,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2341 = desc_of_opt_type typ in
      match uu____2341 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2347  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2361 =
      let uu____2362 = as_string s in FStar_String.lowercase uu____2362 in
    mk_string uu____2361
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2379  ->
    let uu____2390 =
      let uu____2401 =
        let uu____2412 =
          let uu____2421 = let uu____2422 = mk_bool true in Const uu____2422 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2421,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2423 =
          let uu____2434 =
            let uu____2445 =
              let uu____2456 =
                let uu____2467 =
                  let uu____2478 =
                    let uu____2489 =
                      let uu____2498 =
                        let uu____2499 = mk_bool true in Const uu____2499 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2498,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2500 =
                      let uu____2511 =
                        let uu____2520 =
                          let uu____2521 = mk_bool true in Const uu____2521 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2520,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2522 =
                        let uu____2533 =
                          let uu____2542 =
                            let uu____2543 = mk_bool true in Const uu____2543 in
                          (FStar_Getopt.noshort, "doc", uu____2542,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____2544 =
                          let uu____2555 =
                            let uu____2566 =
                              let uu____2575 =
                                let uu____2576 = mk_bool true in
                                Const uu____2576 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____2575,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____2577 =
                              let uu____2588 =
                                let uu____2597 =
                                  let uu____2598 = mk_bool true in
                                  Const uu____2598 in
                                (FStar_Getopt.noshort, "explicit_deps",
                                  uu____2597,
                                  "Do not find dependencies automatically, the user provides them on the command-line") in
                              let uu____2599 =
                                let uu____2610 =
                                  let uu____2619 =
                                    let uu____2620 = mk_bool true in
                                    Const uu____2620 in
                                  (FStar_Getopt.noshort, "extract_all",
                                    uu____2619,
                                    "Discover the complete dependency graph and do not stop at interface boundaries") in
                                let uu____2621 =
                                  let uu____2632 =
                                    let uu____2643 =
                                      let uu____2654 =
                                        let uu____2665 =
                                          let uu____2676 =
                                            let uu____2685 =
                                              let uu____2686 = mk_bool true in
                                              Const uu____2686 in
                                            (FStar_Getopt.noshort,
                                              "hide_genident_nums",
                                              uu____2685,
                                              "Don't print generated identifier numbers") in
                                          let uu____2687 =
                                            let uu____2698 =
                                              let uu____2707 =
                                                let uu____2708 = mk_bool true in
                                                Const uu____2708 in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2707,
                                                "Don't print unification variable numbers") in
                                            let uu____2709 =
                                              let uu____2720 =
                                                let uu____2731 =
                                                  let uu____2740 =
                                                    let uu____2741 =
                                                      mk_bool true in
                                                    Const uu____2741 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2740,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                let uu____2742 =
                                                  let uu____2753 =
                                                    let uu____2762 =
                                                      let uu____2763 =
                                                        mk_bool true in
                                                      Const uu____2763 in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2762,
                                                      "Legacy interactive mode; reads input from stdin") in
                                                  let uu____2764 =
                                                    let uu____2775 =
                                                      let uu____2784 =
                                                        let uu____2785 =
                                                          mk_bool true in
                                                        Const uu____2785 in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2784,
                                                        "JSON-based interactive mode for IDEs") in
                                                    let uu____2786 =
                                                      let uu____2797 =
                                                        let uu____2808 =
                                                          let uu____2817 =
                                                            let uu____2818 =
                                                              mk_bool true in
                                                            Const uu____2818 in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2817,
                                                            "Parses and outputs the files on the command line") in
                                                        let uu____2819 =
                                                          let uu____2830 =
                                                            let uu____2841 =
                                                              let uu____2852
                                                                =
                                                                let uu____2861
                                                                  =
                                                                  let uu____2862
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____2862 in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2861,
                                                                  "Run the lax-type checker only (admit all verification conditions)") in
                                                              let uu____2863
                                                                =
                                                                let uu____2874
                                                                  =
                                                                  let uu____2885
                                                                    =
                                                                    let uu____2894
                                                                    =
                                                                    let uu____2895
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2895 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2894,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                  let uu____2896
                                                                    =
                                                                    let uu____2907
                                                                    =
                                                                    let uu____2916
                                                                    =
                                                                    let uu____2917
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2917 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2916,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____2918
                                                                    =
                                                                    let uu____2929
                                                                    =
                                                                    let uu____2940
                                                                    =
                                                                    let uu____2951
                                                                    =
                                                                    let uu____2962
                                                                    =
                                                                    let uu____2971
                                                                    =
                                                                    let uu____2972
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2972 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2971,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____2973
                                                                    =
                                                                    let uu____2984
                                                                    =
                                                                    let uu____2995
                                                                    =
                                                                    let uu____3004
                                                                    =
                                                                    let uu____3005
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3005 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3004,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3006
                                                                    =
                                                                    let uu____3017
                                                                    =
                                                                    let uu____3028
                                                                    =
                                                                    let uu____3037
                                                                    =
                                                                    let uu____3038
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3038 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3037,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3039
                                                                    =
                                                                    let uu____3050
                                                                    =
                                                                    let uu____3061
                                                                    =
                                                                    let uu____3072
                                                                    =
                                                                    let uu____3081
                                                                    =
                                                                    let uu____3082
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3082 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3081,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3083
                                                                    =
                                                                    let uu____3094
                                                                    =
                                                                    let uu____3103
                                                                    =
                                                                    let uu____3104
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3104 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3103,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3105
                                                                    =
                                                                    let uu____3116
                                                                    =
                                                                    let uu____3125
                                                                    =
                                                                    let uu____3126
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3126 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3125,
                                                                    "Print full names of variables") in
                                                                    let uu____3127
                                                                    =
                                                                    let uu____3138
                                                                    =
                                                                    let uu____3147
                                                                    =
                                                                    let uu____3148
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3148 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3147,
                                                                    "Print implicit arguments") in
                                                                    let uu____3149
                                                                    =
                                                                    let uu____3160
                                                                    =
                                                                    let uu____3169
                                                                    =
                                                                    let uu____3170
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3170 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3169,
                                                                    "Print universes") in
                                                                    let uu____3171
                                                                    =
                                                                    let uu____3182
                                                                    =
                                                                    let uu____3191
                                                                    =
                                                                    let uu____3192
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3192 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3191,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3193
                                                                    =
                                                                    let uu____3204
                                                                    =
                                                                    let uu____3213
                                                                    =
                                                                    let uu____3214
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3214 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3213,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3215
                                                                    =
                                                                    let uu____3226
                                                                    =
                                                                    let uu____3235
                                                                    =
                                                                    let uu____3236
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3236 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3235,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3237
                                                                    =
                                                                    let uu____3248
                                                                    =
                                                                    let uu____3257
                                                                    =
                                                                    let uu____3258
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3258 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3257,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3259
                                                                    =
                                                                    let uu____3270
                                                                    =
                                                                    let uu____3281
                                                                    =
                                                                    let uu____3292
                                                                    =
                                                                    let uu____3301
                                                                    =
                                                                    let uu____3302
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3302 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3301,
                                                                    " ") in
                                                                    let uu____3303
                                                                    =
                                                                    let uu____3314
                                                                    =
                                                                    let uu____3325
                                                                    =
                                                                    let uu____3336
                                                                    =
                                                                    let uu____3347
                                                                    =
                                                                    let uu____3358
                                                                    =
                                                                    let uu____3369
                                                                    =
                                                                    let uu____3378
                                                                    =
                                                                    let uu____3379
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3379 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3378,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3380
                                                                    =
                                                                    let uu____3391
                                                                    =
                                                                    let uu____3400
                                                                    =
                                                                    let uu____3401
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3401 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3400,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3402
                                                                    =
                                                                    let uu____3413
                                                                    =
                                                                    let uu____3422
                                                                    =
                                                                    let uu____3423
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3423 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3422,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3424
                                                                    =
                                                                    let uu____3435
                                                                    =
                                                                    let uu____3444
                                                                    =
                                                                    let uu____3445
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3445 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3444,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3446
                                                                    =
                                                                    let uu____3457
                                                                    =
                                                                    let uu____3466
                                                                    =
                                                                    let uu____3467
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3467 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3466,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this options can have disastrous effects.") in
                                                                    let uu____3468
                                                                    =
                                                                    let uu____3479
                                                                    =
                                                                    let uu____3488
                                                                    =
                                                                    let uu____3489
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3489 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3488,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3490
                                                                    =
                                                                    let uu____3501
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3511 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3510,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3512
                                                                    =
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3543
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3544 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3543,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3545
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3567
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3577 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_all",
                                                                    uu____3576,
                                                                    "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.") in
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3621
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3629 in
                                                                    ((fun
                                                                    uu____3634
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3628) in
                                                                    WithSideEffect
                                                                    uu____3621 in
                                                                    (118,
                                                                    "version",
                                                                    uu____3620,
                                                                    "Display version number") in
                                                                    let uu____3636
                                                                    =
                                                                    let uu____3647
                                                                    =
                                                                    let uu____3656
                                                                    =
                                                                    let uu____3657
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3657 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3656,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____3658
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3680
                                                                    =
                                                                    let uu____3689
                                                                    =
                                                                    let uu____3690
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3690 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3689,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____3691
                                                                    =
                                                                    let uu____3702
                                                                    =
                                                                    let uu____3713
                                                                    =
                                                                    let uu____3724
                                                                    =
                                                                    let uu____3735
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3745
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3745 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3744,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____3746
                                                                    =
                                                                    let uu____3757
                                                                    =
                                                                    let uu____3766
                                                                    =
                                                                    let uu____3767
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3767 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3766,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    let uu____3797
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3797 in
                                                                    ((fun
                                                                    uu____3802
                                                                     ->
                                                                    (
                                                                    let uu____3804
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____3804);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3796) in
                                                                    WithSideEffect
                                                                    uu____3789 in
                                                                    (104,
                                                                    "help",
                                                                    uu____3788,
                                                                    "Display this information") in
                                                                    [uu____3779] in
                                                                    uu____3757
                                                                    ::
                                                                    uu____3768 in
                                                                    uu____3735
                                                                    ::
                                                                    uu____3746 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3724 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3713 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3702 in
                                                                    uu____3680
                                                                    ::
                                                                    uu____3691 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3669 in
                                                                    uu____3647
                                                                    ::
                                                                    uu____3658 in
                                                                    uu____3611
                                                                    ::
                                                                    uu____3636 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3600 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_module",
                                                                    (Accumulated
                                                                    (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "module_name")))),
                                                                    "Name of the module to verify")
                                                                    ::
                                                                    uu____3589 in
                                                                    uu____3567
                                                                    ::
                                                                    uu____3578 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu____3943
                                                                     ->
                                                                    let uu____3944
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    set_option
                                                                    "z3refresh"
                                                                    uu____3944),
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "namespace | fact id")))),
                                                                    "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids")
                                                                    ::
                                                                    uu____3556 in
                                                                    uu____3534
                                                                    ::
                                                                    uu____3545 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3523 in
                                                                    uu____3501
                                                                    ::
                                                                    uu____3512 in
                                                                    uu____3479
                                                                    ::
                                                                    uu____3490 in
                                                                    uu____3457
                                                                    ::
                                                                    uu____3468 in
                                                                    uu____3435
                                                                    ::
                                                                    uu____3446 in
                                                                    uu____3413
                                                                    ::
                                                                    uu____3424 in
                                                                    uu____3391
                                                                    ::
                                                                    uu____3402 in
                                                                    uu____3369
                                                                    ::
                                                                    uu____3380 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3358 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3347 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3336 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3325 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3314 in
                                                                    uu____3292
                                                                    ::
                                                                    uu____3303 in
                                                                    (FStar_Getopt.noshort,
                                                                    "show_signatures",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Show the checked signatures for all top-level symbols in the module")
                                                                    ::
                                                                    uu____3281 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3270 in
                                                                    uu____3248
                                                                    ::
                                                                    uu____3259 in
                                                                    uu____3226
                                                                    ::
                                                                    uu____3237 in
                                                                    uu____3204
                                                                    ::
                                                                    uu____3215 in
                                                                    uu____3182
                                                                    ::
                                                                    uu____3193 in
                                                                    uu____3160
                                                                    ::
                                                                    uu____3171 in
                                                                    uu____3138
                                                                    ::
                                                                    uu____3149 in
                                                                    uu____3116
                                                                    ::
                                                                    uu____3127 in
                                                                    uu____3094
                                                                    ::
                                                                    uu____3105 in
                                                                    uu____3072
                                                                    ::
                                                                    uu____3083 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3061 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3050 in
                                                                    uu____3028
                                                                    ::
                                                                    uu____3039 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3017 in
                                                                    uu____2995
                                                                    ::
                                                                    uu____3006 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2984 in
                                                                    uu____2962
                                                                    ::
                                                                    uu____2973 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2951 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2940 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2929 in
                                                                    uu____2907
                                                                    ::
                                                                    uu____2918 in
                                                                  uu____2885
                                                                    ::
                                                                    uu____2896 in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2874 in
                                                              uu____2852 ::
                                                                uu____2863 in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2841 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2830 in
                                                        uu____2808 ::
                                                          uu____2819 in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2797 in
                                                    uu____2775 :: uu____2786 in
                                                  uu____2753 :: uu____2764 in
                                                uu____2731 :: uu____2742 in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2720 in
                                            uu____2698 :: uu____2709 in
                                          uu____2676 :: uu____2687 in
                                        (FStar_Getopt.noshort,
                                          "gen_native_tactics",
                                          (PathStr "[path]"),
                                          "Compile all user tactics used in the module in <path>")
                                          :: uu____2665 in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____2654 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Only extract modules in the specified namespace")
                                      :: uu____2643 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____2632 in
                                uu____2610 :: uu____2621 in
                              uu____2588 :: uu____2599 in
                            uu____2566 :: uu____2577 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____2555 in
                        uu____2533 :: uu____2544 in
                      uu____2511 :: uu____2522 in
                    uu____2489 :: uu____2500 in
                  (FStar_Getopt.noshort, "dep", (EnumStr ["make"; "graph"]),
                    "Output the transitive closure of the dependency graph in a format suitable for the given tool")
                    :: uu____2478 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2467 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2456 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2445 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"]),
            "Generate code for execution") :: uu____2434 in
        uu____2412 :: uu____2423 in
      (FStar_Getopt.noshort, "admit_except", (SimpleStr "(symbol, id)"),
        "Admit all verification conditions, except those with query label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)'")
        :: uu____2401 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2390
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4505  ->
    let uu____4508 = specs_with_types () in
    FStar_List.map
      (fun uu____4533  ->
         match uu____4533 with
         | (short,long,typ,doc) ->
             let uu____4546 =
               let uu____4557 = arg_spec_of_opt_type long typ in
               (short, long, uu____4557, doc) in
             mk_spec uu____4546) uu____4508
let settable: Prims.string -> Prims.bool =
  fun uu___54_4565  ->
    match uu___54_4565 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "hide_genident_nums" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
    | "hint_file" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "lax" -> true
    | "load" -> true
    | "log_types" -> true
    | "log_queries" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "ugly" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "query_stats" -> true
    | "show_signatures" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "smtencoding.l_arith_repr" -> true
    | "split_cases" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "no_tactics" -> true
    | "using_facts_from" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | uu____4566 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  -> ((settable s) || (s = "z3seed")) || (s = "z3cliopt")
let all_specs: FStar_Getopt.opt Prims.list = specs ()
let all_specs_with_types:
  (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list
  = specs_with_types ()
let settable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4624  ->
          match uu____4624 with
          | (uu____4635,x,uu____4637,uu____4638) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4684  ->
          match uu____4684 with
          | (uu____4695,x,uu____4697,uu____4698) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____4706  ->
    let uu____4707 = specs () in display_usage_aux uu____4707
let fstar_home: Prims.unit -> Prims.string =
  fun uu____4723  ->
    let uu____4724 = get_fstar_home () in
    match uu____4724 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____4730 =
            let uu____4735 = mk_string x1 in ("fstar_home", uu____4735) in
          set_option' uu____4730);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____4744 -> true
    | uu____4745 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____4753 -> uu____4753
let set_options: options -> Prims.string -> FStar_Getopt.parse_cmdline_res =
  fun o  ->
    fun s  ->
      let specs1 =
        match o with
        | Set  -> settable_specs
        | Reset  -> resettable_specs
        | Restore  -> all_specs in
      try
        if s = ""
        then FStar_Getopt.Success
        else
          FStar_Getopt.parse_string specs1
            (fun s1  -> FStar_Exn.raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____4799 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____4799
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4822  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4827 =
             let uu____4830 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4830 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4827) in
    let uu____4869 =
      let uu____4872 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4872 in
    (res, uu____4869)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____4900  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____4929 = specs () in
       FStar_Getopt.parse_cmdline uu____4929 (fun x  -> ()) in
     (let uu____4935 =
        let uu____4940 =
          let uu____4941 = FStar_List.map mk_string old_verify_module in
          List uu____4941 in
        ("verify_module", uu____4940) in
      set_option' uu____4935);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____4950 =
        let uu____4951 =
          let uu____4952 =
            let uu____4953 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____4953 in
          (FStar_String.length f1) - uu____4952 in
        uu____4951 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____4950 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____4958 = get_lax () in
    if uu____4958
    then false
    else
      (let uu____4960 = get_verify_all () in
       if uu____4960
       then true
       else
         (let uu____4962 = get_verify_module () in
          match uu____4962 with
          | [] ->
              let uu____4965 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let uu____4971 = module_name_of_file_name f in
                   uu____4971 = m) uu____4965
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____4979 = module_name_of_file_name fn in should_verify uu____4979
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____4984 = get___temp_no_proj () in
    FStar_List.contains m uu____4984
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____4991 = should_verify m in
    if uu____4991 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____4998  ->
    let uu____4999 = get_no_default_includes () in
    if uu____4999
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5007 =
         let uu____5010 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5010
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5023 =
         let uu____5026 = get_include () in
         FStar_List.append uu____5026 ["."] in
       FStar_List.append uu____5007 uu____5023)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5035 = FStar_Util.is_path_absolute filename in
    if uu____5035
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5042 =
         let uu____5045 = include_path () in FStar_List.rev uu____5045 in
       FStar_Util.find_map uu____5042
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5058  ->
    let uu____5059 = get_prims () in
    match uu____5059 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5063 = find_file filename in
        (match uu____5063 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5067 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5067)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5072  ->
    let uu____5073 = prims () in FStar_Util.basename uu____5073
let pervasives: Prims.unit -> Prims.string =
  fun uu____5077  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5079 = find_file filename in
    match uu____5079 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5083 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5083
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5087  ->
    let uu____5088 = pervasives () in FStar_Util.basename uu____5088
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5092  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5094 = find_file filename in
    match uu____5094 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5098 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5098
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5103 = get_odir () in
    match uu____5103 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5111 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5111 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5119  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5125  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5129  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5135  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5143  ->
    let uu____5144 = get_codegen_lib () in
    FStar_All.pipe_right uu____5144
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5160  -> let uu____5161 = get_debug () in uu____5161 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5176 = get_debug () in
       FStar_All.pipe_right uu____5176 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5186  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5190  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5194  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5198  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5203 = get_dump_module () in
    FStar_All.pipe_right uu____5203 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5211  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____5215  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____5219  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5224 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5224
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5250  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5254  -> true
let hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____5258  -> get_hide_genident_nums ()
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5262  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5266  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5272  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5276  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5280  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5284  ->
    let uu____5285 = get_initial_fuel () in
    let uu____5286 = get_max_fuel () in Prims.min uu____5285 uu____5286
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5290  ->
    let uu____5291 = get_initial_ifuel () in
    let uu____5292 = get_max_ifuel () in Prims.min uu____5291 uu____5292
let interactive: Prims.unit -> Prims.bool =
  fun uu____5296  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5300  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5306  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5310  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5314  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5318  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5322  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5326  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5330  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5334  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5338  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5342  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5346  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5351 = get_no_extract () in
    FStar_All.pipe_right uu____5351 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5359  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5365  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5369  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5373  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5377  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5381  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5385  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5389  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5393  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5397  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5401  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5407  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5411  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5415  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5419  ->
    let uu____5420 = get_smtencoding_nl_arith_repr () in
    uu____5420 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5424  ->
    let uu____5425 = get_smtencoding_nl_arith_repr () in
    uu____5425 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5429  ->
    let uu____5430 = get_smtencoding_nl_arith_repr () in
    uu____5430 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5434  ->
    let uu____5435 = get_smtencoding_l_arith_repr () in uu____5435 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5439  ->
    let uu____5440 = get_smtencoding_l_arith_repr () in
    uu____5440 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____5444  -> get_split_cases ()
let timing: Prims.unit -> Prims.bool = fun uu____5448  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5452  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5456  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5460  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5464  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5468  -> get_use_hints ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5474  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5478  -> get_use_tactics ()
let using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____5486  -> get_using_facts_from ()
let verify_all: Prims.unit -> Prims.bool =
  fun uu____5490  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____5496  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____5500  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____5504  ->
    let uu____5505 = get_smt () in
    match uu____5505 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____5514  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____5518  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____5522  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____5526  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____5530  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____5534  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____5538  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____5545 = no_extract m in Prims.op_Negation uu____5545) &&
      ((extract_all ()) ||
         (let uu____5548 = get_extract_module () in
          match uu____5548 with
          | [] ->
              let uu____5551 = get_extract_namespace () in
              (match uu____5551 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))