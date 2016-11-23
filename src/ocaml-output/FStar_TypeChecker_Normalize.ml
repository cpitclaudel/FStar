
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Primops
| Eager_unfolding
| Inlining
| NoDeltaSteps
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars 
 and steps =
step Prims.list


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iota = (fun _discr_ -> (match (_discr_) with
| Iota (_) -> begin
true
end
| _ -> begin
false
end))


let is_Zeta = (fun _discr_ -> (match (_discr_) with
| Zeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exclude = (fun _discr_ -> (match (_discr_) with
| Exclude (_) -> begin
true
end
| _ -> begin
false
end))


let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))


let is_Primops = (fun _discr_ -> (match (_discr_) with
| Primops (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eager_unfolding = (fun _discr_ -> (match (_discr_) with
| Eager_unfolding (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inlining = (fun _discr_ -> (match (_discr_) with
| Inlining (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoDeltaSteps = (fun _discr_ -> (match (_discr_) with
| NoDeltaSteps (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnfoldUntil = (fun _discr_ -> (match (_discr_) with
| UnfoldUntil (_) -> begin
true
end
| _ -> begin
false
end))


let is_PureSubtermsWithinComputations = (fun _discr_ -> (match (_discr_) with
| PureSubtermsWithinComputations (_) -> begin
true
end
| _ -> begin
false
end))


let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))


let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reify = (fun _discr_ -> (match (_discr_) with
| Reify (_) -> begin
true
end
| _ -> begin
false
end))


let is_CompressUvars = (fun _discr_ -> (match (_discr_) with
| CompressUvars (_) -> begin
true
end
| _ -> begin
false
end))


let ___Exclude____0 = (fun projectee -> (match (projectee) with
| Exclude (_53_11) -> begin
_53_11
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_14) -> begin
_53_14
end))


type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list


let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))


let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))


let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_53_17) -> begin
_53_17
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_20) -> begin
_53_20
end))


let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_23, t, _53_26, _53_28) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_32 -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list}


let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list


type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))


let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))


let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))


let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Steps = (fun _discr_ -> (match (_discr_) with
| Steps (_) -> begin
true
end
| _ -> begin
false
end))


let is_Debug = (fun _discr_ -> (match (_discr_) with
| Debug (_) -> begin
true
end
| _ -> begin
false
end))


let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_53_39) -> begin
_53_39
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_42) -> begin
_53_42
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_45) -> begin
_53_45
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_48) -> begin
_53_48
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_51) -> begin
_53_51
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_54) -> begin
_53_54
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_57) -> begin
_53_57
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_53_60) -> begin
_53_60
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_53_63) -> begin
_53_63
end))


let ___Debug____0 = (fun projectee -> (match (projectee) with
| Debug (_53_66) -> begin
_53_66
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_72) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _148_230 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _148_230 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_79, _53_81) -> begin
(closure_to_string c)
end
| MemoLazy (_53_85) -> begin
"MemoLazy"
end
| Abs (_53_88, bs, _53_91, _53_93, _53_95) -> begin
(let _148_233 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _148_233))
end
| _53_99 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _148_236 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _148_236 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_106 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_113 -> begin
(let _148_252 = (let _148_251 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _148_251))
in (FStar_All.failwith _148_252))
end)


let comp_to_comp_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (Some (u))))
end
| _53_129 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c)))


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_141 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_141) with
| (binders, cdef) -> begin
(

let _53_142 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let inst = (let _148_264 = (let _148_263 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_148_263)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_147 _53_151 -> (match (((_53_147), (_53_151))) with
| ((x, _53_146), (t, _53_150)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _148_264))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _148_265 = (

let _53_154 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _53_154.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _53_154.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_154.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_154.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _148_265 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c)))))
end))
end)))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid) then begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid) then begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end else begin
None
end
end
end)


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let _53_176 = (FStar_List.fold_left (fun _53_167 u -> (match (_53_167) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_171 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_171) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_176) with
| (_53_173, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| _53_193 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_186 -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses)) then begin
(FStar_Syntax_Syntax.U_unknown)::[]
end else begin
(FStar_All.failwith "Universe variable not found")
end
end
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us = (let _148_282 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _148_282 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_220 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_220) with
| (_53_218, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_222 -> begin
us
end))
end
| _53_224 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _148_285 = (aux u)
in (FStar_List.map (fun _148_284 -> FStar_Syntax_Syntax.U_succ (_148_284)) _148_285))
end)))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
FStar_Syntax_Syntax.U_unknown
end else begin
(match ((aux u)) with
| ([]) | ((FStar_Syntax_Syntax.U_zero)::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u)::[] -> begin
u
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u)::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end)
end)))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (

let _53_243 = (log cfg (fun _53_242 -> (match (()) with
| () -> begin
(let _148_309 = (FStar_Syntax_Print.tag_of_term t)
in (let _148_308 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _148_309 _148_308)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_247 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_250) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_263) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _148_314 = (let _148_313 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_148_313))
in (mk _148_314 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _148_315 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _148_315))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_274) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_281) -> begin
(closure_as_term cfg env t0)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _53_297 = (closures_as_binders_delayed cfg env bs)
in (match (_53_297) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _148_318 = (let _148_317 = (let _148_316 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_148_316)))
in FStar_Syntax_Syntax.Tm_abs (_148_317))
in (mk _148_318 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_305 = (closures_as_binders_delayed cfg env bs)
in (match (_53_305) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_313 = (let _148_320 = (let _148_319 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_319)::[])
in (closures_as_binders_delayed cfg env _148_320))
in (match (_53_313) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _148_324 = (let _148_323 = (let _148_322 = (let _148_321 = (FStar_List.hd x)
in (FStar_All.pipe_right _148_321 Prims.fst))
in ((_148_322), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_148_323))
in (mk _148_324 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _148_330 = (let _148_329 = (let _148_328 = (closure_as_term_delayed cfg env t1)
in (let _148_327 = (let _148_326 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _148_325 -> FStar_Util.Inl (_148_325)) _148_326))
in ((_148_328), (_148_327), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_148_329))
in (mk _148_330 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _148_336 = (let _148_335 = (let _148_334 = (closure_as_term_delayed cfg env t1)
in (let _148_333 = (let _148_332 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _148_331 -> FStar_Util.Inr (_148_331)) _148_332))
in ((_148_334), (_148_333), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_148_335))
in (mk _148_336 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _148_341 = (let _148_340 = (let _148_339 = (closure_as_term_delayed cfg env t')
in (let _148_338 = (let _148_337 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_148_337))
in ((_148_339), (_148_338))))
in FStar_Syntax_Syntax.Tm_meta (_148_340))
in (mk _148_341 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _148_347 = (let _148_346 = (let _148_345 = (closure_as_term_delayed cfg env t')
in (let _148_344 = (let _148_343 = (let _148_342 = (closure_as_term_delayed cfg env tbody)
in ((m), (_148_342)))
in FStar_Syntax_Syntax.Meta_monadic (_148_343))
in ((_148_345), (_148_344))))
in FStar_Syntax_Syntax.Tm_meta (_148_346))
in (mk _148_347 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(let _148_353 = (let _148_352 = (let _148_351 = (closure_as_term_delayed cfg env t')
in (let _148_350 = (let _148_349 = (let _148_348 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (_148_348)))
in FStar_Syntax_Syntax.Meta_monadic_lift (_148_349))
in ((_148_351), (_148_350))))
in FStar_Syntax_Syntax.Tm_meta (_148_352))
in (mk _148_353 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _148_356 = (let _148_355 = (let _148_354 = (closure_as_term_delayed cfg env t')
in ((_148_354), (m)))
in FStar_Syntax_Syntax.Tm_meta (_148_355))
in (mk _148_356 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_360 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_366) -> begin
body
end
| FStar_Util.Inl (_53_369) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_372 = lb
in {FStar_Syntax_Syntax.lbname = _53_372.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_372.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_372.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_376, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_385 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_389 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_393 = lb
in (let _148_368 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _148_367 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_393.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_393.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _148_368; FStar_Syntax_Syntax.lbeff = _53_393.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _148_367}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_396 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_411 -> (match (_53_411) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_416) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_426 = (norm_pat env hd)
in (match (_53_426) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _148_380 = (norm_pat env p)
in (Prims.fst _148_380)))))
in (((

let _53_429 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_429.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_429.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_446 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_437 _53_440 -> (match (((_53_437), (_53_440))) with
| ((pats, env), (p, b)) -> begin
(

let _53_443 = (norm_pat env p)
in (match (_53_443) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_446) with
| (pats, env) -> begin
(((

let _53_447 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_447.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_447.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_451 = x
in (let _148_383 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_451.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_451.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_383}))
in (((

let _53_454 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_454.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_454.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_458 = x
in (let _148_384 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_458.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_458.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_384}))
in (((

let _53_461 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_461.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_461.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_467 = x
in (let _148_385 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_467.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_467.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_385}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_471 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_471.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_471.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_475 = (norm_pat env pat)
in (match (_53_475) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_386 = (closure_as_term cfg env w)
in Some (_148_386))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _148_389 = (let _148_388 = (let _148_387 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_148_387)))
in FStar_Syntax_Syntax.Tm_match (_148_388))
in (mk _148_389 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_486 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_492 -> begin
(FStar_List.map (fun _53_495 -> (match (_53_495) with
| (x, imp) -> begin
(let _148_397 = (closure_as_term_delayed cfg env x)
in ((_148_397), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_511 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_501 _53_504 -> (match (((_53_501), (_53_504))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_505 = b
in (let _148_403 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_505.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_505.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_403}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_511) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_517 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _148_408 = (closure_as_term_delayed cfg env t)
in (let _148_407 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _148_408 _148_407)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _148_410 = (closure_as_term_delayed cfg env t)
in (let _148_409 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _148_410 _148_409)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _148_412 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_148_412))
end
| f -> begin
f
end))))
in (let _148_414 = (

let _53_535 = c
in (let _148_413 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _148_413; FStar_Syntax_Syntax.effect_name = _53_535.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _148_414)))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_total_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid))
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
end
| _53_544 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _148_427 = (let _148_426 = (FStar_Util.string_of_int i)
in ((_148_426), (None)))
in FStar_Const.Const_int (_148_427)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _148_623 = (let _148_622 = (FStar_List.map (fun m -> (let _148_621 = (let _148_590 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_148_590), ((fun x y -> (int_as_const (x + y))))))
in (let _148_620 = (let _148_619 = (let _148_601 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_148_601), ((fun x y -> (int_as_const (x - y))))))
in (let _148_618 = (let _148_617 = (let _148_612 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_148_612), ((fun x y -> (int_as_const (x * y))))))
in (_148_617)::[])
in (_148_619)::_148_618))
in (_148_621)::_148_620))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _148_622))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _148_623))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (let _148_633 = (let _148_632 = (let _148_631 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _148_631 FStar_Syntax_Syntax.Delta_constant None))
in FStar_Syntax_Syntax.Tm_fvar (_148_632))
in (mk _148_633)))
in (

let ctor = (fun x -> (let _148_638 = (let _148_637 = (let _148_636 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _148_636 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in FStar_Syntax_Syntax.Tm_fvar (_148_637))
in (mk _148_638)))
in (let _148_668 = (let _148_665 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((_148_665), ((fun s -> (let _148_664 = (FStar_String.list_of_string s)
in (let _148_663 = (let _148_662 = (let _148_661 = (let _148_660 = (let _148_656 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_656 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _148_659 = (let _148_658 = (let _148_657 = (name (("FStar")::("Char")::("char")::[]))
in ((_148_657), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (_148_658)::[])
in ((_148_660), (_148_659))))
in FStar_Syntax_Syntax.Tm_app (_148_661))
in (mk _148_662))
in (FStar_List.fold_right (fun c a -> (let _148_655 = (let _148_654 = (let _148_653 = (let _148_646 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_646 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _148_652 = (let _148_651 = (let _148_647 = (name (("FStar")::("Char")::("char")::[]))
in ((_148_647), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (let _148_650 = (let _148_649 = (let _148_648 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((_148_648), (None)))
in (_148_649)::(((a), (None)))::[])
in (_148_651)::_148_650))
in ((_148_653), (_148_652))))
in FStar_Syntax_Syntax.Tm_app (_148_654))
in (mk _148_655))) _148_664 _148_663)))))))
in (_148_668)::[]))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let find = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_594 -> (match (_53_594) with
| (l, _53_593) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| _53_596 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_604))::((a2, _53_600))::[]) -> begin
(match ((find fv arith_ops)) with
| None -> begin
tm
end
| Some (_53_611, op) -> begin
(

let norm = (fun i j -> (

let c = (let _148_685 = (FStar_Util.int_of_string i)
in (let _148_684 = (FStar_Util.int_of_string j)
in (op _148_685 _148_684)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _148_689 = (let _148_686 = (FStar_Syntax_Subst.compress a1)
in _148_686.FStar_Syntax_Syntax.n)
in (let _148_688 = (let _148_687 = (FStar_Syntax_Subst.compress a2)
in _148_687.FStar_Syntax_Syntax.n)
in ((_148_689), (_148_688))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _53_622))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _53_630))::[])) -> begin
(match ((let _148_697 = (let _148_690 = (FStar_Syntax_Subst.compress head1)
in _148_690.FStar_Syntax_Syntax.n)
in (let _148_696 = (let _148_691 = (FStar_Syntax_Subst.compress head2)
in _148_691.FStar_Syntax_Syntax.n)
in (let _148_695 = (let _148_692 = (FStar_Syntax_Subst.compress arg1)
in _148_692.FStar_Syntax_Syntax.n)
in (let _148_694 = (let _148_693 = (FStar_Syntax_Subst.compress arg2)
in _148_693.FStar_Syntax_Syntax.n)
in ((_148_697), (_148_696), (_148_695), (_148_694))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _148_701 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _148_700 = (let _148_699 = (let _148_698 = (norm i j)
in ((_148_698), (None)))
in (_148_699)::[])
in (FStar_Syntax_Util.mk_app _148_701 _148_700)))
end
| _53_652 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _53_665 -> begin
tm
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_669))::[]) -> begin
(match ((find fv un_ops)) with
| None -> begin
tm
end
| Some (_53_676, op) -> begin
(match ((let _148_704 = (FStar_Syntax_Subst.compress a1)
in _148_704.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, _53_682)) -> begin
(let _148_705 = (FStar_Bytes.unicode_bytes_as_string b)
in (op _148_705))
end
| _53_687 -> begin
tm
end)
end)
end
| _53_689 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_694 = t
in {FStar_Syntax_Syntax.n = _53_694.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_694.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_694.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_703 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(reduce_primops steps tm)
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_781 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| _53_824 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_851))::((_53_842, (arg, _53_845)))::[] -> begin
arg
end
| _53_855 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_859))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_865))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_869 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _148_716 = (FStar_Syntax_Subst.compress t)
in _148_716.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_887)::[], body, _53_891) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_899 -> begin
tm
end)
end
| _53_901 -> begin
tm
end)
end
| _53_903 -> begin
tm
end)
end else begin
tm
end
end
end
end
end
end
| _53_905 -> begin
tm
end)
end))))


let is_norm_request = (fun hd args -> (match ((let _148_720 = (let _148_719 = (FStar_Syntax_Util.un_uinst hd)
in _148_719.FStar_Syntax_Syntax.n)
in ((_148_720), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_53_913)::(_53_911)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_53_919)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| _53_923 -> begin
false
end))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| _53_937 -> begin
(FStar_All.failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_944 = (log cfg (fun _53_943 -> (match (()) with
| () -> begin
(let _148_754 = (FStar_Syntax_Print.tag_of_term t)
in (let _148_753 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _148_754 _148_753)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_947) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app (hd, args) when ((is_norm_request hd args) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _53_990 = cfg
in {steps = s; tcenv = _53_990.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_999; FStar_Syntax_Syntax.pos = _53_997; FStar_Syntax_Syntax.vars = _53_995}, (a1)::(a2)::rest) -> begin
(

let _53_1013 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1013) with
| (hd, _53_1012) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_1021; FStar_Syntax_Syntax.pos = _53_1019; FStar_Syntax_Syntax.vars = _53_1017}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_1032 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1032) with
| (reify_head, _53_1031) -> begin
(

let a = (let _148_758 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (Prims.fst a))
in (FStar_Syntax_Subst.compress _148_758))
in (

let _53_1034 = (let _148_760 = (FStar_Syntax_Print.tag_of_term a)
in (let _148_759 = (FStar_Syntax_Print.term_to_string a)
in (FStar_Util.print2_warning "TRYING NORMALIZATION OF REIFY: %s ... %s\n" _148_760 _148_759)))
in (

let reify_lift = (fun e msrc mtgt t -> if (FStar_Syntax_Util.is_pure_effect msrc) then begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv mtgt)
in (

let _53_1045 = ed.FStar_Syntax_Syntax.return_repr
in (match (_53_1045) with
| (_53_1043, return_repr) -> begin
(let _148_774 = (let _148_773 = (let _148_772 = (let _148_771 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_770 = (let _148_769 = (FStar_Syntax_Syntax.as_arg e)
in (_148_769)::[])
in (_148_771)::_148_770))
in ((return_repr), (_148_772)))
in FStar_Syntax_Syntax.Tm_app (_148_773))
in (FStar_Syntax_Syntax.mk _148_774 None e.FStar_Syntax_Syntax.pos))
end)))
end else begin
(FStar_All.failwith "NYI: monadic lift normalisation")
end)
in (

let normalization_reify_result = (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _148_775 = (FStar_Syntax_Subst.compress e)
in _148_775.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_1064 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_1064) with
| (_53_1062, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (let _148_776 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((lb.FStar_Syntax_Syntax.lbdef), (FStar_Syntax_Syntax.Meta_monadic (((m), (lb.FStar_Syntax_Syntax.lbtyp))))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_reify _148_776))
in (

let body = (let _148_777 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m), (t_body))))))) None body.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_reify _148_777))
in (

let body = (let _148_781 = (let _148_780 = (let _148_779 = (let _148_778 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_778)::[])
in ((_148_779), (body), (None)))
in FStar_Syntax_Syntax.Tm_abs (_148_780))
in (FStar_Syntax_Syntax.mk _148_781 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _148_795 = (let _148_794 = (let _148_793 = (let _148_792 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _148_791 = (let _148_790 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _148_789 = (let _148_788 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_787 = (let _148_786 = (FStar_Syntax_Syntax.as_arg head)
in (let _148_785 = (let _148_784 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_783 = (let _148_782 = (FStar_Syntax_Syntax.as_arg body)
in (_148_782)::[])
in (_148_784)::_148_783))
in (_148_786)::_148_785))
in (_148_788)::_148_787))
in (_148_790)::_148_789))
in (_148_792)::_148_791))
in ((bind_repr), (_148_793)))
in FStar_Syntax_Syntax.Tm_app (_148_794))
in (FStar_Syntax_Syntax.mk _148_795 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified)))))
end
| FStar_Util.Inr (_53_1072) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_1082 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_1082) with
| (_53_1080, bind_repr) -> begin
(

let rec bind_on_lift = (fun args acc -> (match (args) with
| [] -> begin
(match ((FStar_List.rev acc)) with
| [] -> begin
(FStar_All.failwith "bind_on_lift should be always called with a non-empty list")
end
| (head)::args -> begin
(let _148_802 = (let _148_801 = (let _148_800 = (FStar_List.map FStar_Syntax_Syntax.as_arg args)
in ((head), (_148_800)))
in FStar_Syntax_Syntax.Tm_app (_148_801))
in (FStar_Syntax_Syntax.mk _148_802 None t.FStar_Syntax_Syntax.pos))
end)
end
| (e)::es -> begin
(match ((let _148_803 = (FStar_Syntax_Subst.compress e)
in _148_803.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "monadic_app_var" None t')
in (

let body = (let _148_805 = (let _148_804 = (FStar_Syntax_Syntax.bv_to_name x)
in (_148_804)::acc)
in (bind_on_lift es _148_805))
in (

let lifted_e0 = (reify_lift e0 m1 m2 t')
in (

let continuation = (FStar_Syntax_Util.abs ((((x), (None)))::[]) body (Some (FStar_Util.Inr (m2))))
in (let _148_819 = (let _148_818 = (let _148_817 = (let _148_816 = (FStar_Syntax_Syntax.as_arg t')
in (let _148_815 = (let _148_814 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _148_813 = (let _148_812 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_811 = (let _148_810 = (FStar_Syntax_Syntax.as_arg lifted_e0)
in (let _148_809 = (let _148_808 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_807 = (let _148_806 = (FStar_Syntax_Syntax.as_arg continuation)
in (_148_806)::[])
in (_148_808)::_148_807))
in (_148_810)::_148_809))
in (_148_812)::_148_811))
in (_148_814)::_148_813))
in (_148_816)::_148_815))
in ((bind_repr), (_148_817)))
in FStar_Syntax_Syntax.Tm_app (_148_818))
in (FStar_Syntax_Syntax.mk _148_819 None e0.FStar_Syntax_Syntax.pos))))))
end
| _53_1107 -> begin
(bind_on_lift es ((e)::acc))
end)
end))
in (

let binded_e = (let _148_821 = (let _148_820 = (FStar_List.map Prims.fst args)
in (head)::_148_820)
in (bind_on_lift _148_821 []))
in (norm cfg env stack binded_e)))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (reify_lift e msrc mtgt t')
in (norm cfg env stack lifted))
end
| _53_1119 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_1128)); FStar_Syntax_Syntax.tk = _53_1126; FStar_Syntax_Syntax.pos = _53_1124; FStar_Syntax_Syntax.vars = _53_1122}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_1144 -> (match (_53_1144) with
| (pat, wopt, tm) -> begin
(let _148_823 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_148_823)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_1148 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
in (

let _53_1151 = (let _148_825 = (FStar_Syntax_Print.term_to_string a)
in (let _148_824 = (FStar_Syntax_Print.term_to_string normalization_reify_result)
in (FStar_Util.print2_warning "RESULT OF NORMALIZATION : before %s    after %s\n" _148_825 _148_824)))
in normalization_reify_result)))))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _148_826 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _148_826)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _148_828 = (let _148_827 = (FStar_List.map (norm_universe cfg env) us)
in ((_148_827), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_148_828))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun _53_5 -> (match (_53_5) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end))))
in if (not (should_delta)) then begin
(rebuild cfg env stack t)
end else begin
(

let r_env = (let _148_830 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv _148_830))
in (match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _53_1179 = (log cfg (fun _53_1178 -> (match (()) with
| () -> begin
(let _148_833 = (FStar_Syntax_Print.term_to_string t0)
in (let _148_832 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _148_833 _148_832)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_1185))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_1193 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_1195 -> begin
(let _148_837 = (let _148_836 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _148_836))
in (FStar_All.failwith _148_837))
end)
end else begin
(norm cfg env stack t)
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1199) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
if ((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps)))) then begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _53_1213 = (log cfg (fun _53_1212 -> (match (()) with
| () -> begin
(let _148_840 = (FStar_Syntax_Print.term_to_string t)
in (let _148_839 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _148_840 _148_839)))
end)))
in (match ((let _148_841 = (FStar_Syntax_Subst.compress t')
in _148_841.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1216) -> begin
(norm cfg env stack t')
end
| _53_1219 -> begin
(rebuild cfg env stack t')
end))
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end)
end else begin
(norm cfg env stack t0)
end
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (_53_1229))::_53_1227 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1235))::_53_1233 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1241, _53_1243))::stack_rest -> begin
(match (c) with
| Univ (_53_1248) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1251 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1254)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1258 = (log cfg (fun _53_1257 -> (match (()) with
| () -> begin
(let _148_843 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_843))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1264 = (log cfg (fun _53_1263 -> (match (()) with
| () -> begin
(let _148_845 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_845))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1270 = (log cfg (fun _53_1269 -> (match (()) with
| () -> begin
(let _148_847 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_847))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1273 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1275 -> begin
(

let cfg = (

let _53_1276 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1276.tcenv; delta_level = _53_1276.delta_level})
in (let _148_848 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_848)))
end)
end
| (_53_1281)::tl -> begin
(

let _53_1284 = (log cfg (fun _53_1283 -> (match (()) with
| () -> begin
(let _148_850 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_850))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1293 = cfg
in {steps = s; tcenv = _53_1293.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1299 = (set_memo r ((env), (t)))
in (

let _53_1302 = (log cfg (fun _53_1301 -> (match (()) with
| () -> begin
(let _148_852 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _148_852))
end)))
in (norm cfg env stack t)))
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _148_853 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_853))
end else begin
(

let _53_1338 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1338) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _148_859 = (let _148_857 = (let _148_855 = (let _148_854 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _148_854))
in (FStar_All.pipe_right _148_855 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _148_857 (fun _148_856 -> FStar_Util.Inl (_148_856))))
in (FStar_All.pipe_right _148_859 (fun _148_858 -> Some (_148_858))))
end
| _53_1343 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1346 -> (Dummy)::env) env))
in (

let _53_1350 = (log cfg (fun _53_1349 -> (match (()) with
| () -> begin
(let _148_863 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _148_863))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1358 stack -> (match (_53_1358) with
| (a, aq) -> begin
(let _148_870 = (let _148_869 = (let _148_868 = (let _148_867 = (let _148_866 = (FStar_Util.mk_ref None)
in ((env), (a), (_148_866), (false)))
in Clos (_148_867))
in ((_148_868), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_148_869))
in (_148_870)::stack)
end)) args))
in (

let _53_1362 = (log cfg (fun _53_1361 -> (match (()) with
| () -> begin
(let _148_872 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _148_872))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let _53_1372 = x
in {FStar_Syntax_Syntax.ppname = _53_1372.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1372.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1376 -> begin
(let _148_873 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_873))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1380 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1380) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _148_876 = (let _148_875 = (let _148_874 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1382 = x
in {FStar_Syntax_Syntax.ppname = _53_1382.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1382.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_148_874)))
in FStar_Syntax_Syntax.Tm_refine (_148_875))
in (mk _148_876 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _148_877 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_877))
end else begin
(

let _53_1391 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1391) with
| (bs, c) -> begin
(

let c = (let _148_880 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1393 -> (Dummy)::env) env))
in (norm_comp cfg _148_880 c))
in (

let t = (let _148_881 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _148_881 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1421 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1424 = (log cfg (fun _53_1423 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _148_883 = (norm cfg env [] t)
in FStar_Util.Inl (_148_883))
end
| FStar_Util.Inr (c) -> begin
(let _148_884 = (norm_comp cfg env c)
in FStar_Util.Inr (_148_884))
end)
in (let _148_885 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _148_885)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1437, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1449); FStar_Syntax_Syntax.lbunivs = _53_1447; FStar_Syntax_Syntax.lbtyp = _53_1445; FStar_Syntax_Syntax.lbeff = _53_1443; FStar_Syntax_Syntax.lbdef = _53_1441})::_53_1439), _53_1455) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))))))) then begin
(

let env = (let _148_888 = (let _148_887 = (let _148_886 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_148_886), (false)))
in Clos (_148_887))
in (_148_888)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1469 = (let _148_891 = (let _148_890 = (let _148_889 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _148_889 FStar_Syntax_Syntax.mk_binder))
in (_148_890)::[])
in (FStar_Syntax_Subst.open_term _148_891 body))
in (match (_53_1469) with
| (bs, body) -> begin
(

let lb = (

let _53_1470 = lb
in (let _148_897 = (let _148_894 = (let _148_892 = (FStar_List.hd bs)
in (FStar_All.pipe_right _148_892 Prims.fst))
in (FStar_All.pipe_right _148_894 (fun _148_893 -> FStar_Util.Inl (_148_893))))
in (let _148_896 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _148_895 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _148_897; FStar_Syntax_Syntax.lbunivs = _53_1470.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _148_896; FStar_Syntax_Syntax.lbeff = _53_1470.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _148_895}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1474 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _148_900 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_900))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1500 = (FStar_List.fold_right (fun lb _53_1489 -> (match (_53_1489) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _148_903 = (

let _53_1490 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1490.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1490.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _148_903))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1500) with
| (rec_env, memos, _53_1499) -> begin
(

let _53_1503 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _148_910 = (let _148_909 = (let _148_908 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_148_908), (false)))
in Clos (_148_909))
in (_148_910)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1518 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _53_1518.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1527 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _53_1527.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end
| _53_1531 -> begin
(match (stack) with
| (_53_1535)::_53_1533 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1540) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1547 -> begin
(norm cfg env stack head)
end)
end
| _53_1549 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _148_911 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_148_911))
end
| _53_1554 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1562 -> (match (_53_1562) with
| (a, imp) -> begin
(let _148_916 = (norm cfg env [] a)
in ((_148_916), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _53_1571 = comp
in (let _148_923 = (let _148_922 = (let _148_921 = (norm cfg env [] t)
in (let _148_920 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_148_921), (_148_920))))
in FStar_Syntax_Syntax.Total (_148_922))
in {FStar_Syntax_Syntax.n = _148_923; FStar_Syntax_Syntax.tk = _53_1571.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1571.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1571.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _53_1577 = comp
in (let _148_927 = (let _148_926 = (let _148_925 = (norm cfg env [] t)
in (let _148_924 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_148_925), (_148_924))))
in FStar_Syntax_Syntax.GTotal (_148_926))
in {FStar_Syntax_Syntax.n = _148_927; FStar_Syntax_Syntax.tk = _53_1577.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1577.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1577.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1585 -> (match (_53_1585) with
| (a, i) -> begin
(let _148_931 = (norm cfg env [] a)
in ((_148_931), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_6 -> (match (_53_6) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _148_933 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_148_933))
end
| f -> begin
f
end))))
in (

let _53_1591 = comp
in (let _148_938 = (let _148_937 = (

let _53_1593 = ct
in (let _148_936 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _148_935 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _148_934 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _148_936; FStar_Syntax_Syntax.effect_name = _53_1593.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _148_935; FStar_Syntax_Syntax.effect_args = _148_934; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_148_937))
in {FStar_Syntax_Syntax.n = _148_938; FStar_Syntax_Syntax.tk = _53_1591.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1591.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1591.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1600 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1600.tcenv; delta_level = _53_1600.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _148_946 = (norm t)
in (FStar_Syntax_Util.non_informative _148_946)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1605) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _53_1611 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _53_1611.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1611.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1611.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1618 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1618.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1618.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1618.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1618.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1622 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1622.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1622.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1622.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1622.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1625 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1625.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1625.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1625.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1628 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1633 -> (match (_53_1633) with
| (x, imp) -> begin
(let _148_951 = (

let _53_1634 = x
in (let _148_950 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1634.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1634.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_950}))
in ((_148_951), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1647 = (FStar_List.fold_left (fun _53_1641 b -> (match (_53_1641) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1647) with
| (nbs, _53_1646) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _148_962 = (let _148_961 = (let _148_960 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _148_960))
in FStar_Util.Inl (_148_961))
in Some (_148_962))
end else begin
(let _148_965 = (let _148_964 = (let _148_963 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _148_963))
in FStar_Util.Inl (_148_964))
in Some (_148_965))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1656 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
(

let _53_1666 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms"))) then begin
(let _148_971 = (FStar_Syntax_Print.term_to_string tm)
in (let _148_970 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _148_971 _148_970)))
end else begin
()
end
in (rebuild cfg env stack t))
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1674 = cfg
in {steps = s; tcenv = _53_1674.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1687 = (set_memo r ((env), (t)))
in (

let _53_1690 = (log cfg (fun _53_1689 -> (match (()) with
| () -> begin
(let _148_973 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _148_973))
end)))
in (rebuild cfg env stack t)))
end
| (Let (env', bs, lb, r))::stack -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) None r)
in (rebuild cfg env' stack t)))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (let _148_974 = (

let _53_1713 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1713.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1713.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1713.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _148_974))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1749), aq, r))::stack -> begin
(

let _53_1758 = (log cfg (fun _53_1757 -> (match (()) with
| () -> begin
(let _148_976 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _148_976))
end)))
in if (FStar_List.contains (Exclude (Iota)) cfg.steps) then begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end else begin
(match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (MemoLazy (m))::(App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end
| Some (_53_1768, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _148_977 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _148_977)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1789 = (log cfg (fun _53_1788 -> (match (()) with
| () -> begin
(let _148_979 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _148_979))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _53_1793 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun _53_7 -> (match (_53_7) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _53_1799 -> begin
false
end))))
in (

let steps' = if (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)) then begin
(Exclude (Zeta))::[]
end else begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end
in (

let _53_1802 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = _53_1802.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg_exclude_iota_zeta env t)
end else begin
(norm cfg_exclude_iota_zeta env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1812) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1822 = (norm_pat env hd)
in (match (_53_1822) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _148_992 = (norm_pat env p)
in (Prims.fst _148_992)))))
in (((

let _53_1825 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1825.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1825.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1842 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1833 _53_1836 -> (match (((_53_1833), (_53_1836))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1839 = (norm_pat env p)
in (match (_53_1839) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1842) with
| (pats, env) -> begin
(((

let _53_1843 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1843.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1843.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1847 = x
in (let _148_995 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1847.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1847.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_995}))
in (((

let _53_1850 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1850.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1850.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1854 = x
in (let _148_996 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1854.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1854.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_996}))
in (((

let _53_1857 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1857.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1857.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1863 = x
in (let _148_997 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1863.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1863.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_997}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1867 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1867.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1867.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1871 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1876 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1876) with
| (p, wopt, e) -> begin
(

let _53_1879 = (norm_pat env p)
in (match (_53_1879) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_999 = (norm_or_whnf env w)
in Some (_148_999))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _148_1000 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _148_1000)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1890) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1915 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee p -> (

let scrutinee = (FStar_Syntax_Util.unmeta scrutinee)
in (

let _53_1932 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_53_1932) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_53_1938) -> begin
Some (m)
end
| FStar_Util.Inr (true) -> begin
Some (m)
end
| FStar_Util.Inr (false) -> begin
None
end))))
in (match (mopt) with
| None -> begin
FStar_Util.Inr (false)
end
| Some (m) -> begin
m
end))
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
FStar_Util.Inl ((scrutinee)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (_53_1955) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1962 -> begin
(let _148_1017 = (not ((is_cons head)))
in FStar_Util.Inr (_148_1017))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _148_1018 = (FStar_Syntax_Util.un_uinst head)
in _148_1018.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1970 -> begin
(let _148_1019 = (not ((is_cons head)))
in FStar_Util.Inr (_148_1019))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1980))::rest_a, ((p, _53_1986))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1994 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(match ((matches_pat scrutinee p)) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let _53_2012 = (log cfg (fun _53_2011 -> (match (()) with
| () -> begin
(let _148_1030 = (FStar_Syntax_Print.pat_to_string p)
in (let _148_1029 = (let _148_1028 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _148_1028 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _148_1030 _148_1029)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _148_1035 = (let _148_1034 = (let _148_1033 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_148_1033), (false)))
in Clos (_148_1034))
in (_148_1035)::env)) env s)
in (let _148_1036 = (guard_when_clause wopt b rest)
in (norm cfg env stack _148_1036))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun _53_8 -> (match (_53_8) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| _53_2025 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _53_2029 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _148_1048 = (config s e)
in (norm _148_1048 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _148_1055 = (config s e)
in (norm_comp _148_1055 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _148_1060 = (config [] env)
in (norm_universe _148_1060 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _148_1065 = (config [] env)
in (ghost_to_pure_aux _148_1065 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _148_1072 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _148_1072)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_2048 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_2048.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_2048.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_2050 -> (match (()) with
| () -> begin
(let _148_1074 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _148_1074))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _148_1079 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _148_1079)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _148_1085 = (let _148_1084 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _148_1084 [] c))
in (FStar_Syntax_Print.comp_to_string _148_1085)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _148_1096 = (let _148_1095 = (let _148_1094 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_148_1094)))
in FStar_Syntax_Syntax.Tm_refine (_148_1095))
in (mk _148_1096 t0.FStar_Syntax_Syntax.pos))
end
| _53_2073 -> begin
t
end))
end
| _53_2075 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let _53_2080 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_2080) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_2083 -> begin
(

let _53_2086 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_2086) with
| (binders, args) -> begin
(let _148_1105 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _148_1104 = (let _148_1103 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _148_1101 -> FStar_Util.Inl (_148_1101)))
in (FStar_All.pipe_right _148_1103 (fun _148_1102 -> Some (_148_1102))))
in (FStar_Syntax_Util.abs binders _148_1105 _148_1104)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match ((let _148_1110 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_148_1110), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_2092) -> begin
(let _148_1111 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t _148_1111))
end
| (_53_2095, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| _53_2100 -> begin
(

let _53_2103 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_2103) with
| (head, args) -> begin
(match ((let _148_1112 = (FStar_Syntax_Subst.compress head)
in _148_1112.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_2105, thead) -> begin
(

let _53_2111 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_2111) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_2119 = (env.FStar_TypeChecker_Env.type_of (

let _53_2112 = env
in {FStar_TypeChecker_Env.solver = _53_2112.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_2112.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_2112.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_2112.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_2112.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_2112.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_2112.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_2112.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_2112.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_2112.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_2112.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_2112.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_2112.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_2112.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_2112.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_2112.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_2112.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_2112.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_2112.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_2112.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_2112.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_2119) with
| (_53_2115, ty, _53_2118) -> begin
(eta_expand_with_type t ty)
end))
end
end))
end
| _53_2121 -> begin
(

let _53_2129 = (env.FStar_TypeChecker_Env.type_of (

let _53_2122 = env
in {FStar_TypeChecker_Env.solver = _53_2122.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_2122.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_2122.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_2122.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_2122.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_2122.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_2122.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_2122.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_2122.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_2122.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_2122.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_2122.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_2122.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_2122.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_2122.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_2122.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_2122.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_2122.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_2122.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_2122.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_2122.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_2129) with
| (_53_2125, ty, _53_2128) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end))




