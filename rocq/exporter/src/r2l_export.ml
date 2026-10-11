(* Rocq2Lean source exporter.

   Frontend: MetaRocq Template quotation ([Ast_quoter.quote_term_rec ~bypass:true]), which quotes
   each root together with its recursive dependency environment, reading opaque bodies through
   the [opaque_access] state of the vernacular command.  This module only serializes the quoted
   MetaRocq AST, field by field, into the NDJSON IR described in docs/IR_SPEC.md; it performs no
   normalization.  A small native audit adds what the quotation does not carry (body kind,
   typing flags, template/private status, library files). *)

open Metarocq_template_plugin
module A = Ast0
module E = Ast0.Env
module B = BasicAst
module K = Kernames
module U = Universes0
module J = R2l_json

let ir_version = "rocq2lean-ir/0.2"
let metarocq_commit = "c18395ad772a40d59b6d04a5fcd1a4e0e5073d81"

let bs = Caml_bytestring.caml_string_of_bytestring
let nat = Caml_nat.caml_int_of_nat

let rec int_of_pos = function
  | BinNums.Coq_xH -> 1
  | BinNums.Coq_xO p -> 2 * int_of_pos p
  | BinNums.Coq_xI p -> (2 * int_of_pos p) + 1

let int_of_z = function
  | BinNums.Z0 -> 0
  | BinNums.Zpos p -> int_of_pos p
  | BinNums.Zneg p -> -int_of_pos p

(* ---------- names ---------- *)

(* MetaRocq dirpaths are innermost-first (Rocq's internal order); the IR stores them outer-first. *)
let dirpath_outer_first (dp : K.dirpath) = List.rev_map bs dp

(* Canonical string keys: file components joined by '.', module fields by '/', then '.' ident.
   Identifiers contain neither '.' nor '/', so keys are unambiguous. *)
let rec mp_key = function
  | K.MPfile dp -> String.concat "." (dirpath_outer_first dp)
  | K.MPdot (mp, id) -> mp_key mp ^ "/" ^ bs id
  | K.MPbound (dp, id, n) ->
    Printf.sprintf "%%bound(%s,%s,%d)" (String.concat "." (dirpath_outer_first dp)) (bs id) (nat n)

let kn_key ((mp, id) : K.kername) = mp_key mp ^ "." ^ bs id

let rec mp_json = function
  | K.MPfile dp -> J.Obj [ ("file", J.Arr (List.map (fun s -> J.Str s) (dirpath_outer_first dp))) ]
  | K.MPdot (mp, id) -> J.Obj [ ("dot", J.Arr [ mp_json mp; J.Str (bs id) ]) ]
  | K.MPbound (dp, id, n) ->
    J.Obj
      [ ( "bound",
          J.Arr
            [ J.Arr (List.map (fun s -> J.Str s) (dirpath_outer_first dp)); J.Str (bs id); J.Int (nat n) ] ) ]

let ind_json (i : K.inductive) =
  J.Obj [ ("mind", J.Str (kn_key i.K.inductive_mind)); ("i", J.Int (nat i.K.inductive_ind)) ]

(* ---------- universes ---------- *)

let level_json = function
  | U.Level.Coq_lzero -> J.Obj [ ("k", J.Str "set") ]
  | U.Level.Coq_level s -> J.Obj [ ("k", J.Str "global"); ("n", J.Str (bs s)) ]
  | U.Level.Coq_lvar n -> J.Obj [ ("k", J.Str "var"); ("i", J.Int (nat n)) ]

let universe_json (u : U.Universe.t) =
  J.Arr
    (List.map
       (fun ((l, k) : U.LevelExpr.t) -> J.Obj [ ("l", level_json l); ("n", J.Int (nat k)) ])
       (U.LevelExprSet.elements u))

let sort_json = function
  | U.Sort.Coq_sProp -> J.Obj [ ("k", J.Str "prop") ]
  | U.Sort.Coq_sSProp -> J.Obj [ ("k", J.Str "sprop") ]
  | U.Sort.Coq_sType u -> J.Obj [ ("k", J.Str "type"); ("u", universe_json u) ]

let instance_json (i : U.Instance.t) = J.Arr (List.map level_json i)

let constraint_json (((l1, ct), l2) : U.UnivConstraint.t) =
  let rel =
    match ct with
    | U.ConstraintType.Le z -> J.Obj [ ("k", J.Str "le"); ("offset", J.Int (int_of_z z)) ]
    | U.ConstraintType.Eq -> J.Obj [ ("k", J.Str "eq") ]
  in
  J.Obj [ ("l", level_json l1); ("rel", rel); ("r", level_json l2) ]

let name_json = function B.Coq_nAnon -> J.Null | B.Coq_nNamed id -> J.Str (bs id)

let udecl_json = function
  | U.Monomorphic_ctx -> J.Obj [ ("k", J.Str "monomorphic") ]
  | U.Polymorphic_ctx (names, cs) ->
    J.Obj
      [ ("k", J.Str "polymorphic");
        ("names", J.Arr (List.map name_json names));
        ("constraints", J.Arr (List.map constraint_json (U.ConstraintSet.elements cs))) ]

(* ---------- terms ---------- *)

let rel_json = function B.Relevant -> J.Str "R" | B.Irrelevant -> J.Str "I"
let aname_json (a : B.aname) = J.Obj [ ("n", name_json a.B.binder_name); ("r", rel_json a.B.binder_relevance) ]

let rec term_json (t : A.term) : J.t =
  let k tag fields = J.Obj (("k", J.Str tag) :: fields) in
  match t with
  | A.Coq_tRel n -> k "rel" [ ("i", J.Int (nat n)) ]
  | A.Coq_tVar id -> k "var" [ ("id", J.Str (bs id)) ]
  | A.Coq_tEvar (ev, args) -> k "evar" [ ("ev", J.Int (nat ev)); ("args", terms args) ]
  | A.Coq_tSort s -> k "sort" [ ("s", sort_json s) ]
  | A.Coq_tCast (c, ck, ty) ->
    let kind = match ck with B.VmCast -> "vm" | B.NativeCast -> "native" | B.Cast -> "default" in
    k "cast" [ ("t", term_json c); ("kind", J.Str kind); ("ty", term_json ty) ]
  | A.Coq_tProd (na, ty, b) -> k "prod" [ ("n", aname_json na); ("ty", term_json ty); ("b", term_json b) ]
  | A.Coq_tLambda (na, ty, b) -> k "lam" [ ("n", aname_json na); ("ty", term_json ty); ("b", term_json b) ]
  | A.Coq_tLetIn (na, v, ty, b) ->
    k "let" [ ("n", aname_json na); ("v", term_json v); ("ty", term_json ty); ("b", term_json b) ]
  | A.Coq_tApp (f, args) -> k "app" [ ("f", term_json f); ("args", terms args) ]
  | A.Coq_tConst (c, u) -> k "const" [ ("c", J.Str (kn_key c)); ("u", instance_json u) ]
  | A.Coq_tInd (i, u) -> k "ind" [ ("ind", ind_json i); ("u", instance_json u) ]
  | A.Coq_tConstruct (i, c, u) -> k "construct" [ ("ind", ind_json i); ("c", J.Int (nat c)); ("u", instance_json u) ]
  | A.Coq_tCase (ci, p, c, brs) ->
    k "case"
      [ ( "ci",
          J.Obj
            [ ("ind", ind_json ci.B.ci_ind); ("npar", J.Int (nat ci.B.ci_npar)); ("r", rel_json ci.B.ci_relevance) ] );
        ( "p",
          J.Obj
            [ ("u", instance_json p.A.puinst);
              ("params", terms p.A.pparams);
              ("ctx", J.Arr (List.map aname_json p.A.pcontext));
              ("ret", term_json p.A.preturn) ] );
        ("c", term_json c);
        ( "brs",
          J.Arr
            (List.map
               (fun (br : A.term A.branch) ->
                 J.Obj [ ("ctx", J.Arr (List.map aname_json br.A.bcontext)); ("body", term_json br.A.bbody) ])
               brs) ) ]
  | A.Coq_tProj (p, c) ->
    k "proj"
      [ ( "p",
          J.Obj
            [ ("ind", ind_json p.K.proj_ind); ("npars", J.Int (nat p.K.proj_npars)); ("arg", J.Int (nat p.K.proj_arg)) ] );
        ("t", term_json c) ]
  | A.Coq_tFix (mfix, idx) -> k "fix" [ ("defs", mfix_json mfix); ("idx", J.Int (nat idx)) ]
  | A.Coq_tCoFix (mfix, idx) -> k "cofix" [ ("defs", mfix_json mfix); ("idx", J.Int (nat idx)) ]
  | A.Coq_tInt i -> k "int" [ ("v", J.Str (Uint63.to_string i)) ]
  | A.Coq_tFloat f -> k "float" [ ("v", J.Str (Float64.to_hex_string f)) ]
  | A.Coq_tString s -> k "string" [ ("v", J.Str (Pstring.to_string s)) ]
  | A.Coq_tArray (u, arr, def, ty) ->
    k "array" [ ("u", level_json u); ("elems", terms arr); ("default", term_json def); ("ty", term_json ty) ]

and terms l = J.Arr (List.map term_json l)

and mfix_json m =
  J.Arr
    (List.map
       (fun (d : A.term B.def) ->
         J.Obj
           [ ("n", aname_json d.B.dname);
             ("ty", term_json d.B.dtype);
             ("body", term_json d.B.dbody);
             ("rarg", J.Int (nat d.B.rarg)) ])
       m)

(* MetaRocq contexts are snoc lists: element 0 is the innermost (last-bound) declaration. *)
let ctx_json (ctx : E.context) =
  J.Arr
    (List.map
       (fun (d : A.term B.context_decl) ->
         J.Obj
           [ ("n", aname_json d.B.decl_name); ("body", J.opt term_json d.B.decl_body); ("ty", term_json d.B.decl_type) ])
       ctx)

(* ---------- dependency edges ---------- *)

module SS = Set.Make (String)

let rec deps acc (t : A.term) =
  let ind acc (i : K.inductive) = SS.add (kn_key i.K.inductive_mind) acc in
  match t with
  | A.Coq_tRel _ | A.Coq_tVar _ | A.Coq_tSort _ | A.Coq_tInt _ | A.Coq_tFloat _ | A.Coq_tString _ -> acc
  | A.Coq_tEvar (_, args) -> List.fold_left deps acc args
  | A.Coq_tCast (a, _, b) | A.Coq_tProd (_, a, b) | A.Coq_tLambda (_, a, b) -> deps (deps acc a) b
  | A.Coq_tLetIn (_, a, b, c) -> deps (deps (deps acc a) b) c
  | A.Coq_tApp (f, args) -> List.fold_left deps (deps acc f) args
  | A.Coq_tConst (c, _) -> SS.add (kn_key c) acc
  | A.Coq_tInd (i, _) | A.Coq_tConstruct (i, _, _) -> ind acc i
  | A.Coq_tCase (ci, p, c, brs) ->
    let acc = ind acc ci.B.ci_ind in
    let acc = List.fold_left deps acc p.A.pparams in
    let acc = deps (deps acc p.A.preturn) c in
    List.fold_left (fun acc (br : A.term A.branch) -> deps acc br.A.bbody) acc brs
  | A.Coq_tProj (p, c) -> deps (ind acc p.K.proj_ind) c
  | A.Coq_tFix (m, _) | A.Coq_tCoFix (m, _) ->
    List.fold_left (fun acc (d : A.term B.def) -> deps (deps acc d.B.dtype) d.B.dbody) acc m
  | A.Coq_tArray (_, arr, d, ty) -> deps (deps (List.fold_left deps acc arr) d) ty

let ctx_deps acc (ctx : E.context) =
  List.fold_left
    (fun acc (d : A.term B.context_decl) ->
      let acc = deps acc d.B.decl_type in
      match d.B.decl_body with None -> acc | Some b -> deps acc b)
    acc ctx

let set_json s = J.Arr (List.map (fun x -> J.Str x) (SS.elements s))

(* ---------- native audit ---------- *)

let rec to_rocq_mp = function
  | K.MPfile dp -> Names.ModPath.MPfile (Names.DirPath.make (List.map (fun s -> Names.Id.of_string (bs s)) dp))
  | K.MPdot (mp, id) -> Names.ModPath.MPdot (to_rocq_mp mp, Names.Id.of_string (bs id))
  | K.MPbound _ -> raise Not_found

let to_rocq_kn ((mp, id) : K.kername) = Names.KerName.make (to_rocq_mp mp) (Names.Id.of_string (bs id))

let flags_json (f : Declarations.typing_flags) =
  let open Declarations in
  J.Obj
    [ ("check_guarded", J.Bool f.check_guarded);
      ("check_positive", J.Bool f.check_positive);
      ("check_universes", J.Bool f.check_universes);
      ("check_eliminations", J.Bool f.check_eliminations);
      ("indices_matter", J.Bool f.indices_matter);
      ("impredicative_set", J.Bool f.impredicative_set);
      ("sprop_allowed", J.Bool f.sprop_allowed);
      ("allow_uip", J.Bool f.allow_uip) ]

(* ---------- prepared environment (M5) ----------
   Two documented, kernel-validated preparations of the native environment before quotation:
   1. Sealed-module implementations: a parameter of a module sealed by a signature
      (`Module M : T. ... End M`, e.g. MathComp's HB.lock) has no body in the environment; its
      implementation's body is read from the module's structure.
   2. Lowering of `Corelib.ssr.ssreflect_rw.ssr_have_upoly` (sort-polymorphic, cannot be quoted by
      MetaRocq c18395ad): a fully applied `ssr_have_upoly P G step rest args` is replaced by its
      delta-beta reduct `rest step args`. Nothing else is changed.
   Every prepared body is re-checked by Rocq's kernel against the declared type. *)
let ssr_have_upoly = "Corelib.ssr.ssreflect_rw.ssr_have_upoly"

let rec lower c =
  match Constr.kind c with
  | Constr.App (f, args)
    when Array.length args >= 4
         && (match Constr.kind f with
             | Constr.Const (cst, _) -> Names.KerName.to_string (Names.Constant.user cst) = ssr_have_upoly
             | _ -> false) ->
    let n = Array.length args in
    Constr.mkApp (lower args.(3), Array.append [| lower args.(2) |] (Array.map lower (Array.sub args 4 (n - 4))))
  | _ -> Constr.map lower c

let sealed_impl env c =
  let cb = Environ.lookup_constant c env in
  match cb.Declarations.const_body with
  | Declarations.Undef _ ->
    let kn = Names.Constant.user c in
    (try
       match Mod_declarations.mod_expr (Environ.lookup_module (Names.KerName.modpath kn) env) with
       | Mod_declarations.Struct (_, sb) ->
         (match List.assoc_opt (Names.Label.to_id (Names.KerName.label kn)) sb with
          | Some (Declarations.SFBconst icb) -> Some icb
          | _ -> None)
       | _ -> None
     with Not_found -> None)
  | _ -> None

(* (prepared body, sealed implementation?, lowered?) *)
let prepared_body ~opaque_access env c =
  let cb = Environ.lookup_constant c env in
  let sealed, src = match sealed_impl env c with Some icb -> (true, icb) | None -> (false, cb) in
  match Global.body_of_constant_body opaque_access src with
  | None -> None
  | Some (b, _, _) ->
    let b' = lower b in
    Some (b', sealed, not (Constr.equal b b'))

let rec native_constant ~opaque_access env kn = native_constant_kn ~opaque_access env (to_rocq_kn kn)

and native_constant_kn ~opaque_access env rkn =
  match Environ.lookup_constant (Names.Constant.make1 rkn) env with
  | cb ->
    let private_univs =
      match Global.body_of_constant_body opaque_access cb with
      | Some (_, Opaqueproof.PrivateMonomorphic (), _) -> "none"
      | Some (_, Opaqueproof.PrivatePolymorphic _, _) -> "polymorphic_private"
      | None -> "no_body"
    in
    let c = Names.Constant.make1 rkn in
    let sealed, lowered =
      match prepared_body ~opaque_access env c with Some (_, s, l) -> (s, l) | None -> (false, false)
    in
    let kind =
      match cb.Declarations.const_body with
      | Declarations.Undef _ when sealed -> "sealed_implementation"
      | Declarations.Undef _ -> "assumption"
      | Declarations.Def _ -> "transparent"
      | Declarations.OpaqueDef _ -> "opaque"
      | Declarations.Primitive _ -> "primitive"
      | Declarations.Symbol _ -> "symbol"
    in
    ( Some kind,
      J.Obj
        [ ("body_kind", J.Str kind);
          ("prepared", J.Obj [ ("sealed_implementation", J.Bool sealed); ("lowered_ssr_have_upoly", J.Bool lowered) ]);
          ("polymorphic", J.Bool (Declareops.constant_is_polymorphic cb));
          ("private_universes", J.Str private_univs);
          ("typing_flags", flags_json cb.Declarations.const_typing_flags) ] )
  | exception Not_found -> (None, J.Obj [ ("error", J.Str "not found in native environment") ])

let rec native_inductive env kn = native_inductive_kn env (to_rocq_kn kn)

(* Template polymorphism as the Rocq kernel records it (Declarations.template_universes): the
   default instance (the levels MetaRocq substitutes into the quoted terms), and for each
   LocalAssum parameter in regular order whether its sort binds template levels, with every bound
   level variable named by its default level. The conclusion sort likewise. *)
and template_info_json (t : Declarations.template_universes) =
  let open Declarations in
  let level_name l = if Univ.Level.is_set l then "Set" else Univ.Level.to_string l in
  let defaults = snd (UVars.Instance.to_array t.template_defaults) in
  let univ_json u =
    J.Arr
      (List.map
         (fun (l, k) ->
           match Univ.Level.var_index l with
           | Some i when i < Array.length defaults ->
             J.Obj [ ("l", J.Str (level_name defaults.(i))); ("bound", J.Int i); ("n", J.Int k) ]
           | _ -> J.Obj [ ("l", J.Str (level_name l)); ("bound", J.Null); ("n", J.Int k) ])
         (Univ.Universe.repr u))
  in
  let sort_json (s : Sorts.t) =
    match s with
    | Sorts.SProp -> J.Obj [ ("k", J.Str "sprop") ]
    | Sorts.Prop -> J.Obj [ ("k", J.Str "prop") ]
    | Sorts.Set -> J.Obj [ ("k", J.Str "set") ]
    | Sorts.Type u -> J.Obj [ ("k", J.Str "type"); ("u", univ_json u) ]
    | Sorts.GSort (_, u) | Sorts.VSort (_, u) -> J.Obj [ ("k", J.Str "quality_sort"); ("u", univ_json u) ]
  in
  J.Obj
    [ ("defaults", J.Arr (Array.to_list (Array.map (fun l -> J.Str (level_name l)) defaults)));
      ( "param_arguments",
        J.Arr (List.map (function None -> J.Null | Some s -> sort_json s) t.template_param_arguments) );
      ("concl", sort_json t.template_concl) ]

and native_inductive_kn env rkn =
  match Environ.lookup_mind (Names.MutInd.make1 rkn) env with
  | mib ->
    let open Declarations in
    J.Obj
      [ ("polymorphic", J.Bool (Declareops.inductive_is_polymorphic mib));
        (* M6: number of *uniform* parameters (recursive occurrences use them unchanged); the others
           are non-uniform and become indices in Lean *)
        ("nparams_rec", J.Int mib.mind_nparams_rec);
        ("template", J.Bool (Option.has_some mib.mind_template));
        ( "template_info",
          match mib.mind_template with None -> J.Null | Some t -> template_info_json t );
        ( "private",
          match mib.mind_private with None -> J.Null | Some b -> J.Bool b );
        ("typing_flags", flags_json mib.mind_typing_flags) ]
  | exception Not_found -> J.Obj [ ("error", J.Str "not found in native environment") ]

(* Body state, from the native body kind and the presence of a quoted body. *)
let body_state native_kind (body : A.term option) =
  match (native_kind, body) with
  | Some "transparent", Some _ -> "transparent"
  | Some "opaque", Some _ -> "opaque_present"
  | Some "sealed_implementation", Some _ -> "sealed_implementation"
  | Some "assumption", None -> "assumption"
  | Some ("primitive" | "symbol"), _ -> "unsupported_primitive"
  | _, None -> "unavailable"
  | _, Some _ -> "inconsistent"

(* ---------- statement-only mode: bookkeeping (docs/STATEMENT_ONLY_DESIGN.md) ---------- *)

(* What the statement preparation did, by IR key: proof-valued constants exported without their
   body; obligation constants (parent definition, index); the obligations of each definition; the
   definitions whose extraction was refused (reason). *)
type stmt_info = {
  proof_only : (string, unit) Hashtbl.t;
  (* opaque data (Qed with a type that is not a proposition): the type only, with its sort; Rocq's
     kernel never unfolds it, so its body is not exported and providing a value is a task *)
  opaque_data : (string, Constr.t) Hashtbl.t;
  obligation_of : (string, string * int) Hashtbl.t;
  def_obligations : (string, string list) Hashtbl.t;
  failed : (string, string) Hashtbl.t;
  (* rewritten definitions accepted by Rocq's kernel only without the guard check: a recursive call
     whose structural argument was a proof subterm, now an obligation (termination is deferred) *)
  deferred_guard : (string, string) Hashtbl.t;
}

let new_stmt_info () =
  { proof_only = Hashtbl.create 97; opaque_data = Hashtbl.create 17; obligation_of = Hashtbl.create 97; def_obligations = Hashtbl.create 97;
    failed = Hashtbl.create 17; deferred_guard = Hashtbl.create 7 }

(* The IR key of a native kernel name (same scheme as [kn_key]). *)
let rec native_mp_key = function
  | Names.ModPath.MPfile dp -> String.concat "." (List.rev_map Names.Id.to_string (Names.DirPath.repr dp))
  | Names.ModPath.MPdot (mp, l) -> native_mp_key mp ^ "/" ^ Names.Label.to_string l
  | Names.ModPath.MPbound _ -> "%bound"

let native_kn_key kn = native_mp_key (Names.KerName.modpath kn) ^ "." ^ Names.Label.to_string (Names.KerName.label kn)
let const_key c = native_kn_key (Names.Constant.user c)

(* ---------- native universe facts ---------- *)

let level_name l = if Univ.Level.is_set l then "Set" else Univ.Level.to_string l

(* Universe levels occurring in the native kernel terms of an exported declaration. *)
let native_decl_levels ~opaque_access env (((kn : K.kername), (d : E.global_decl))) acc =
  try
    match d with
    | E.ConstantDecl _ ->
      let cb = Environ.lookup_constant (Names.Constant.make1 (to_rocq_kn kn)) env in
      let acc = Vars.universes_of_constr ~init:acc cb.Declarations.const_type in
      (match Global.body_of_constant_body opaque_access cb with
       | Some (c, _, _) -> Vars.universes_of_constr ~init:acc c
       | None -> acc)
    | E.InductiveDecl _ ->
      let mib = Environ.lookup_mind (Names.MutInd.make1 (to_rocq_kn kn)) env in
      (* Template inductives: MetaRocq quotes them at their default instance (template_defaults),
         so those default levels are part of the export. *)
      let acc =
        match mib.Declarations.mind_template with
        | Some t ->
          Array.fold_left (fun acc l -> Univ.Level.Set.add l acc) acc
            (snd (UVars.Instance.to_array t.Declarations.template_defaults))
        | None -> acc
      in
      Array.fold_left
        (fun acc oib ->
          let acc = Vars.universes_of_constr ~init:acc oib.Declarations.mind_user_arity in
          Array.fold_left (fun acc c -> Vars.universes_of_constr ~init:acc c) acc oib.Declarations.mind_user_lc)
        acc mib.Declarations.mind_packets
  with Not_found -> acc

let native_relation g a b =
  let u = Univ.Universe.make in
  if UGraph.check_leq g (Univ.Universe.super (u a)) (u b) then "lt"
  else if UGraph.check_leq g (u a) (u b) then "le"
  else "none"

(* Pairwise native relations (from the loaded environment's universe graph) between Set and
   every global level occurring in the exported declarations. *)
let universe_facts_json ~opaque_access env decls =
  let lv = List.fold_left (fun acc d -> native_decl_levels ~opaque_access env d acc) Univ.Level.Set.empty decls in
  let lv = Univ.Level.Set.filter (fun l -> not (Univ.Level.is_set l) && Univ.Level.var_index l = None) lv in
  let levels = Univ.Level.set :: Univ.Level.Set.elements lv in
  let g = Environ.universes env in
  let rels =
    List.concat_map
      (fun a ->
        List.filter_map
          (fun b ->
            if Univ.Level.equal a b then None
            else
              match native_relation g a b with
              | "none" -> None
              | r -> Some (J.Obj [ ("l", J.Str (level_name a)); ("rel", J.Str r); ("r", J.Str (level_name b)) ]))
          levels)
      levels
  in
  J.Obj
    [ ("kind", J.Str "universe_facts");
      ("levels", J.Arr (List.map (fun l -> J.Str (level_name l)) (List.tl levels)));
      ("relations", J.Arr rels);
      ("source", J.Str "native UGraph.check_leq on the loaded environment; pairwise over Set and all levels of the export") ]

(* Rocq2Lean CheckRelation "a" "b" "lt|le|none": re-check one fact against the native graph of a
   fresh process. Names are resolved through the graph's own domain (no string parsing). *)
let check_relation a b want =
  let g = Environ.universes (Global.env ()) in
  let by_name = Hashtbl.create 97 in
  Univ.Level.Set.iter (fun l -> Hashtbl.replace by_name (level_name l) l) (UGraph.domain g);
  Hashtbl.replace by_name "Set" Univ.Level.set;
  match (Hashtbl.find_opt by_name a, Hashtbl.find_opt by_name b) with
  | Some la, Some lb ->
    let got = if a = b then "eq" else native_relation g la lb in
    if got = want then Feedback.msg_info Pp.(str ("UREL_OK " ^ a ^ " " ^ b ^ " " ^ want))
    else Feedback.msg_info Pp.(str ("UREL_MISMATCH " ^ a ^ " " ^ b ^ " expected=" ^ want ^ " native=" ^ got))
  | _ -> Feedback.msg_info Pp.(str ("UREL_UNKNOWN " ^ a ^ " " ^ b))

(* Rocq2Lean NativeMeta "key" "constant|inductive": recompute the native metadata of one
   declaration in a fresh process. Keys are parsed back to kernel names (IR_SPEC "Keys"). *)
let kername_of_key key =
  let i = String.rindex key '.' in
  let mp_s = String.sub key 0 i and id = String.sub key (i + 1) (String.length key - i - 1) in
  let parts = String.split_on_char '/' mp_s in
  let file = List.hd parts in
  let dp = Names.DirPath.make (List.rev_map Names.Id.of_string (String.split_on_char '.' file)) in
  let mp =
    List.fold_left (fun mp f -> Names.ModPath.MPdot (mp, Names.Id.of_string f)) (Names.ModPath.MPfile dp) (List.tl parts)
  in
  Names.KerName.make mp (Names.Id.of_string id)

let native_meta ~opaque_access key kind =
  let env = Global.env () in
  let j =
    try
      let rkn = kername_of_key key in
      match kind with
      | "constant" -> snd (native_constant_kn ~opaque_access env rkn)
      | _ -> native_inductive_kn env rkn
    with e -> J.Obj [ ("error", J.Str (Printexc.to_string e)) ]
  in
  Feedback.msg_info Pp.(str ("NATIVE_META " ^ key ^ " " ^ J.to_string j))

(* ---------- declarations ---------- *)

let finite_json = function B.Finite -> J.Str "Finite" | B.CoFinite -> J.Str "CoFinite" | B.BiFinite -> J.Str "BiFinite"

let kelim_json = function
  | U.IntoSProp -> J.Str "IntoSProp"
  | U.IntoPropSProp -> J.Str "IntoPropSProp"
  | U.IntoSetPropSProp -> J.Str "IntoSetPropSProp"
  | U.IntoAny -> J.Str "IntoAny"

let variance_json = function
  | U.Variance.Irrelevant -> J.Str "irrelevant"
  | U.Variance.Covariant -> J.Str "covariant"
  | U.Variance.Invariant -> J.Str "invariant"

let decl_json ?stmt ~opaque_access env ((kn : K.kername), (d : E.global_decl)) =
  let key = kn_key kn in
  let ident = [ ("name", J.Str key); ("mp", mp_json (fst kn)); ("id", J.Str (bs (snd kn))) ] in
  match d with
  | E.ConstantDecl cb ->
    (* native metadata always from the original environment (not the prepared one): body kind,
       sealed implementation / lowering provenance, typing flags; an obligation constant exists only
       in the prepared environment (statement mode) *)
    let native_kind, native =
      match stmt with
      | Some st when Hashtbl.mem st.obligation_of key ->
        (* an obligation is checked under its parent definition's typing flags *)
        let parent, k = Hashtbl.find st.obligation_of key in
        let flags =
          match Environ.lookup_constant (Names.Constant.make1 (kername_of_key parent)) (Global.env ()) with
          | pcb -> flags_json pcb.Declarations.const_typing_flags
          | exception Not_found -> J.Null
        in
        (Some "obligation",
         J.Obj [ ("obligation", J.Obj [ ("of", J.Str parent); ("index", J.Int k) ]); ("typing_flags", flags) ])
      | _ -> native_constant ~opaque_access (Global.env ()) kn
    in
    let state =
      match stmt with
      | Some st when Hashtbl.mem st.obligation_of key -> "obligation"
      | Some st when Hashtbl.mem st.proof_only key -> "statement_only"
      | Some st when Hashtbl.mem st.opaque_data key -> "opaque_interface"
      | Some st when Hashtbl.mem st.failed key -> "obligation_extraction_failed"
      | _ -> body_state native_kind cb.E.cst_body
    in
    let stmt_fields =
      match stmt with
      | Some st when Hashtbl.mem st.def_obligations key ->
        [ ("obligations", J.Arr (List.map (fun o -> J.Str o) (Hashtbl.find st.def_obligations key))) ]
      | Some st when Hashtbl.mem st.failed key -> [ ("extraction_refused", J.Str (Hashtbl.find st.failed key)) ]
      | _ -> []
    in
    let stmt_fields =
      match stmt with
      | Some st when Hashtbl.mem st.deferred_guard key ->
        stmt_fields @ [ ("termination", J.Obj [ ("state", J.Str "deferred"); ("guard_error", J.Str (Hashtbl.find st.deferred_guard key)) ]) ]
      | _ -> stmt_fields
    in
    let stmt_fields =
      match stmt with
      | Some st when Hashtbl.mem st.opaque_data key ->
        let sigma = Evd.from_env env in
        stmt_fields
        @ [ ("type_sort", term_json (snd (Ast_quoter.quote_term_rec ~bypass:true ~opaque_access env sigma (Hashtbl.find st.opaque_data key)))) ]
      | _ -> stmt_fields
    in
    let tdeps = deps SS.empty cb.E.cst_type in
    let bdeps = match cb.E.cst_body with None -> SS.empty | Some b -> deps SS.empty b in
    J.Obj
      ((("kind", J.Str "constant") :: ident)
      @ [ ("type", term_json cb.E.cst_type);
          ("body", J.opt term_json cb.E.cst_body);
          ("body_state", J.Str state);
          ("universes", udecl_json cb.E.cst_universes);
          ("relevance", rel_json cb.E.cst_relevance);
          ("deps", J.Obj [ ("type", set_json (SS.remove key tdeps)); ("body", set_json (SS.remove key bdeps)) ]);
          ("native", native) ]
      @ stmt_fields)
  | E.InductiveDecl mib ->
    let body_json (ob : E.one_inductive_body) =
      J.Obj
        [ ("name", J.Str (bs ob.E.ind_name));
          ("indices", ctx_json ob.E.ind_indices);
          ("sort", sort_json ob.E.ind_sort);
          ("type", term_json ob.E.ind_type);
          ("kelim", kelim_json ob.E.ind_kelim);
          ( "ctors",
            J.Arr
              (List.map
                 (fun (c : E.constructor_body) ->
                   J.Obj
                     [ ("name", J.Str (bs c.E.cstr_name));
                       ("args", ctx_json c.E.cstr_args);
                       ("indices", terms c.E.cstr_indices);
                       ("type", term_json c.E.cstr_type);
                       ("arity", J.Int (nat c.E.cstr_arity)) ])
                 ob.E.ind_ctors) );
          ( "projs",
            J.Arr
              (List.map
                 (fun (p : E.projection_body) ->
                   J.Obj
                     [ ("name", J.Str (bs p.E.proj_name)); ("r", rel_json p.E.proj_relevance); ("type", term_json p.E.proj_type) ])
                 ob.E.ind_projs) );
          ("r", rel_json ob.E.ind_relevance) ]
    in
    let tdeps =
      List.fold_left
        (fun acc (ob : E.one_inductive_body) ->
          let acc = deps (ctx_deps acc ob.E.ind_indices) ob.E.ind_type in
          let acc =
            List.fold_left
              (fun acc (c : E.constructor_body) ->
                List.fold_left deps (deps (ctx_deps acc c.E.cstr_args) c.E.cstr_type) c.E.cstr_indices)
              acc ob.E.ind_ctors
          in
          List.fold_left (fun acc (p : E.projection_body) -> deps acc p.E.proj_type) acc ob.E.ind_projs)
        (ctx_deps SS.empty mib.E.ind_params) mib.E.ind_bodies
    in
    J.Obj
      ((("kind", J.Str "inductive") :: ident)
      @ [ ("finite", finite_json mib.E.ind_finite);
          ("npars", J.Int (nat mib.E.ind_npars));
          ("params", ctx_json mib.E.ind_params);
          ("bodies", J.Arr (List.map body_json mib.E.ind_bodies));
          ("universes", udecl_json mib.E.ind_universes);
          ("variance", J.opt (fun l -> J.Arr (List.map variance_json l)) mib.E.ind_variance);
          ("deps", J.Obj [ ("type", set_json (SS.remove key tdeps)) ]);
          ("native", native_inductive (Global.env ()) kn) ])

(* ---------- driver ---------- *)

let root_constr env (gr : Names.GlobRef.t) =
  match gr with
  | Names.GlobRef.ConstRef cst ->
    let cb = Environ.lookup_constant cst env in
    Constr.mkConstU (cst, UVars.make_abstract_instance (Declareops.constant_polymorphic_context cb))
  | Names.GlobRef.IndRef ind ->
    let mib = Environ.lookup_mind (fst ind) env in
    Constr.mkIndU (ind, UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib))
  | Names.GlobRef.ConstructRef c ->
    let mib = Environ.lookup_mind (fst (fst c)) env in
    Constr.mkConstructU (c, UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib))
  | Names.GlobRef.VarRef _ -> CErrors.user_err Pp.(str "Rocq2Lean Export: a section variable cannot be a root")

let rec mp_file = function
  | K.MPfile dp -> Some dp
  | K.MPdot (mp, _) -> mp_file mp
  | K.MPbound _ -> None

(* ---------- native closure scan (quotability, before MetaRocq quoting) ----------
   MetaRocq c18395ad cannot quote a declaration whose universe context binds sort qualities (Rocq
   9.x sort polymorphism); [quote_term_rec] then aborts the whole export. The scan walks each root's
   native dependency closure (types, bodies incl. opaque ones, inductive arities and constructors)
   and reports the first such declaration with its dependency path, so that the CLI can report a
   precise blocker instead of an opaque failure. *)
let gref_name = function
  | Names.GlobRef.ConstRef c -> Names.KerName.to_string (Names.Constant.user c)
  | Names.GlobRef.IndRef (m, _) -> Names.KerName.to_string (Names.MutInd.user m)
  | _ -> "?"

let gref_key g = (match g with Names.GlobRef.ConstRef _ -> "c:" | _ -> "i:") ^ gref_name g

let rec constr_refs acc c =
  let acc =
    match Constr.kind c with
    | Constr.Const (cst, _) -> Names.GlobRef.ConstRef cst :: acc
    | Constr.Ind ((m, _), _) -> Names.GlobRef.IndRef (m, 0) :: acc
    | Constr.Construct (((m, _), _), _) -> Names.GlobRef.IndRef (m, 0) :: acc
    | Constr.Case (ci, _, _, _, _, _, _) -> Names.GlobRef.IndRef (fst ci.Constr.ci_ind, 0) :: acc
    | Constr.Proj (p, _, _) -> Names.GlobRef.IndRef (fst (Names.Projection.inductive p), 0) :: acc
    | _ -> acc
  in
  Constr.fold constr_refs acc c

let decl_refs ~opaque_access env = function
  | Names.GlobRef.ConstRef c ->
    let cb = Environ.lookup_constant c env in
    let acc = constr_refs [] cb.Declarations.const_type in
    (match Global.body_of_constant_body opaque_access cb with Some (b, _, _) -> constr_refs acc b | None -> acc)
  | Names.GlobRef.IndRef (m, _) ->
    let mib = Environ.lookup_mind m env in
    Array.fold_left
      (fun acc oib ->
        Array.fold_left constr_refs (constr_refs acc oib.Declarations.mind_user_arity) oib.Declarations.mind_user_lc)
      [] mib.Declarations.mind_packets
  | _ -> []

(* Number of sort-quality variables bound by a polymorphic declaration (None if monomorphic). *)
let sort_qualities env = function
  | Names.GlobRef.ConstRef c ->
    (match (Environ.lookup_constant c env).Declarations.const_universes with
     | Declarations.Polymorphic a -> Some (fst (UVars.AbstractContext.size a))
     | _ -> None)
  | Names.GlobRef.IndRef (m, _) ->
    (match (Environ.lookup_mind m env).Declarations.mind_universes with
     | Declarations.Polymorphic a -> Some (fst (UVars.AbstractContext.size a))
     | _ -> None)
  | _ -> None

let scan_root ~opaque_access env root =
  let parent = Hashtbl.create 97 and q = Queue.create () and found = ref None in
  Hashtbl.replace parent (gref_key root) None;
  Queue.add root q;
  while Option.is_empty !found && not (Queue.is_empty q) do
    let g = Queue.pop q in
    match sort_qualities env g with
    | Some nq when nq > 0 -> found := Some g
    | _ ->
      List.iter
        (fun d ->
          let k = gref_key d in
          if not (Hashtbl.mem parent k) then begin Hashtbl.replace parent k (Some g); Queue.add d q end)
        (decl_refs ~opaque_access env g)
  done;
  match !found with
  | None -> None
  | Some g ->
    let rec path g acc =
      match Hashtbl.find parent (gref_key g) with None -> g :: acc | Some p -> path p (g :: acc)
    in
    Some (path g [])

(* The prepared environment for a set of roots: every constant of the (prepared) closure with a sealed
   implementation or a lowering gets its prepared body; then each prepared body is re-checked by the
   kernel against its declared type (after all replacements, so that a sealed `unlock := erefl`
   sees its transparent `body`). *)
let prepare_env ~opaque_access env0 roots =
  let env = ref env0 and seen = Hashtbl.create 97 and q = Queue.create () and changed = ref [] in
  List.iter (fun g -> Queue.add g q) roots;
  while not (Queue.is_empty q) do
    let g = Queue.pop q in
    let k = gref_key g in
    if not (Hashtbl.mem seen k) then begin
      Hashtbl.add seen k ();
      (match g with
       | Names.GlobRef.ConstRef c ->
         (match prepared_body ~opaque_access !env c with
          | Some (b', sealed, lowered) when sealed || lowered ->
            let cb = Environ.lookup_constant c !env in
            env := Environ.add_constant c { cb with Declarations.const_body = Declarations.Def b' } !env;
            changed := (g, b', cb.Declarations.const_type) :: !changed
          | _ -> ())
       | _ -> ());
      List.iter (fun d -> Queue.add d q) (decl_refs ~opaque_access !env g)
    end
  done;
  List.iter
    (fun (g, b', ty) ->
      let ok =
        try
          let j = Typeops.infer !env b' in
          Conversion.conv_leq !env j.Environ.uj_type ty = Ok ()
        with _ -> false
      in
      if not ok then
        CErrors.user_err Pp.(str ("ROCQ2LEAN_PREPARE: the prepared body of " ^ gref_name g ^ " is not accepted by the kernel at its declared type")))
    !changed;
  !env

(* ---------- statement-only preparation (docs/STATEMENT_ONLY_DESIGN.md) ----------
   A constant is proof-valued when the sort of its type is Prop or SProp (Rocq's kernel decides,
   not the keyword). The statement environment keeps every kept term's proofs out:
   * a proof-valued constant keeps its type and loses its body (statement only);
   * in every kept term (a type, or the body of a constant that is not a proof) each maximal proof
     subterm t, in local context G, is replaced by [o G], where [o : forall G, T] is a new obligation
     constant (parameter) of the declaration; a proof subterm that is a proof-valued constant [c]
     stays as a reference to [c] (its statement is a task of its own); local variables stay;
   * the rewritten body must type-check against the rewritten type with Rocq's kernel, the
     obligations being parameters; otherwise the definition is exported without a body and the
     refusal is recorded (never silently kept). *)

let is_proof_type env sigma ty =
  match Retyping.get_sort_quality_of env sigma ty with
  | Sorts.Quality.QConstant (Sorts.Quality.QProp | Sorts.Quality.QSProp) -> true
  | _ -> false

let proof_valued env c =
  let cb = Environ.lookup_constant c env in
  let sigma = Evd.from_env env in
  try is_proof_type env sigma (EConstr.of_constr cb.Declarations.const_type) with _ -> false

(* A stable, environment-free description of why Rocq's kernel refused a rewritten declaration. *)
let refusal_reason e =
  let open Type_errors in
  match e with
  | TypeError (_, err) -> (
    "kernel type error: "
    ^
    match err with
    | IllFormedRecBody (FixGuardError g, _, i, _, _) ->
      "ill-formed recursive definition (fixpoint " ^ string_of_int i ^ "): "
      ^ (match g with
         | NotEnoughAbstractionInFixBody _ -> "not enough abstractions"
         | RecursionNotOnInductiveType _ -> "recursion not on an inductive type"
         | RecursionOnIllegalTerm (k, _, _) -> "recursive call " ^ string_of_int k ^ " on a term that is not a structural subterm"
         | NotEnoughArgumentsForFixCall k -> "recursive call " ^ string_of_int k ^ " with too few arguments"
         | FixpointOnNonEliminable _ -> "fixpoint on a non-eliminable type")
    | IllFormedRecBody (CoFixGuardError _, _, _, _, _) -> "ill-formed corecursive definition"
    | IllTypedRecBody _ -> "ill-typed recursive body"
    | ActualType _ -> "actual type mismatch"
    | CantApplyBadType _ -> "application to an argument of the wrong type"
    | CantApplyNonFunctional _ -> "application of a non-function"
    | UnsatisfiedUnivConstraints _ | UnsatisfiedPConstraints _ -> "universe constraints not satisfied"
    | UndeclaredUniverses _ | UndeclaredQualities _ -> "undeclared universe levels or qualities"
    | ElimArity _ -> "elimination not allowed"
    | BadCaseRelevance _ | BadBinderRelevance _ -> "relevance mismatch"
    | IllFormedBranch _ -> "ill-formed branch"
    | _ -> "other")
  | Failure m -> m
  | e -> Printexc.to_string e

(* Replace the maximal proof subterms of [t] (closed in [env0]) by applications of fresh obligations;
   [mk stmt] returns the obligation constant for the closed statement [stmt].
   The statement of an obligation is the type its position *expects* — the domain of the applied
   function at that argument (after the preceding, already rewritten, arguments), or the declared
   type of a let — not the type inferred from the proof: the inferred type depends on how the proof
   was written (a convertible variant, e.g. a beta-redex left by a tactic), the expected type only on
   the surrounding definition. Statements are beta-normalized. Elsewhere (no expected type at hand)
   the inferred type is used. *)
let extract_proofs env0 sigma mk t =
  let canon env ty = Reductionops.nf_beta env sigma ty in
  let is_proof env t = try is_proof_type env sigma (Retyping.get_type_of env sigma t) with _ -> false in
  let extract env ty t =
    match EConstr.kind sigma t with
    | Constr.Const (c, _) when proof_valued env c -> t
    | _ ->
      let ctx = EConstr.rel_context env in
      let o = mk (EConstr.it_mkProd_or_LetIn (canon env ty) ctx) in
      EConstr.mkApp (o, Context.Rel.instance EConstr.mkRel 0 ctx)
  in
  let rec go env t =
    match EConstr.kind sigma t with
    | Constr.Rel _ | Constr.Var _ | Constr.Sort _ | Constr.Meta _ | Constr.Evar _ -> t
    | _ when is_proof env t -> extract env (Retyping.get_type_of env sigma t) t
    | Constr.App (f, args) ->
      let f' = go env f in
      let fty = ref (try Some (Retyping.get_type_of env sigma f') with _ -> None) in
      let args' =
        Array.map
          (fun a ->
            let dom_cod =
              match !fty with
              | None -> None
              | Some ty -> (
                let ty = match EConstr.kind sigma ty with Constr.Prod _ -> ty | _ -> Reductionops.whd_all env sigma ty in
                match EConstr.kind sigma ty with Constr.Prod (_, d, b) -> Some (d, b) | _ -> None)
            in
            let a' =
              match dom_cod with
              | Some (d, _) when is_proof env a -> extract env d a
              | _ -> go env a
            in
            fty := (match dom_cod with Some (_, b) -> Some (EConstr.Vars.subst1 a' b) | None -> None);
            a')
          args
      in
      EConstr.mkApp (f', args')
    | Constr.LetIn (na, v, ty, b) ->
      let ty' = go env ty in
      let v' = if is_proof env v then extract env ty' v else go env v in
      EConstr.mkLetIn (na, v', ty', go (EConstr.push_rel (Context.Rel.Declaration.LocalDef (na, v', ty')) env) b)
    | _ -> Termops.map_constr_with_full_binders env sigma EConstr.push_rel go env t
  in
  go env0 t

(* The statement environment for [roots], recording what was done in [st]. *)
let statement_env ?(follow = true) ~opaque_access st env0 roots =
  let env = ref env0 and seen = Hashtbl.create 97 and q = Queue.create () in
  List.iter (fun g -> Queue.add g q) roots;
  while not (Queue.is_empty q) do
    let g = Queue.pop q in
    let k = gref_key g in
    if not (Hashtbl.mem seen k) then begin
      Hashtbl.add seen k ();
      (match g with
       | Names.GlobRef.ConstRef c when not (Hashtbl.mem st.obligation_of (const_key c)) ->
         (* rewritten against the fixed base environment (never against earlier rewrites): the
            result for a constant does not depend on the request or on the walk order *)
         let cb = Environ.lookup_constant c env0 in
         let key = const_key c in
         let sigma = Evd.from_env env0 in
         let poly = Declareops.constant_is_polymorphic cb in
         let inst =
           if poly then EConstr.EInstance.make (UVars.make_abstract_instance (Declareops.constant_polymorphic_context cb))
           else EConstr.EInstance.empty
         in
         let obls = ref [] and n = ref 0 in
         let mk stmt =
           incr n;
           let lbl = Names.Label.to_string (Names.Constant.label c) ^ "__rocq2lean_obligation_" ^ string_of_int !n in
           let o = Names.Constant.make1 (Names.KerName.make (Names.Constant.modpath c) (Names.Label.make lbl)) in
           obls := (o, EConstr.to_constr sigma stmt) :: !obls;
           EConstr.mkConstU (o, inst)
         in
         let is_proof = proof_valued env0 c in
         (* opacity as declared in Rocq (the native environment): the preparation may have replaced
            an opaque body by its lowered form, which does not make it transparent *)
         let is_opaque_data =
           (not is_proof)
           && (match (Environ.lookup_constant c (Global.env ())).Declarations.const_body with
               | Declarations.OpaqueDef _ -> true
               | _ -> false
               | exception Not_found -> false)
         in
         let ty' = EConstr.to_constr sigma (extract_proofs env0 sigma mk (EConstr.of_constr cb.Declarations.const_type)) in
         let body' =
           if is_proof || is_opaque_data then None
           else
             match Global.body_of_constant_body opaque_access cb with
             | None -> None
             | Some (b, _, _) -> Some (EConstr.to_constr sigma (extract_proofs env0 sigma mk (EConstr.of_constr b)))
         in
         let obls = List.rev !obls in
         (* the obligations, as parameters, then Rocq's kernel re-check of the rewritten declaration *)
         let add_obls e =
           List.fold_left
             (fun e (o, stmt) ->
               Environ.add_constant o
                 { cb with Declarations.const_body = Declarations.Undef None; const_type = stmt;
                           const_relevance = Sorts.Relevant; const_hyps = [] }
                 e)
             e obls
         in
         (* a polymorphic constant is re-checked under its abstract universe context (De Bruijn
            universe variables), as Rocq's checker does *)
         let env' =
           if poly then Environ.push_context ~strict:false (UVars.AbstractContext.repr (Declareops.constant_polymorphic_context cb)) (add_obls env0)
           else add_obls env0
         in
         (* the constant's own typing flags, as when Rocq checked it *)
         let flags = cb.Declarations.const_typing_flags in
         let env' = Environ.set_typing_flags flags env' in
         let check env' =
           try
             let _ = Typeops.infer_type env' ty' in
             List.iter (fun (_, stmt) -> ignore (Typeops.infer_type env' stmt)) obls;
             (match body' with
              | Some b ->
                let j = Typeops.infer env' b in
                if Conversion.conv_leq env' j.Environ.uj_type ty' <> Ok () then failwith "rewritten body does not have the rewritten type"
              | None -> ());
             None
           with e -> Some (e, refusal_reason e)
         in
         let checked =
           match check env' with
           | None -> None
           | Some (Type_errors.TypeError (_, Type_errors.IllFormedRecBody (Type_errors.FixGuardError (Type_errors.RecursionOnIllegalTerm _), _, _, _, _)), why)
             when flags.Declarations.check_guarded && not is_proof ->
             (* Rocq accepted the original under the guard check; the rewritten body differs only in
                proof subterms, one of which was a recursive call's structural argument. Re-check
                everything but the guard; termination becomes an explicit obligation of the
                translation (never assumed). *)
             (match check (Environ.set_typing_flags { flags with Declarations.check_guarded = false } env') with
              | None -> Hashtbl.replace st.deferred_guard key why; None
              | Some (_, why') -> Some why')
           | Some (_, why) -> Some why
         in
         (match checked with
          | Some why when not is_proof ->
            (* refused: exported without a body, statement deps only *)
            Hashtbl.replace st.failed key why;
            env := Environ.add_constant c { cb with Declarations.const_body = Declarations.Undef None } !env
          | Some why ->
            Hashtbl.replace st.failed key why;
            Hashtbl.replace st.proof_only key ();
            env := Environ.add_constant c { cb with Declarations.const_body = Declarations.Undef None } !env
          | None ->
            env := add_obls !env;
            List.iteri (fun i (o, _) -> Hashtbl.replace st.obligation_of (const_key o) (key, i + 1)) obls;
            if obls <> [] then Hashtbl.replace st.def_obligations key (List.map (fun (o, _) -> const_key o) obls);
            if is_proof then Hashtbl.replace st.proof_only key ();
            if is_opaque_data then
              Hashtbl.replace st.opaque_data key
                (EConstr.to_constr sigma (EConstr.mkSort (Retyping.get_sort_of env' sigma (EConstr.of_constr ty'))));
            let body = match body' with Some b -> Declarations.Def b | None -> Declarations.Undef None in
            env := Environ.add_constant c { cb with Declarations.const_type = ty'; const_body = body } !env;
            List.iter (fun (o, _) -> Queue.add (Names.GlobRef.ConstRef o) q) obls)
       | _ -> ());
      if follow then List.iter (fun d -> Queue.add d q) (decl_refs ~opaque_access !env g)
    end
  done;
  !env

let statement_env_one ~opaque_access st env c =
  statement_env ~follow:false ~opaque_access st env [ Names.GlobRef.ConstRef c ]

let export_in ?stmt ~opaque_access env file (roots : Libnames.qualid list) =
  let sigma = Evd.from_env env in
  let blocked =
    List.filter_map
      (fun qid ->
        match scan_root ~opaque_access env (Nametab.global qid) with
        | Some p -> Some (qid, p)
        | None -> None)
      roots
  in
  if blocked <> [] then begin
    let oc = open_out (file ^ ".blockers.json") in
    output_string oc
      (J.to_string
         (J.Obj
            [ ("kind", J.Str "unquotable");
              ( "reason",
                J.Str "sort-polymorphic universe context: MetaRocq c18395ad cannot quote it" );
              ( "roots",
                J.Arr
                  (List.map
                     (fun (qid, p) ->
                       J.Obj
                         [ ("requested", J.Str (Libnames.string_of_qualid qid));
                           ("path", J.Arr (List.map (fun g -> J.Str (gref_name g)) p)) ])
                     blocked) ) ]));
    close_out oc;
    CErrors.user_err
      Pp.(str "ROCQ2LEAN_UNQUOTABLE: " ++ int (List.length blocked)
          ++ str " root(s) depend on a sort-polymorphic declaration; see " ++ str file ++ str ".blockers.json")
  end;
  let quoted =
    List.map
      (fun qid ->
        let gr = Nametab.global qid in
        let (genv, t) : E.program =
          Ast_quoter.quote_term_rec ~bypass:true ~opaque_access env sigma (root_constr env gr)
        in
        (qid, genv, t))
      roots
  in
  (* Merge the per-root environments; each MetaRocq environment is newest-first, so reversing
     yields dependencies before dependents. *)
  let seen = Hashtbl.create 97 in
  let order = ref [] in
  List.iter
    (fun (_, (genv : E.global_env), _) ->
      List.iter
        (fun ((kn, _) as d) ->
          let key = kn_key kn in
          if not (Hashtbl.mem seen key) then begin
            Hashtbl.add seen key ();
            order := d :: !order
          end)
        (List.rev genv.E.declarations))
    quoted;
  let decls = List.rev !order in
  let levels = Hashtbl.create 17 and constraints = Hashtbl.create 17 in
  let add tbl j = let s = J.to_string j in if not (Hashtbl.mem tbl s) then Hashtbl.add tbl s j in
  List.iter
    (fun (_, (genv : E.global_env), _) ->
      let lvls, cstrs = genv.E.universes in
      List.iter (fun l -> add levels (level_json l)) (U.LevelSet.elements lvls);
      List.iter (fun c -> add constraints (constraint_json c)) (U.ConstraintSet.elements cstrs))
    quoted;
  let sorted tbl = List.sort compare (Hashtbl.fold (fun s _ acc -> s :: acc) tbl []) |> List.map (Hashtbl.find tbl) in
  let libs =
    List.sort_uniq compare
      (List.filter_map (fun ((mp, _), _) -> Option.map (fun dp -> List.map bs dp) (mp_file mp)) decls)
  in
  let lib_json dp =
    let rdp = Names.DirPath.make (List.map Names.Id.of_string dp) in
    let vo = match Loadpath.locate_absolute_library rdp with Ok f -> J.Str f | Error _ -> J.Null in
    J.Obj [ ("dirpath", J.Str (String.concat "." (List.rev dp))); ("vo", vo) ]
  in
  let header =
    J.Obj
      [ ("kind", J.Str "header");
        ("ir", J.Str ir_version);
        ( "frontend",
          J.Obj
            [ ("name", J.Str "metarocq-template");
              ("metarocq_commit", J.Str metarocq_commit);
              ("quoter", J.Str "Ast_quoter.quote_term_rec ~bypass:true");
              ("opaque_access", J.Str "vernac STATE opaque_access") ] );
        ("rocq_version", J.Str Coq_config.version);
        ("ocaml_version", J.Str Sys.ocaml_version);
        ("global_typing_flags", flags_json (Environ.typing_flags env));
        ( "mode",
          match stmt with
          | None -> J.Str "proof"
          | Some st ->
            J.Obj
              [ ("name", J.Str "statement");
                ("proof_only", J.Int (Hashtbl.length st.proof_only));
                ("obligations", J.Int (Hashtbl.length st.obligation_of));
                ( "extraction_refused",
                  J.Obj (List.sort compare (Hashtbl.fold (fun k v acc -> (k, J.Str v) :: acc) st.failed [])) );
                ( "termination_deferred",
                  J.Arr (List.map (fun k -> J.Str k) (List.sort compare (Hashtbl.fold (fun k _ acc -> k :: acc) st.deferred_guard []))) ) ] );
        ( "conventions",
          J.Obj
            [ ("bvar", J.Str "MetaRocq tRel n = IR rel n, 0 = innermost binder");
              ("contexts", J.Str "arrays innermost-first (MetaRocq snoc order)");
              ("ctor_index", J.Str "0-based");
              ("dirpaths", J.Str "outer-first");
              ("case", J.Str "MetaRocq compact case: pcontext/bcontext carry names only") ] ) ]
  in
  let roots_json =
    J.Obj
      [ ("kind", J.Str "roots");
        ( "roots",
          J.Arr
            (List.map
               (fun (qid, _, t) ->
                 let name =
                   match t with
                   | A.Coq_tConst (c, _) -> J.Str (kn_key c)
                   | A.Coq_tInd (i, _) | A.Coq_tConstruct (i, _, _) -> J.Str (kn_key i.K.inductive_mind)
                   | _ -> J.Null
                 in
                 J.Obj [ ("requested", J.Str (Libnames.string_of_qualid qid)); ("name", name); ("term", term_json t) ])
               quoted) ) ]
  in
  let oc = open_out_bin file in
  let line j = output_string oc (J.to_string j); output_char oc '\n' in
  line header;
  line roots_json;
  line (J.Obj [ ("kind", J.Str "libraries"); ("libraries", J.Arr (List.map lib_json libs)) ]);
  line (J.Obj [ ("kind", J.Str "universes"); ("levels", J.Arr (sorted levels)); ("constraints", J.Arr (sorted constraints)) ]);
  line (universe_facts_json ~opaque_access env decls);
  List.iter (fun d -> line (decl_json ?stmt ~opaque_access env d)) decls;
  line (J.Obj [ ("kind", J.Str "footer"); ("declarations", J.Int (List.length decls)) ]);
  close_out oc;
  Feedback.msg_info
    Pp.(str "Rocq2Lean Export: wrote " ++ int (List.length decls) ++ str " declarations for "
        ++ int (List.length roots) ++ str " root(s) to " ++ str file)

let export ~opaque_access file (roots : Libnames.qualid list) =
  let env = prepare_env ~opaque_access (Global.env ()) (List.map Nametab.global roots) in
  export_in ~opaque_access env file roots

(* Statement-only export: the statement environment of the roots (after the usual preparation). *)
let export_statements ~opaque_access file (roots : Libnames.qualid list) =
  let grefs = List.map Nametab.global roots in
  let env = prepare_env ~opaque_access (Global.env ()) grefs in
  let st = new_stmt_info () in
  let env = statement_env ~opaque_access st env grefs in
  export_in ~stmt:st ~opaque_access env file roots

(* Round trip of the statement preparation: a fresh process re-prepares one constant alone and
   prints its rewritten type and body and its obligations (quoted), to be compared with the IR. *)
let check_statement_prepared ~opaque_access key =
  let c = Names.Constant.make1 (kername_of_key key) in
  let env = prepare_env ~opaque_access (Global.env ()) [ Names.GlobRef.ConstRef c ] in
  let st = new_stmt_info () in
  (* only this constant: stop the closure walk after it *)
  let env' = statement_env_one ~opaque_access st env c in
  let sigma = Evd.from_env env' in
  let q t = term_json (snd (Ast_quoter.quote_term_rec ~bypass:true ~opaque_access env' sigma t)) in
  let cb = Environ.lookup_constant c env' in
  let body = match cb.Declarations.const_body with Declarations.Def b -> q b | _ -> J.Null in
  let obls =
    match Hashtbl.find_opt st.def_obligations key with
    | None -> []
    | Some os ->
      List.map
        (fun o -> J.Obj [ ("name", J.Str o); ("type", q (Environ.lookup_constant (Names.Constant.make1 (kername_of_key o)) env').Declarations.const_type) ])
        os
  in
  let state =
    if Hashtbl.mem st.failed key && not (Hashtbl.mem st.proof_only key) then "obligation_extraction_failed"
    else if Hashtbl.mem st.proof_only key then "statement_only"
    else if Hashtbl.mem st.opaque_data key then "opaque_interface" else "kept"
  in
  Feedback.msg_info
    Pp.(str ("STATEMENT " ^ key ^ " " ^ J.to_string (J.Obj [ ("type", q cb.Declarations.const_type); ("body", body);
                                                                ("state", J.Str state); ("obligations", J.Arr obls);
                                                                ("termination", if Hashtbl.mem st.deferred_guard key then J.Str "deferred" else J.Null) ])))

(* Fresh-process recomputation for the round trip: the prepared type and body of one constant, quoted,
   after the kernel re-check (prepare_env raises otherwise). *)
let check_prepared ~opaque_access key =
  let rkn = kername_of_key key in
  let c = Names.Constant.make1 rkn in
  let env = prepare_env ~opaque_access (Global.env ()) [ Names.GlobRef.ConstRef c ] in
  let sigma = Evd.from_env env in
  let cb = Environ.lookup_constant c env in
  let q t = snd (Ast_quoter.quote_term_rec ~bypass:true ~opaque_access env sigma t) in
  let body = match cb.Declarations.const_body with Declarations.Def b -> term_json (q b) | _ -> J.Null in
  Feedback.msg_info
    Pp.(str ("PREPARED " ^ key ^ " " ^ J.to_string (J.Obj [ ("type", term_json (q cb.Declarations.const_type)); ("body", body) ])))

(* Rocq2Lean CheckInstance "key" "l1=r1;l2=r2": re-check a constant with Rocq's own kernel after
   substituting the given global levels (by Set or by other global levels) in its type and in its
   (prepared) body: the source-side obligation of the cumulativity tier's R2B-P (a proof-local level
   solved below a native fact must still be a valid Rocq instance of the declaration). *)
let check_instance ~opaque_access key subst_s =
  let env = Global.env () in
  let g = Environ.universes env in
  let by_name = Hashtbl.create 97 in
  Univ.Level.Set.iter (fun l -> Hashtbl.replace by_name (level_name l) l) (UGraph.domain g);
  Hashtbl.replace by_name "Set" Univ.Level.set;
  let res =
    try
      let pairs = List.filter (fun s -> s <> "") (String.split_on_char ';' subst_s) in
      let m =
        List.fold_left
          (fun m p ->
            match String.split_on_char '=' p with
            | [ a; b ] -> (
              match (Hashtbl.find_opt by_name a, Hashtbl.find_opt by_name b) with
              | Some la, Some lb -> Univ.Level.Map.add la lb m
              | _ -> failwith ("unknown level in " ^ p))
            | _ -> failwith ("malformed substitution " ^ p))
          Univ.Level.Map.empty pairs
      in
      let sub = (Sorts.QVar.Map.empty, m) in
      let c = Names.Constant.make1 (kername_of_key key) in
      let ty = Vars.subst_univs_level_constr sub (Environ.lookup_constant c env).Declarations.const_type in
      let _ = Typeops.infer_type env ty in
      match prepared_body ~opaque_access env c with
      | None -> "INSTANCE_OK"
      | Some (b, _, _) -> (
        let b = Vars.subst_univs_level_constr sub b in
        let j = Typeops.infer env b in
        match Conversion.default_conv_leq env j.Environ.uj_type ty with
        | Ok () -> "INSTANCE_OK"
        | Error () -> "INSTANCE_TYPE_MISMATCH")
    with e -> "INSTANCE_REJECTED " ^ String.map (fun ch -> if ch = '\n' then ' ' else ch) (Printexc.to_string e)
  in
  Feedback.msg_info Pp.(str ("INSTANCE " ^ key ^ " " ^ res))
