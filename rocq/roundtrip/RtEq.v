(* Transparent structural equality on MetaRocq Template ASTs, for the export round trip.
   MetaRocq's own eqb_*_body go through ReflectEq_EqDec_obligation_1, which is opaque, so they
   do not compute; these functions compare every field and reduce fully under cbv. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import ListNotations.

Definition list_eqb {A} (f : A -> A -> bool) : list A -> list A -> bool :=
  fix go l l' := match l, l' with
                 | [], [] => true
                 | x :: xs, y :: ys => f x y && go xs ys
                 | _, _ => false end.

Definition option_eqb {A} (f : A -> A -> bool) (o o' : option A) : bool :=
  match o, o' with None, None => true | Some x, Some y => f x y | _, _ => false end.

Definition str_eqb (s s' : string) : bool := String.eqb s s'.

Definition level_eqb (l l' : Level.t) : bool :=
  match l, l' with
  | Level.lzero, Level.lzero => true
  | Level.level s, Level.level s' => str_eqb s s'
  | Level.lvar n, Level.lvar n' => Nat.eqb n n'
  | _, _ => false end.

Definition lexpr_eqb (e e' : LevelExpr.t) : bool := level_eqb e.1 e'.1 && Nat.eqb e.2 e'.2.
Definition univ_eqb (u u' : Universe.t) : bool :=
  list_eqb lexpr_eqb (LevelExprSet.elements u) (LevelExprSet.elements u').

Definition sort_eqb (s s' : sort) : bool :=
  match s, s' with
  | sProp, sProp | sSProp, sSProp => true
  | sType u, sType u' => univ_eqb u u'
  | _, _ => false end.

Definition rel_eqb (r r' : relevance) : bool :=
  match r, r' with Relevant, Relevant | Irrelevant, Irrelevant => true | _, _ => false end.

Definition name_eqb (n n' : name) : bool :=
  match n, n' with nAnon, nAnon => true | nNamed s, nNamed s' => str_eqb s s' | _, _ => false end.

Definition aname_eqb (a a' : aname) : bool :=
  name_eqb a.(binder_name) a'.(binder_name) && rel_eqb a.(binder_relevance) a'.(binder_relevance).

Fixpoint mp_eqb (m m' : modpath) : bool :=
  match m, m' with
  | MPfile d, MPfile d' => list_eqb str_eqb d d'
  | MPbound d i n, MPbound d' i' n' => list_eqb str_eqb d d' && str_eqb i i' && Nat.eqb n n'
  | MPdot m i, MPdot m' i' => mp_eqb m m' && str_eqb i i'
  | _, _ => false end.

Definition kn_eqb (k k' : kername) : bool := mp_eqb k.1 k'.1 && str_eqb k.2 k'.2.
Definition ind_eqb (i i' : inductive) : bool :=
  kn_eqb i.(inductive_mind) i'.(inductive_mind) && Nat.eqb i.(inductive_ind) i'.(inductive_ind).
Definition inst_eqb := list_eqb level_eqb.

Definition cast_eqb (c c' : cast_kind) : bool :=
  match c, c' with VmCast, VmCast | NativeCast, NativeCast | Cast, Cast => true | _, _ => false end.

Fixpoint term_eqb (t t' : term) {struct t} : bool :=
  match t, t' with
  | tRel n, tRel n' => Nat.eqb n n'
  | tVar i, tVar i' => str_eqb i i'
  | tEvar e a, tEvar e' a' => Nat.eqb e e' && list_eqb term_eqb a a'
  | tSort s, tSort s' => sort_eqb s s'
  | tCast c k ty, tCast c' k' ty' => term_eqb c c' && cast_eqb k k' && term_eqb ty ty'
  | tProd n a b, tProd n' a' b' | tLambda n a b, tLambda n' a' b' =>
      aname_eqb n n' && term_eqb a a' && term_eqb b b'
  | tLetIn n v ty b, tLetIn n' v' ty' b' =>
      aname_eqb n n' && term_eqb v v' && term_eqb ty ty' && term_eqb b b'
  | tApp f a, tApp f' a' => term_eqb f f' && list_eqb term_eqb a a'
  | tConst c u, tConst c' u' => kn_eqb c c' && inst_eqb u u'
  | tInd i u, tInd i' u' => ind_eqb i i' && inst_eqb u u'
  | tConstruct i k u, tConstruct i' k' u' => ind_eqb i i' && Nat.eqb k k' && inst_eqb u u'
  | tCase ci p c brs, tCase ci' p' c' brs' =>
      ind_eqb ci.(ci_ind) ci'.(ci_ind) && Nat.eqb ci.(ci_npar) ci'.(ci_npar)
      && rel_eqb ci.(ci_relevance) ci'.(ci_relevance)
      && inst_eqb p.(puinst) p'.(puinst) && list_eqb term_eqb p.(pparams) p'.(pparams)
      && list_eqb aname_eqb p.(pcontext) p'.(pcontext) && term_eqb p.(preturn) p'.(preturn)
      && term_eqb c c'
      && list_eqb (fun b b' => list_eqb aname_eqb b.(bcontext) b'.(bcontext) && term_eqb b.(bbody) b'.(bbody)) brs brs'
  | tProj p c, tProj p' c' =>
      ind_eqb p.(proj_ind) p'.(proj_ind) && Nat.eqb p.(proj_npars) p'.(proj_npars)
      && Nat.eqb p.(proj_arg) p'.(proj_arg) && term_eqb c c'
  | tFix m i, tFix m' i' | tCoFix m i, tCoFix m' i' =>
      Nat.eqb i i' && list_eqb (fun d d' => aname_eqb d.(dname) d'.(dname) && term_eqb d.(dtype) d'.(dtype)
                                  && term_eqb d.(dbody) d'.(dbody) && Nat.eqb d.(rarg) d'.(rarg)) m m'
  | _, _ => false (* primitives are rejected by the decoder *)
  end.

Definition decl_eqb (d d' : context_decl) : bool :=
  aname_eqb d.(decl_name) d'.(decl_name) && option_eqb term_eqb d.(decl_body) d'.(decl_body)
  && term_eqb d.(decl_type) d'.(decl_type).
Definition ctx_eqb := list_eqb decl_eqb.

Definition ctype_eqb (c c' : ConstraintType.t) : bool :=
  match c, c' with
  | ConstraintType.Le z, ConstraintType.Le z' => Z.eqb z z'
  | ConstraintType.Eq, ConstraintType.Eq => true
  | _, _ => false end.
Definition cstr_eqb (c c' : UnivConstraint.t) : bool :=
  level_eqb c.1.1 c'.1.1 && ctype_eqb c.1.2 c'.1.2 && level_eqb c.2 c'.2.
Definition udecl_eqb (u u' : universes_decl) : bool :=
  match u, u' with
  | Monomorphic_ctx, Monomorphic_ctx => true
  | Polymorphic_ctx (ns, cs), Polymorphic_ctx (ns', cs') =>
      list_eqb name_eqb ns ns' && list_eqb cstr_eqb (ConstraintSet.elements cs) (ConstraintSet.elements cs')
  | _, _ => false end.

Definition cb_eqb (c c' : constant_body) : bool :=
  term_eqb c.(cst_type) c'.(cst_type) && option_eqb term_eqb c.(cst_body) c'.(cst_body)
  && udecl_eqb c.(cst_universes) c'.(cst_universes) && rel_eqb c.(cst_relevance) c'.(cst_relevance).

Definition kelim_eqb (k k' : allowed_eliminations) : bool :=
  match k, k' with IntoSProp, IntoSProp | IntoPropSProp, IntoPropSProp
  | IntoSetPropSProp, IntoSetPropSProp | IntoAny, IntoAny => true | _, _ => false end.
Definition finite_eqb (f f' : recursivity_kind) : bool :=
  match f, f' with Finite, Finite | CoFinite, CoFinite | BiFinite, BiFinite => true | _, _ => false end.
Definition variance_eqb (v v' : Variance.t) : bool :=
  match v, v' with Variance.Irrelevant, Variance.Irrelevant | Variance.Covariant, Variance.Covariant
  | Variance.Invariant, Variance.Invariant => true | _, _ => false end.

Definition ctor_eqb (c c' : constructor_body) : bool :=
  str_eqb c.(cstr_name) c'.(cstr_name) && ctx_eqb c.(cstr_args) c'.(cstr_args)
  && list_eqb term_eqb c.(cstr_indices) c'.(cstr_indices) && term_eqb c.(cstr_type) c'.(cstr_type)
  && Nat.eqb c.(cstr_arity) c'.(cstr_arity).
Definition proj_eqb (p p' : projection_body) : bool :=
  str_eqb p.(proj_name) p'.(proj_name) && rel_eqb p.(proj_relevance) p'.(proj_relevance)
  && term_eqb p.(proj_type) p'.(proj_type).
Definition oib_eqb (b b' : one_inductive_body) : bool :=
  str_eqb b.(ind_name) b'.(ind_name) && ctx_eqb b.(ind_indices) b'.(ind_indices)
  && sort_eqb b.(ind_sort) b'.(ind_sort) && term_eqb b.(ind_type) b'.(ind_type)
  && kelim_eqb b.(ind_kelim) b'.(ind_kelim) && list_eqb ctor_eqb b.(ind_ctors) b'.(ind_ctors)
  && list_eqb proj_eqb b.(ind_projs) b'.(ind_projs) && rel_eqb b.(ind_relevance) b'.(ind_relevance).
Definition mib_eqb (m m' : mutual_inductive_body) : bool :=
  finite_eqb m.(ind_finite) m'.(ind_finite) && Nat.eqb m.(ind_npars) m'.(ind_npars)
  && ctx_eqb m.(ind_params) m'.(ind_params) && list_eqb oib_eqb m.(ind_bodies) m'.(ind_bodies)
  && udecl_eqb m.(ind_universes) m'.(ind_universes)
  && option_eqb (list_eqb variance_eqb) m.(ind_variance) m'.(ind_variance).
