(* Result-sort-only levels of nested class records (MathComp HB's shape; not Prosa).
   - hasDec : a mixin record; its level rs32 is its result sort only;
   - axE    : a class record whose only field is a mixin (rs32 is not a level of axE's source);
   - typeE  : a structure packing a carrier and its class;
   - unify_like : a statement taking a mixin and building the class (the corpus obligation
     Builders_32.HB_unnamed_factory_34 obligation 5: its mixin level must stay generic);
   - getop / pack_eta / mk / mk_op : projections, a dependent elimination, a constructed instance;
   - holder : a record whose field is a typeE: typeE's carrier level is a genuine field level (not
     result-sort-only), never taken by the rule (kernel-rejected before and after the rule: its
     carrier level is defaulted to 0, an existing limitation);
   - wrapA  : a block whose parameter is a typeE: typeE's carrier level becomes an implicit level
     through the arity (R3G, not this rule); the negative control claims it as result-sort-only. *)
Universes rs29 rs32 rs51 rs55 rs58.
Record hasDec (T : Type@{rs29}) : Type@{rs32} := HasDec { op : T -> T -> bool }.
Record axE (T : Type@{rs51}) : Type@{rs55} := Cls { mix : hasDec T }.
Record typeE : Type@{rs58} := Pack { sort : Type@{rs51}; cls : axE sort }.
Lemma unify_like (T : Type) (m : hasDec T) : Cls T m = Cls T m.
Proof. reflexivity. Qed.
Definition getop (e : typeE) : sort e -> sort e -> bool := op _ (mix _ (cls e)).
Lemma pack_eta (e : typeE) : e = Pack (sort e) (cls e).
Proof. destruct e; reflexivity. Qed.
Definition mk (T : Type) (f : T -> T -> bool) : typeE := Pack T (Cls T (HasDec T f)).
Lemma mk_op (T : Type) (f : T -> T -> bool) : getop (mk T f) = f.
Proof. reflexivity. Qed.
Universe rh.
Record holder : Type@{rh} := Hold { held : typeE }.
Universe rw.
Record wrapA (e : typeE) : Type@{rw} := WA { w : sort e -> bool }.

(* fax : a definition over the structure and its projection (MathComp fintype.finite_axiom's shape) *)
Definition fax (T : typeE) (e : list (sort T)) : Prop := forall x : sort T, x = x.
(* eqop / pr1 : MathComp eqtype.eq_op and pred1's shapes (a definition through a definition) *)
Definition eqop (s : typeE) : sort s -> sort s -> bool := op (sort s) (mix (sort s) (cls s)).
Definition pr1 (T : typeE) (a1 : sort T) : sort T -> bool := fun x => eqop T x a1.
