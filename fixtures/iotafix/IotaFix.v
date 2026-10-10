(* M6 ι-generalized fix lowering: structural fixpoints whose decreasing match is not outermost
   (the shapes of Stdlib Pos.eqb, Pos.compare_cont, ListDef.nth), a dependent return clause on the
   decreasing argument, and reflexivity checks of their computation rules on open variables. *)
Inductive pos : Set := xI : pos -> pos | xO : pos -> pos | xH : pos.
Inductive cmp : Set := Eq | Lt | Gt.
Open Scope list_scope.

(* Pos.eqb: struct q, the outer match is on p *)
Fixpoint eqb (p q : pos) {struct q} : bool :=
  match p, q with
  | xI p, xI q => eqb p q
  | xO p, xO q => eqb p q
  | xH, xH => true
  | _, _ => false
  end.

(* Pos.compare_cont: the accumulator r and the first argument x change in recursive calls *)
Fixpoint compare_cont (r : cmp) (x y : pos) {struct y} : cmp :=
  match x, y with
  | xI p, xI q => compare_cont r p q
  | xI p, xO q => compare_cont Gt p q
  | xI _, xH => Gt
  | xO p, xI q => compare_cont Lt p q
  | xO p, xO q => compare_cont r p q
  | xO _, xH => Gt
  | xH, xH => r
  | xH, _ => Lt
  end.

(* ListDef.nth: struct l, the outer match is on n, which changes *)
Fixpoint nth {A : Type} (n : nat) (l : list A) (default : A) {struct l} : A :=
  match n, l with
  | O, x :: _ => x
  | O, nil => default
  | S _, nil => default
  | S m, _ :: t => nth m t default
  end.

(* a match on an unchanged argument first; a dependent return clause on the decreasing argument *)
Definition T (p : pos) : Set := match p with xH => bool | _ => nat end.
Fixpoint dep (b : bool) (p : pos) {struct p} : T p :=
  match b with
  | true => match p as p0 return T p0 with
            | xI q => 0
            | xO q => match q as q0 return T q0 -> nat with xH => fun c => if c then 1 else 2 | _ => fun n => S n end (dep b q)
            | xH => true
            end
  | false => match p as p0 return T p0 with xI _ | xO _ => 7 | xH => false end
  end.

(* the decreasing argument used outside a match (it denotes the constructor application) *)
Fixpoint size_if (b : bool) (p : pos) {struct p} : nat :=
  if b then match p with xI q | xO q => S (size_if b q) | xH => 1 end else (match p with xH => 0 | _ => 1 end).

Definition four := xO (xO xH).
Definition five := xI (xO xH).
Example eqb_ex : eqb four four = true := eq_refl.
Example eqb_ex2 : eqb four five = false := eq_refl.
Example cmp_ex : compare_cont Eq four five = Lt := eq_refl.
Example cmp_ex2 : compare_cont Eq five four = Gt := eq_refl.
Example nth_ex : nth 2 (10 :: 20 :: 30 :: nil) 0 = 30 := eq_refl.
Example nth_ex2 : nth 5 (10 :: nil) 0 = 0 := eq_refl.
Example dep_ex : dep true (xO xH) = 1 := eq_refl.
Example dep_ex2 : dep true (xO (xO xH)) = 2 := eq_refl.
Example size_ex : size_if true five = 3 := eq_refl.

(* open-variable computation rules: definitional in the source, hence in the target *)
Lemma eqb_step (p q : pos) : eqb (xI p) (xI q) = eqb p q. Proof. reflexivity. Qed.
Lemma eqb_mixed (p q : pos) : eqb (xI p) (xO q) = false. Proof. reflexivity. Qed.
Lemma cmp_step (r : cmp) (p q : pos) : compare_cont r (xI p) (xO q) = compare_cont Gt p q. Proof. reflexivity. Qed.
Lemma nth_step {A} (m : nat) (a : A) (t : list A) (d : A) : nth (S m) (a :: t) d = nth m t d. Proof. reflexivity. Qed.
Lemma size_step (p : pos) : size_if true (xO p) = S (size_if true p). Proof. reflexivity. Qed.

(* ζ: a let-bound partial application of the recursive function (the shape of Pos.peano_rect) *)
Fixpoint sumto (k : nat) (n : nat) {struct n} : nat :=
  let g := sumto (S k) in match n with O => k | S m => k + g m end.
Example sumto_ex : sumto 1 3 = 10 := eq_refl.
Lemma sumto_step (k m : nat) : sumto k (S m) = k + sumto (S k) m. Proof. reflexivity. Qed.

(* a functional recursive field (the shape of Acc's (forall y, R y x -> Acc y)) *)
Inductive tree : Set := leaf : nat -> tree | node : (nat -> tree) -> tree.
Fixpoint walk (k : nat) (t : tree) {struct t} : nat :=
  match t with leaf n => n | node f => walk k (f k) + walk k (f (S k)) end.
Definition t3 : tree := node (fun i => node (fun j => leaf (10 * i + j))).
Example walk_ex : walk 1 t3 = 66 := eq_refl.
Lemma walk_step (k : nat) (f : nat -> tree) : walk k (node f) = walk k (f k) + walk k (f (S k)). Proof. reflexivity. Qed.

(* δβ: a fixpoint passed to another constant, which calls it on a structural subterm
   (the shapes of Ring_polynom.Padd/PaddI and Tauto.xcnf/mk_and) *)
Inductive pol : Set := pc : nat -> pol | pinj : nat -> pol -> pol | px : pol -> pol -> pol.
Section AddI.
  Variable Pop : pol -> pol -> pol.
  Variable Q : pol.
  Fixpoint addI (P : pol) {struct P} : pol :=
    match P with pc c => pinj c Q | pinj j Q' => pinj j (Pop Q' Q) | px A B => px A (addI B) end.
End AddI.
Fixpoint padd (P P' : pol) {struct P'} : pol :=
  match P' with pc c => P | pinj j Q' => addI padd Q' P | px A B => px (padd P A) (padd P B) end.
Fixpoint psize (P : pol) : nat := match P with pc c => c | pinj j Q => j + psize Q | px A B => psize A + psize B end.
Example padd_ex : psize (padd (pinj 1 (pc 2)) (pinj 3 (px (pc 4) (pc 5)))) = 5 := eq_refl.
Lemma padd_step (P Q : pol) (j : nat) : padd P (pinj j Q) = addI padd Q P. Proof. reflexivity. Qed.

Inductive t2 : Set := lf : t2 | nd : t2 -> t2 -> t2.
Definition both (rec : bool -> t2 -> nat) (b : bool) (l r : t2) : nat := rec b l + rec (negb b) r.
Fixpoint count (k : nat) (b : bool) (t : t2) {struct t} : nat :=
  match t with lf => if b then k else 0 | nd l r => both (count k) b l r end.
Example count_ex : count 5 true (nd (nd lf lf) lf) = 5 := eq_refl.
Lemma count_step (k : nat) (b : bool) (l r : t2) : count k b (nd l r) = count k b l + count k (negb b) r.
Proof. reflexivity. Qed.

(* course-of-values: recursive calls on subterms that are not direct fields (the shape of
   Ring_polynom.norm_aux: a call on the field of a matched field) *)
Inductive pe : Set := econst : nat -> pe | eadd : pe -> pe -> pe | eopp : pe -> pe.
Fixpoint norm (e : pe) : nat :=
  match e with
  | econst n => n
  | eadd e1 e2 =>
      match e2 with
      | eopp e3 => norm e1 - norm e3
      | eadd a b => match a with eopp c => norm e1 + norm c + norm b | _ => norm e1 + norm e2 end
      | _ => norm e1 + norm e2
      end
  | eopp e1 => norm e1
  end.
Example norm_ex : norm (eadd (econst 9) (eopp (econst 4))) = 5 := eq_refl.
Example norm_ex2 : norm (eadd (econst 1) (eadd (eopp (econst 3)) (econst 7))) = 11 := eq_refl.
Lemma norm_step (x y : pe) : norm (eadd x (eopp y)) = norm x - norm y. Proof. reflexivity. Qed.
Lemma norm_step3 (x c b : pe) : norm (eadd x (eadd (eopp c) b)) = norm x + norm c + norm b. Proof. reflexivity. Qed.

(* a proof whose cast needs norm's unfolding at open arguments (the shape of
   Ring_polynom.norm_aux_PEadd: simpl, then case analysis) *)
Lemma norm_eadd (x y : pe) :
  norm (eadd x y) =
  match y with
  | eopp e3 => norm x - norm e3
  | eadd a b => match a with eopp c => norm x + norm c + norm b | _ => norm x + norm y end
  | _ => norm x + norm y
  end.
Proof. simpl norm. destruct y as [n|a b|e3]; try destruct a; reflexivity. Qed.

(* negative control: recursion through the nesting of a nested inductive (an inner fixpoint over
   the children) is not supported and must be rejected, not mis-lowered *)
Inductive rose : Set := rnode : list rose -> rose.
Fixpoint rsize (r : rose) : nat :=
  match r with
  | rnode cs => S ((fix go (l : list rose) : nat := match l with nil => 0 | cons c t => rsize c + go t end) cs)
  end.
