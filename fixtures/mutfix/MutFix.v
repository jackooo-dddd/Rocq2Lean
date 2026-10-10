(* M6 mutual structural fixpoints over one inductive: the shapes of Stdlib Pos.add/add_carry and
   Pos.sub_mask/sub_mask_carry (copied over a local positive type), a parametric mutual pair, a
   mutual pair whose decreasing match is not outermost, closed computations and open-variable
   computation rules by reflexivity. *)
Inductive pos : Set := xI : pos -> pos | xO : pos -> pos | xH : pos.
Open Scope list_scope.

Fixpoint succ (x : pos) : pos := match x with xI p => xO (succ p) | xO p => xI p | xH => xO xH end.

Fixpoint add (x y : pos) : pos :=
  match x, y with
  | xI p, xI q => xO (add_carry p q)
  | xI p, xO q => xI (add p q)
  | xI p, xH => xO (succ p)
  | xO p, xI q => xI (add p q)
  | xO p, xO q => xO (add p q)
  | xO p, xH => xI p
  | xH, xI q => xO (succ q)
  | xH, xO q => xI q
  | xH, xH => xO xH
  end
with add_carry (x y : pos) : pos :=
  match x, y with
  | xI p, xI q => xI (add_carry p q)
  | xI p, xO q => xO (add_carry p q)
  | xI p, xH => xI (succ p)
  | xO p, xI q => xO (add_carry p q)
  | xO p, xO q => xI (add p q)
  | xO p, xH => xO (succ p)
  | xH, xI q => xI (succ q)
  | xH, xO q => xO (succ q)
  | xH, xH => xI xH
  end.

Inductive mask : Set := IsNul : mask | IsPos : pos -> mask | IsNeg : mask.
Definition double_mask (x : mask) : mask := match x with IsNul => IsNul | IsNeg => IsNeg | IsPos p => IsPos (xO p) end.
Definition succ_double_mask (x : mask) : mask := match x with IsNul => IsPos xH | IsNeg => IsNeg | IsPos p => IsPos (xI p) end.
Definition double_pred_mask (x : pos) : mask :=
  match x with xI p => IsPos (xO (xO p)) | xO p => IsPos (xO (match p with xH => xH | _ => p end)) | xH => IsNul end.
Fixpoint pred_double (x : pos) : pos := match x with xI p => xI (xO p) | xO p => xI (pred_double p) | xH => xH end.

Fixpoint sub_mask (x y : pos) {struct y} : mask :=
  match x, y with
  | xI p, xI q => double_mask (sub_mask p q)
  | xI p, xO q => succ_double_mask (sub_mask p q)
  | xI p, xH => IsPos (xO p)
  | xO p, xI q => succ_double_mask (sub_mask_carry p q)
  | xO p, xO q => double_mask (sub_mask p q)
  | xO p, xH => IsPos (pred_double p)
  | xH, xH => IsNul
  | xH, _ => IsNeg
  end
with sub_mask_carry (x y : pos) {struct y} : mask :=
  match x, y with
  | xI p, xI q => succ_double_mask (sub_mask_carry p q)
  | xI p, xO q => double_mask (sub_mask p q)
  | xI p, xH => IsPos (pred_double p)
  | xO p, xI q => double_mask (sub_mask_carry p q)
  | xO p, xO q => succ_double_mask (sub_mask_carry p q)
  | xO p, xH => double_pred_mask p
  | xH, _ => IsNeg
  end.

(* parametric mutual recursion on lists: shared parameter A and an extra argument after x. With
   A : Type, Rocq gives each function its own global universe for A (MutFix.23 / MutFix.26), so the
   leading argument types differ: rejected (UNSUPPORTED_FEATURE), a documented limit of the rule. *)
Fixpoint evens {A : Type} (l : list A) (acc : list A) : list A :=
  match l with nil => acc | cons a t => cons a (odds t acc) end
with odds {A : Type} (l : list A) (acc : list A) : list A :=
  match l with nil => acc | cons _ t => evens t acc end.

(* the same with A : Set (one shared parameter type) *)
Fixpoint evens_s {A : Set} (l : list A) (acc : list A) : list A :=
  match l with nil => acc | cons a t => cons a (odds_s t acc) end
with odds_s {A : Set} (l : list A) (acc : list A) : list A :=
  match l with nil => acc | cons _ t => evens_s t acc end.

(* mutual recursion whose decreasing match is not outermost (struct y, x changes) *)
Fixpoint alt_eq (x y : pos) {struct y} : bool :=
  match x, y with xI p, xI q => alt_neq p q | xO p, xO q => alt_eq p q | xH, xH => true | _, _ => false end
with alt_neq (x y : pos) {struct y} : bool :=
  match x, y with xI p, xI q => alt_eq p q | xO p, xO q => alt_neq p q | xH, xH => false | _, _ => true end.

Fixpoint p2n (p : pos) : nat := match p with xI q => S (2 * p2n q) | xO q => 2 * p2n q | xH => 1 end.
Definition m2n (m : mask) : nat := match m with IsNul => 0 | IsPos p => p2n p | IsNeg => 99 end.

Definition seven := xI (xI xH).
Definition twelve := xO (xO (xI xH)).
Example add_ex : p2n (add seven twelve) = 19 := eq_refl.
Example add_carry_ex : p2n (add_carry seven twelve) = 20 := eq_refl.
Example sub_ex : m2n (sub_mask twelve seven) = 5 := eq_refl.
Example sub_ex2 : sub_mask seven twelve = IsNeg := eq_refl.
Example sub_ex3 : sub_mask seven seven = IsNul := eq_refl.
Example evens_ex : evens (1 :: 2 :: 3 :: 4 :: 5 :: nil) nil = 1 :: 3 :: 5 :: nil := eq_refl.
Example evens_s_ex : evens_s (1 :: 2 :: 3 :: 4 :: 5 :: nil) nil = 1 :: 3 :: 5 :: nil := eq_refl.
Example odds_s_ex : odds_s (1 :: 2 :: 3 :: 4 :: 5 :: nil) (9 :: nil) = 2 :: 4 :: 9 :: nil := eq_refl.
Example alt_ex : alt_eq (xI (xO xH)) (xI (xO xH)) = false := eq_refl.
Example alt_ex2 : alt_neq (xI (xI xH)) (xI (xI xH)) = false := eq_refl.
Example odds_ex : odds (1 :: 2 :: 3 :: 4 :: 5 :: nil) (9 :: nil) = 2 :: 4 :: 9 :: nil := eq_refl.

(* open-variable computation rules, cross-function calls included *)
Lemma add_step (p q : pos) : add (xI p) (xI q) = xO (add_carry p q). Proof. reflexivity. Qed.
Lemma add_carry_step (p q : pos) : add_carry (xO p) (xO q) = xI (add p q). Proof. reflexivity. Qed.
Lemma sub_step (p q : pos) : sub_mask (xO p) (xI q) = succ_double_mask (sub_mask_carry p q). Proof. reflexivity. Qed.
Lemma odds_s_step {A : Set} (a : A) (t acc : list A) : odds_s (a :: t) acc = evens_s t acc. Proof. reflexivity. Qed.
Lemma alt_step (p q : pos) : alt_eq (xI p) (xI q) = alt_neq p q. Proof. reflexivity. Qed.
Lemma odds_step {A} (a : A) (t acc : list A) : odds (a :: t) acc = evens t acc. Proof. reflexivity. Qed.
