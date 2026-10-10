(* Fresh holdouts for the hardened implementation. Written after the implementation was frozen at
   tag hardening-freeze-1; nothing in the implementation was changed after seeing their results.
   Ordinary Rocq developments inside the declared M1-M3 fragment, not copies of earlier fixtures. *)

(* Arithmetic over Corelib nat, proved by induction (Corelib nat_ind, Nat.add). *)
Lemma add_0_r' : forall n, n + 0 = n.
Proof. induction n as [|n IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma add_S_r' : forall n m, n + S m = S (n + m).
Proof. induction n as [|n IH]; intro m; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
Lemma add_comm' : forall n m, n + m = m + n.
Proof. intros n m. induction n as [|n IH]; simpl. - rewrite add_0_r'. reflexivity. - rewrite IH, add_S_r'. reflexivity. Qed.

(* A parameterized inductive with three constructors, two of them with two fields. *)
Inductive Shape (A : Set) : Set :=
| Pt : A -> Shape A
| Seg : A -> A -> Shape A
| Grp : Shape A -> Shape A -> Shape A.
Arguments Pt {A}. Arguments Seg {A}. Arguments Grp {A}.
Fixpoint points {A : Set} (s : Shape A) : nat :=
  match s with Pt _ => 1 | Seg _ _ => 2 | Grp l r => points l + points r end.
Fixpoint flip {A : Set} (s : Shape A) : Shape A :=
  match s with Pt a => Pt a | Seg a b => Seg b a | Grp l r => Grp (flip r) (flip l) end.
Lemma points_flip : forall (A : Set) (s : Shape A), points (flip s) = points s.
Proof.
  intros A s. induction s as [a|a b|l IHl r IHr]; simpl.
  - reflexivity. - reflexivity. - rewrite IHl, IHr. apply add_comm'.
Qed.

(* An indexed family other than Vec; recursion with index generalization and an index-dependent result. *)
Inductive Fin : nat -> Set :=
| F1 : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n).
Arguments F1 {n}. Arguments FS {n}.
Fixpoint fin_val {n} (i : Fin n) : nat := match i with F1 => 0 | FS j => S (fin_val j) end.
Fixpoint fin_lift {n} (i : Fin n) : Fin (S n) := match i with F1 => F1 | FS j => FS (fin_lift j) end.
Lemma fin_val_lift : forall n (i : Fin n), fin_val (fin_lift i) = fin_val i.
Proof. intros n i. induction i as [n|n j IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

(* Nested non-recursive matches; case-analysis proofs. *)
Inductive Tri : Set := Lo | Mid | Hi.
Definition tmax (a b : Tri) : Tri :=
  match a with Hi => Hi | Mid => match b with Hi => Hi | _ => Mid end | Lo => b end.
Lemma tmax_comm : forall a b, tmax a b = tmax b a. Proof. intros [] []; reflexivity. Qed.
Lemma tmax_idem : forall a, tmax a a = a. Proof. intros []; reflexivity. Qed.
Lemma tri_neq : Lo <> Hi. Proof. discriminate. Qed.
Lemma S_inj' : forall n m, S n = S m -> n = m. Proof. intros n m H. injection H as H. exact H. Qed.

(* An indexed inductive predicate; induction on its proofs (eliminating into Prop). *)
Inductive Ev : nat -> Prop := ev0 : Ev 0 | evSS : forall n, Ev n -> Ev (S (S n)).
Fixpoint dbl (n : nat) : nat := match n with 0 => 0 | S p => S (S (dbl p)) end.
Lemma ev_dbl : forall n, Ev (dbl n).
Proof. induction n as [|n IH]; simpl. - constructor. - constructor. exact IH. Qed.
Lemma ev_plus4 : forall n, Ev n -> Ev (4 + n). Proof. intros n H. simpl. apply evSS, evSS, H. Qed.
Lemma ev_sum : forall n m, Ev n -> Ev m -> Ev (n + m).
Proof. intros n m Hn Hm. induction Hn as [|n Hn IH]; simpl. - exact Hm. - apply evSS. exact IH. Qed.

(* A list type, an accumulator recursion and a generalized induction. *)
Inductive L : Set := nil' : L | cons' : nat -> L -> L.
Fixpoint len (l : L) : nat := match l with nil' => 0 | cons' _ t => S (len t) end.
Fixpoint revA (l acc : L) {struct l} : L := match l with nil' => acc | cons' x t => revA t (cons' x acc) end.
Lemma len_revA : forall l acc, len (revA l acc) = len l + len acc.
Proof. induction l as [|x t IH]; intro acc; simpl. - reflexivity. - rewrite IH. simpl. apply add_S_r'. Qed.

(* Section variables discharged into a parameter that recursive calls keep. *)
Section Map.
  Variable f : nat -> nat.
  Fixpoint mapL (l : L) : L := match l with nil' => nil' | cons' x t => cons' (f x) (mapL t) end.
  Lemma len_mapL : forall l, len (mapL l) = len l.
  Proof. induction l as [|x t IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.
End Map.

(* A transparent lemma and a let, used computationally. *)
Definition three : nat := let x := 1 in x + 2.
Lemma three_eq : three = 3. Proof. reflexivity. Defined.
Lemma use_three : dbl three = 6. Proof. reflexivity. Qed.
