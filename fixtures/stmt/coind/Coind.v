(* Rule T fixture (docs/COINDUCTIVE.md): Classic's Task_T shape, a non-recursive coinductive record.
   Synthetic. *)
CoInductive Task_T : Set := build_task : nat -> nat -> nat -> nat -> Task_T.
Definition get_P (t : Task_T) : nat := match t with build_task p _ _ _ => p end.
Definition get_C (t : Task_T) : nat := match t with build_task _ c _ _ => c end.
Lemma get_P_build (a b c d : nat) : get_P (build_task a b c d) = a.
Proof. reflexivity. Qed.
(* T1, Rocq side (checked here by Rocq): every inhabitant is a constructor application, propositionally *)
Lemma Task_T_eta (x : Task_T) : x = build_task (get_P x) (get_C x)
  (match x with build_task _ _ d _ => d end) (match x with build_task _ _ _ e => e end).
Proof. destruct x; reflexivity. Qed.
(* negative: a recursive coinductive type, and cofixpoints, stay refused *)
CoInductive stream : Set := scons : nat -> stream -> stream.
CoFixpoint zeros : stream := scons 0 zeros.
CoFixpoint task0 : Task_T := build_task 0 0 0 0.
Inductive fin2 : Set := f0 | f1.
