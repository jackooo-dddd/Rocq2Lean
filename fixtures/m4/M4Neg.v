(* M4 negative input: Rocq's template prod "can be instantiated to Prop". The translation fixes the
   template defaults' quality (Type), so a Prop instance must be rejected explicitly, not coerced. *)
Definition pp : True * True := (I, I).
(* A Prop-valued family for sigT's template arity parameter P : A -> Type: Rocq uses Prop <= Type
   cumulativity, which Lean cannot express without a lift; it must be rejected explicitly. *)
Definition sig_prop : {n : nat & n = n} := existT (fun n => n = n) 0 eq_refl.
