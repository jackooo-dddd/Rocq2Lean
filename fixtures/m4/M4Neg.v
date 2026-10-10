(* M4 negative input: Rocq's template prod "can be instantiated to Prop". The translation fixes the
   template defaults' quality (Type), so a Prop instance must be rejected explicitly, not coerced. *)
Definition pp : True * True := (I, I).
