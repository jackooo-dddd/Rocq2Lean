(* R2B-V control (tests/statement/check_universe_c.py): a Prop-valued body declared in Type (Rocq: Prop ≤
   Type cumulativity). Taking the value's sort would make it a proposition (proof-irrelevant elements):
   not a universe-level lowering, never done by R2B-V. *)
Definition Rprop (n m : nat) : Type := n = m.
