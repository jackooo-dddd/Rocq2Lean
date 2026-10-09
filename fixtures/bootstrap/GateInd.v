(* Fresh inductive + a universe-mentioning definition, compiled separately for the MetaRocq gate. *)
Inductive RBool : Set := RT | RF.
Definition rneg (b : RBool) : RBool := match b with RT => RF | RF => RT end.
Definition TypeOfSets : Type := Set.
