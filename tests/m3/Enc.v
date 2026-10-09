(* Constructor-index encoding of closed values, for source/target computation comparison. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Open Scope bs_scope.

Fixpoint enc (t : term) : string :=
  match t with
  | tConstruct ind k _ => "(c " ^ string_of_kername ind.(inductive_mind) ^ " " ^ string_of_nat k ^ ")"
  | tInd ind _ => "(i " ^ string_of_kername ind.(inductive_mind) ^ ")"
  | tApp f args =>
      "(a " ^ enc f ^ List.fold_left (fun acc a => acc ^ " " ^ a) (List.map enc args) "" ^ ")"
  | _ => "?"
  end.
