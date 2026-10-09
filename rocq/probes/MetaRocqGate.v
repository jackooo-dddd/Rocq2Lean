(* Phase 0 MetaRocq compatibility gate (Rocq 9.3.0). Loads separately compiled fixtures. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From Fixtures Require Import IdNat GateInd.
Import MonadNotation.
Open Scope bs_scope.

Definition body_state (Σ : global_env) (kn : kername) : string :=
  match lookup_env Σ kn with
  | Some (ConstantDecl cb) => match cst_body cb with Some _ => "BODY_PRESENT" | None => "NO_BODY" end
  | Some (InductiveDecl _) => "INDUCTIVE"
  | None => "MISSING"
  end.

Definition gate (name : string) {A} (a : A) : TemplateMonad unit :=
  p <- tmQuoteRecTransp a true ;;
  t <- tmQuote a ;;
  match t with
  | tConst kn _ =>
      tmMsg (name ^ " " ^ string_of_kername kn ^ " " ^ body_state (fst p) kn ^
             " env_decls=" ^ string_of_nat (List.length (declarations (fst p))))
  | tInd ind _ =>
      tmMsg (name ^ " " ^ string_of_kername (inductive_mind ind) ^ " " ^ body_state (fst p) (inductive_mind ind))
  | _ => tmFail "unexpected quotation shape"
  end.

MetaRocq Run (gate "GATE_TRANSPARENT" id_nat).
MetaRocq Run (gate "GATE_QED" id_nat_correct).
MetaRocq Run (gate "GATE_INDUCTIVE" RBool).
MetaRocq Run (gate "GATE_UNIVERSE" TypeOfSets).

(* Without bypass, the Qed body must be hidden: this is the opacity semantics we rely on. *)
MetaRocq Run (p <- tmQuoteRecTransp id_nat_correct false ;; t <- tmQuote id_nat_correct ;;
  match t with tConst kn _ => tmMsg ("GATE_QED_NOBYPASS " ^ body_state (fst p) kn) | _ => tmFail "?" end).

(* Raw shapes, for the IR index convention: tRel 0 must be the innermost binder. *)
MetaRocq Quote Recursively Definition q_idnat_correct := id_nat_correct.
MetaRocq Test Quote (fun (x y : nat) => x).
MetaRocq Run (p <- tmQuoteRecTransp id_nat_correct true ;; t <- tmQuote id_nat_correct ;;
  match t with
  | tConst kn _ => match lookup_env (fst p) kn with
                   | Some (ConstantDecl cb) => tmEval cbv (cst_type cb, cst_body cb, cst_universes cb) >>= tmPrint
                   | _ => tmFail "?" end
  | _ => tmFail "?" end).
MetaRocq Run (p <- tmQuoteRecTransp TypeOfSets true ;; tmEval cbv (universes (fst p)) >>= tmPrint).
