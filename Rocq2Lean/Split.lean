import Rocq2Lean.IR

/-!
# R-SPLIT: one source level shared by several parameter binder sorts (experimental rule)

docs/LEVEL_SPLIT.md. A monomorphic declaration may use one global level `l` as the sort of several
parameter binders (CoqEAL's parametricity relations: `list_R (A1 A2 : Type@{190}) (A_R : A1 → A2 →
Type@{190})`). Rocq's cumulativity lets every use instantiate each of those parameters with a type of
its own level `≤ l`; a Lean translation with one universe parameter for `l` forces all of them to one
level. The *split view* of the declaration gives each such binder its own copy `l__s<i>` of `l`.

Eligibility (derived from the source only): `l` occurs (i) as the final sort of the types of at least
two parameter binders, whose binder types mention `l` nowhere else, and (ii) otherwise only in the
final result sort of the declaration (the join of the copies there); nowhere else (bodies, constructor
arguments, indices, projections, other binders). Single-body, monomorphic, non-template only.

Correspondence: renaming every copy back to `l` gives the source declaration exactly (the diagonal);
every use instantiates the copy of binder `i` with the level of its argument, which Rocq's
cumulativity places below `l` (`a ≤ l`, a fact of the source graph, checked at every reference by
R3). The copies inherit the *upper* bounds of `l` (`l ≤ m`, `l < m`), never its lower bounds (an
argument below `l` need not satisfy them).
-/

namespace Rocq2Lean.Split
open IR

partial def mapLevels (f : LevelExpr → Array LevelExpr) : Term → Term
  | .sort (.type u) => .sort (.type (u.foldl (fun acc e => acc ++ f e) #[]))
  | .cast t k ty => .cast (mapLevels f t) k (mapLevels f ty)
  | .prod n a b => .prod n (mapLevels f a) (mapLevels f b)
  | .lam n a b => .lam n (mapLevels f a) (mapLevels f b)
  | .letIn n v t b => .letIn n (mapLevels f v) (mapLevels f t) (mapLevels f b)
  | .app g args => .app (mapLevels f g) (args.map (mapLevels f))
  | .evar ev args => .evar ev (args.map (mapLevels f))
  | .case i np r pu pps pctx pret scrut brs =>
    .case i np r pu (pps.map (mapLevels f)) pctx (mapLevels f pret) (mapLevels f scrut) (brs.map fun (c, b) => (c, mapLevels f b))
  | .proj i np a t => .proj i np a (mapLevels f t)
  | .fix defs k => .fix (defs.map fun (n, t, b, r) => (n, mapLevels f t, mapLevels f b, r)) k
  | .cofix defs k => .cofix (defs.map fun (n, t, b, r) => (n, mapLevels f t, mapLevels f b, r)) k
  | t => t

partial def countLevel (l : String) : Term → Nat
  | .sort (.type u) => (u.filter (·.level == .global l)).size
  | .cast t _ ty => countLevel l t + countLevel l ty
  | .prod _ a b | .lam _ a b => countLevel l a + countLevel l b
  | .letIn _ v t b => countLevel l v + countLevel l t + countLevel l b
  | .app g args => countLevel l g + args.foldl (· + countLevel l ·) 0
  | .evar _ args => args.foldl (· + countLevel l ·) 0
  | .case _ _ _ pu pps _ pret scrut brs =>
    (pu.filter (· == .global l)).size + pps.foldl (· + countLevel l ·) 0 + countLevel l pret + countLevel l scrut + brs.foldl (· + countLevel l ·.2) 0
  | .proj _ _ _ t => countLevel l t
  | .fix defs _ | .cofix defs _ => defs.foldl (fun a (_, t, b, _) => a + countLevel l t + countLevel l b) 0
  -- (a level in a universe instance, or in a primitive's raw data, is an occurrence the split view
  -- does not rename: it makes the level ineligible)
  | .const _ u | .ind _ u | .construct _ _ u => (u.filter (· == .global l)).size
  | .prim _ raw => if (raw.compress.splitOn l).length > 1 then 1 else 0
  | _ => 0

def countSort (l : String) : SortIR → Nat
  | .type u => (u.filter (·.level == .global l)).size
  | _ => 0

/-- `l` replaced by the copies `news` (a `max` of them). -/
def rename (l : String) (news : Array String) : Term → Term :=
  mapLevels fun e => if e.level == .global l then news.map fun n => { e with level := .global n } else #[e]

def renameSort (l : String) (news : Array String) : SortIR → SortIR
  | .type u => .type (u.foldl (fun acc e => if e.level == .global l then acc ++ news.map fun n => { e with level := .global n } else acc.push e) #[])
  | s => s

/-- The final sort of a binder type `∀ …, Sort s`, if `l` occurs there and nowhere else in it. -/
partial def groupBinder (l : String) (ty : Term) : Bool :=
  let rec fin : Term → Option SortIR
    | .prod _ _ b => fin b
    | .sort s => some s
    | _ => none
  match fin ty with
  | some s => countSort l s ≥ 1 && countLevel l ty == countSort l s
  | none => false

/-- Leading `∀` binder types (up to `n`) and the remainder. -/
partial def prods (t : Term) (n : Nat) : Array (AName × Term) × Term :=
  match n, t with
  | n + 1, .prod a ty b => let (xs, r) := prods b n; (#[(a, ty)] ++ xs, r)
  | _, t => (#[], t)

partial def lams (t : Term) (n : Nat) : Array (AName × Term) × Term :=
  match n, t with
  | n + 1, .lam a ty b => let (xs, r) := lams b n; (#[(a, ty)] ++ xs, r)
  | _, t => (#[], t)

partial def nprods : Term → Nat
  | .prod _ _ b => nprods b + 1
  | _ => 0

partial def nlams : Term → Nat
  | .lam _ _ b => nlams b + 1
  | _ => 0

/-- Occurrences of `l` in the final sort of a term `∀ …, Sort s`. -/
partial def finalSortCount (l : String) : Term → Nat
  | .prod _ _ b => finalSortCount l b
  | .sort s => countSort l s
  | _ => 0

/-- The final sort of `t` with `l` replaced by the copies (only there). -/
partial def renameFinal (l : String) (news : Array String) : Term → Term
  | .prod n a b => .prod n a (renameFinal l news b)
  | .sort s => .sort (renameSort l news s)
  | t => t

def splitName (l : String) (i : Nat) : String := s!"{l}__s{i}"

structure Info where
  level : String
  params : Array Nat
  names : Array String
  deriving Inhabited

def rebuildProds (bs : Array (AName × Term)) (rest : Term) : Term :=
  bs.foldr (fun (a, ty) acc => .prod a ty acc) rest

def rebuildLams (bs : Array (AName × Term)) (rest : Term) : Term :=
  bs.foldr (fun (a, ty) acc => .lam a ty acc) rest

partial def globalsOfTerm (t : Term) : Array String :=
  let rec go : Term → Array String → Array String
    | .sort (.type u), a => u.foldl (fun a e => match e.level with | .global n => if a.contains n then a else a.push n | _ => a) a
    | .cast t _ ty, a => go ty (go t a)
    | .prod _ x b, a | .lam _ x b, a => go b (go x a)
    | .letIn _ v t b, a => go b (go t (go v a))
    | .app g args, a => args.foldl (fun a x => go x a) (go g a)
    | .evar _ args, a => args.foldl (fun a x => go x a) a
    | .case _ _ _ _ pps _ pret scrut brs, a =>
      brs.foldl (fun a (_, b) => go b a) (go scrut (go pret (pps.foldl (fun a x => go x a) a)))
    | .proj _ _ _ t, a => go t a
    | .fix defs _, a | .cofix defs _, a => defs.foldl (fun a (_, t, b, _) => go b (go t a)) a
    | _, a => a
  go t #[]

/-- The level is named in the declaration's native metadata (conservatively: not eligible). -/
def inNative (native : Lean.Json) (l : String) : Bool := (native.compress.splitOn s!"\"{l}\"").length > 1

/-- Split view of a constant definition. -/
def viewConstant (c : ConstantDecl) : Option (ConstantDecl × Array Info) := do
  let some body := c.body | none
  unless c.universes matches .monomorphic do none
  let np := min (nprods c.type) (nlams body)
  let (tb, trest) := prods c.type np
  let (bb, brest) := lams body np
  let mut infos : Array Info := #[]
  let mut ty := c.type
  let mut bd := body
  for l in globalsOfTerm c.type do
    let groups := (List.range np).toArray.filter fun i => groupBinder l tb[i]!.2 && groupBinder l bb[i]!.2
    if groups.size < 2 then continue
    let allowed := groups.foldl (fun a i => a + countLevel l tb[i]!.2 + countLevel l bb[i]!.2) 0 + finalSortCount l trest
    let total := countLevel l c.type + countLevel l body
    if inNative c.native l then continue
    unless total == allowed && countLevel l trest == finalSortCount l trest && countLevel l brest == 0 do continue
    let names := groups.map (splitName l)
    infos := infos.push { level := l, params := groups, names }
  if infos.isEmpty then none
  -- apply every split (levels are distinct, positions disjoint)
  let (tb0, trest0) := prods ty np
  let (bb0, brest0) := lams bd np
  let mut tb' := tb0
  let mut bb' := bb0
  let mut trest' := trest0
  for inf in infos do
    for i in inf.params, n in inf.names do
      tb' := tb'.set! i (tb'[i]!.1, rename inf.level #[n] tb'[i]!.2)
      bb' := bb'.set! i (bb'[i]!.1, rename inf.level #[n] bb'[i]!.2)
    trest' := renameFinal inf.level inf.names trest'
  ty := rebuildProds tb' trest'
  bd := rebuildLams bb' brest0
  some ({ c with type := ty, body := some bd }, infos)

/-- Split view of a single-body, non-template inductive. -/
def viewInductive (i : InductiveDecl) : Option (InductiveDecl × Array Info) := do
  unless i.bodies.size == 1 && i.npars ≥ 2 do none
  unless i.universes matches .monomorphic do none
  if (i.native.getObjValAs? Bool "template").toOption == some true then none
  let b := i.bodies[0]!
  let np := i.npars
  let (ab, arest) := prods b.type np
  let mut infos : Array Info := #[]
  for l in globalsOfTerm b.type ++ (b.ctors.foldl (fun a c => a ++ globalsOfTerm c.type) #[]) do
    if infos.any (·.level == l) then continue
    let groups := (List.range np).toArray.filter fun k => groupBinder l ab[k]!.2 && groupBinder l i.params[np - 1 - k]!.type
    if groups.size < 2 then continue
    -- allowed: the parameter binders in the arity, the params context and every constructor type, and
    -- the final sort of the arity / the `sort` field
    let ctorAllowed := b.ctors.foldl (fun a c =>
      let (cb, _) := prods c.type np
      a + groups.foldl (fun a k => a + countLevel l cb[k]!.2) 0) 0
    let paramAllowed := groups.foldl (fun a k => a + countLevel l i.params[np - 1 - k]!.type) 0
    let allowed := groups.foldl (fun a k => a + countLevel l ab[k]!.2) 0 + finalSortCount l arest + countSort l b.sort +
      ctorAllowed + paramAllowed
    let total := countLevel l b.type + countSort l b.sort + i.params.foldl (fun a p => a + countLevel l p.type) 0 +
      b.indices.foldl (fun a p => a + countLevel l p.type) 0 +
      b.ctors.foldl (fun a c => a + countLevel l c.type + c.args.foldl (fun a p => a + countLevel l p.type) 0 +
        c.indices.foldl (fun a t => a + countLevel l t) 0) 0 +
      b.projs.foldl (fun a (_, _, t) => a + countLevel l t) 0
    if inNative i.native l then continue
    unless total == allowed && countLevel l arest == finalSortCount l arest do continue
    -- the parameter binders of every constructor type must be the arity's (same binder types)
    unless b.ctors.all (fun c => groups.all fun k => groupBinder l (prods c.type np).1[k]!.2) do continue
    infos := infos.push { level := l, params := groups, names := groups.map (splitName l) }
  if infos.isEmpty then none
  let mut ab' := ab
  let mut arest' := arest
  let mut sort' := b.sort
  let mut params' := i.params
  let mut ctors' := b.ctors
  for inf in infos do
    for k in inf.params, n in inf.names do
      ab' := ab'.set! k (ab'[k]!.1, rename inf.level #[n] ab'[k]!.2)
      let pk := np - 1 - k
      params' := params'.set! pk { params'[pk]! with type := rename inf.level #[n] params'[pk]!.type }
    arest' := renameFinal inf.level inf.names arest'
    sort' := renameSort inf.level inf.names sort'
    ctors' := ctors'.map fun c =>
      let (cb, crest) := prods c.type np
      let cb' := (List.range np).toArray.map fun k =>
        match inf.params.idxOf? k with
        | some j => (cb[k]!.1, rename inf.level #[inf.names[j]!] cb[k]!.2)
        | none => cb[k]!
      { c with type := rebuildProds cb' crest }
  some ({ i with params := params', bodies := #[{ b with type := rebuildProds ab' arest', sort := sort', ctors := ctors' }] }, infos)

def view : Decl → Option (Decl × Array Info)
  | .constant c => (viewConstant c).map fun (c', is) => (.constant c', is)
  | .inductive i => (viewInductive i).map fun (i', is) => (.inductive i', is)

/-- The copies lie below their level (`l__s<i> ≤ l`: a copy stands for an argument `a ≤ l`, R3 at every
use) and inherit its upper bounds (`l ≤ m`, `l < m`), never its lower bounds. -/
def copiedRelations (facts : UniverseFacts) (infos : Array Info) : Array (String × String × String) :=
  infos.foldl (fun acc inf =>
    facts.relations.foldl (fun acc (a, r, b) =>
      if a == inf.level && b != inf.level && (r == "le" || r == "lt") then acc ++ inf.names.map fun n => (n, r, b) else acc)
      (acc ++ inf.names.map fun n => (n, "le", inf.level))) #[]

/-- R3G-F (docs/RESULT_SORT_LEVELS.md): the global levels of a single-body inductive that occur in its
declaration only in its result sort (the arity's final sort and the body's `sort`): nowhere in a
parameter, index, constructor, projection or the native metadata. -/
def resultOnlyLevels (i : InductiveDecl) : Array String := Id.run do
  unless i.bodies.size == 1 do return #[]
  let b := i.bodies[0]!
  let mut out := #[]
  for l in globalsOfTerm b.type do
    if inNative i.native l then continue
    let res := finalSortCount l b.type + countSort l b.sort
    let total := countLevel l b.type + countSort l b.sort + i.params.foldl (fun a p => a + countLevel l p.type) 0 +
      b.indices.foldl (fun a p => a + countLevel l p.type) 0 +
      b.ctors.foldl (fun a c => a + countLevel l c.type + c.args.foldl (fun a p => a + countLevel l p.type) 0 +
        c.indices.foldl (fun a t => a + countLevel l t) 0) 0 +
      b.projs.foldl (fun a (_, _, t) => a + countLevel l t) 0
    if res > 0 && total == res then out := out.push l
  return out

/-- R-CARRIER (docs/CARRIER_LEVELS.md, P1): the carrier levels of a block — global levels occurring as the
final sort of a parameter binder's type in its arity (an operand's carrier, e.g. `SubType`'s
`T : Type@{573}`). Each stands for the argument level of its operand at a use (R3), so its R2F reading
is minimal: it is not raised by its lower bounds (it still raises the levels above it). -/
def carrierLevels (i : InductiveDecl) : Array String := Id.run do
  let mut out := #[]
  for b in i.bodies do
    let (ps, _) := prods b.type i.npars
    for (_, ty) in ps do
      let rec fin : Term → Option SortIR
        | .prod _ _ c => fin c
        | .sort s => some s
        | _ => none
      if let some (.type u) := fin ty then
        for e in u do
          if let .global n := e.level then
            unless out.contains n do out := out.push n
  return out

/-- R-CARRIER P1 (narrowed): the pairs `(l, m)` where `l` is a parameter carrier of the block and `m` another
global level of the same block (a field sort, its result sort, …). In every R2F reading a source fact
`m ≤ l` (or `m < l`) for such a pair does not raise `l`: the operand's carrier is not tied to the block's own
other levels (SubType's base carrier 573 and its sub sort 577). Other lower bounds still apply. -/
def decoupledPairs (i : InductiveDecl) : Array (String × String) := Id.run do
  let cs := carrierLevels i
  if cs.isEmpty then return #[]
  let all := i.bodies.foldl (fun acc b => b.ctors.foldl (fun acc c => acc ++ globalsOfTerm c.type) (acc ++ globalsOfTerm b.type)) #[]
  let mut out := #[]
  for l in cs do
    for m in all do
      if m != l && !out.contains (l, m) then out := out.push (l, m)
  return out

end Rocq2Lean.Split
