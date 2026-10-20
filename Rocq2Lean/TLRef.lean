import Std.Data.HashMap

/-!
# Per-thread mutable cells

The translator keeps tier switches and per-declaration logs in global cells (`initialize … ← …`). The parallel task
farm (`R2L_JOBS`, `docs/PARALLEL.md`) translates several declarations at once, each on its own dedicated thread, so
each cell holds one value per thread (`IO.getTID`), behind the `get` / `set` / `modify` interface of `IO.Ref`. A
sequential run has one thread and behaves exactly as with a plain reference.
-/

/-- A mutable cell with one value per thread (initially `init` on every thread). -/
structure TLRef (α : Type) where
  init : α
  cells : IO.Ref (Std.HashMap UInt64 α)

instance {α : Type} [Inhabited α] : Nonempty (TLRef α) := ⟨⟨default, Classical.ofNonempty⟩⟩

namespace TLRef

def new {α : Type} (init : α) : BaseIO (TLRef α) := do
  return { init, cells := ← IO.mkRef {} }

@[inline] def get {α : Type} (r : TLRef α) : BaseIO α := do
  let t ← IO.getTID
  return ((← r.cells.get).get? t).getD r.init

@[inline] def set {α : Type} (r : TLRef α) (v : α) : BaseIO Unit := do
  let t ← IO.getTID
  r.cells.modify (·.insert t v)

@[inline] def modify {α : Type} (r : TLRef α) (f : α → α) : BaseIO Unit := do
  let t ← IO.getTID
  r.cells.modify fun m => m.insert t (f ((m.get? t).getD r.init))

/-- The values of every thread (the farm collects per-worker logs at the end). -/
def all {α : Type} (r : TLRef α) : BaseIO (Array α) := do
  return (← r.cells.get).toArray.map (·.2)

end TLRef
