import Rocq2LeanOut
-- the extracted obligation of the opaque data `bounded` (2 ≤ 5, Rocq's `le`): a synthetic test proof
theorem RocqProofTemplates.T@TASK@.proof : Rocq.SF.Opq.bounded__rocq2lean_obligation_1.statement :=
  Rocq.Corelib.Init.Peano.le.le_S 2 4 (Rocq.Corelib.Init.Peano.le.le_S 2 3
    (Rocq.Corelib.Init.Peano.le.le_S 2 2 (Rocq.Corelib.Init.Peano.le.le_n 2)))
