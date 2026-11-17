/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8VacuumSteps

/-!
# `E₈` propagation steps `3751..3874` (kernel checks)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem stepOK_30 : ∀ s, s < 3875 → 3751 ≤ s → stepOK s = true := by
  -- Offset form keeps the kernel's `Nat.decidableBallLT` recursion depth at 124.
  have h : ∀ k, k < 124 → stepOK (3751 + k) = true := by decide +kernel
  intro s hs ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  exact h k (by omega)

end VOA.DeligneAudit.DeligneCarrier.E8
