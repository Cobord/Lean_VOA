/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8VacuumSteps

/-!
# `E₈` propagation steps `2626..2750` (kernel checks)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem stepOK_21 : ∀ s, s < 2751 → 2626 ≤ s → stepOK s = true := by
  -- Offset form keeps the kernel's `Nat.decidableBallLT` recursion depth at 125.
  have h : ∀ k, k < 125 → stepOK (2626 + k) = true := by decide +kernel
  intro s hs ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  exact h k (by omega)

end VOA.DeligneAudit.DeligneCarrier.E8
