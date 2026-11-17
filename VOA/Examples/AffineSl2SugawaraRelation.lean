/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2Virasoro

/-!
# The Sugawara relation for `V^k(𝔰𝔩₂)` in the `e, f, h` basis

With `e, f, h` the currents `J 0, J 1, J 2`, the Sugawara vector
`ω = (2(k+2))⁻¹ (e₋₁f₋₁ + f₋₁e₋₁ + ½ h₋₁h₋₁)|0⟩` (`omegaA_creation_form`) becomes, after
`f₋₁e₋₁|0⟩ = e₋₁f₋₁|0⟩ − h₋₂|0⟩` (the commutator `[e₋₁, f₋₁] = h₋₂`, no central term since
`-1 + -1 ≠ 0`),

  `2(k+2) · ω = 2 e₋₁f₋₁|0⟩ − h₋₂|0⟩ + ½ h₋₁h₋₁|0⟩`.

At the admissible level `k = -4/3` this is `2e₋₁f₋₁ − h₋₂ + ½h₋₁² = (4/3) L₋₂` on the vacuum,
the rewriting used for the weight-3 singular vector in the Adamović symbol-descent chapter.
-/

open VOA VOA.AffineVOA VOA.AffineVOA.SugawaraCov
open scoped BigOperators

namespace VOA.AffineVOA.Vir

/-- **The Sugawara relation** for `V^k(𝔰𝔩₂)`, at every non-critical level `k ≠ -2`.  (At `k = -2`
the left side is `0` while the right side is the Segal–Sugawara vector, which is not `0`.) -/
theorem sugawara_relation (k : ℂ) (hk : k + dualCoxeter ≠ 0) :
    (2 * (k + dualCoxeter)) • omegaA k
      = (2 : ℂ) • J k 0 (-1) (J k 1 (-1) (vacuumA k)) - J k 2 (-2) (vacuumA k)
        + (1 / 2 : ℂ) • J k 2 (-1) (J k 2 (-1) (vacuumA k)) := by
  have hfe : J k 1 (-1) (J k 0 (-1) (vacuumA k))
      = J k 0 (-1) (J k 1 (-1) (vacuumA k)) - J k 2 (-2) (vacuumA k) := by
    have h := congrArg (fun T => T (vacuumA k)) (J_bracket k 0 1 (-1) (-1))
    simp only [Fin.sum_univ_three, fabc, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.add_apply, LinearMap.smul_apply, zero_smul, one_smul, zero_add, add_zero] at h
    norm_num at h
    rw [← h]; abel
  rw [omegaA_creation_form, c0, smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero hk), one_smul]
  simp only [Fin.sum_univ_three, kappaInv, zero_smul, add_zero, zero_add, one_smul]
  rw [hfe]
  module

/-- **At `k = -4/3`**: `2 e₋₁f₋₁|0⟩ − h₋₂|0⟩ + ½ h₋₁h₋₁|0⟩ = (4/3) ω`, i.e. `(4/3) L₋₂|0⟩`. -/
theorem sugawara_relation_neg_four_thirds :
    (2 : ℂ) • J (-4/3) 0 (-1) (J (-4/3) 1 (-1) (vacuumA (-4/3))) - J (-4/3) 2 (-2) (vacuumA (-4/3))
        + (1 / 2 : ℂ) • J (-4/3) 2 (-1) (J (-4/3) 2 (-1) (vacuumA (-4/3)))
      = (4 / 3 : ℂ) • omegaA (-4/3) := by
  rw [← sugawara_relation _ (by norm_num [dualCoxeter])]
  norm_num [dualCoxeter]

end VOA.AffineVOA.Vir
